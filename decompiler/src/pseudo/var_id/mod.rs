//! Variable identity system using interned IDs.
//!
//! Each variable gets a unique numeric ID at creation time, eliminating
//! name-based shadowing issues.

use std::cell::Cell;
use std::collections::HashMap;

// Both allocators use thread-local counters, not process-wide
// atomics, so concurrent `decompile_program` work on another thread
// cannot perturb this thread's allocation order; within a thread each
// counter advances deterministically.
//
// AST constructors (`compat_var`, `helper_symbol`, `compat_let_bind`)
// emit `id: None`. `fresh_compat_placeholder` remains for the fallback
// sites that convert `Option<VarId>` → `VarId` via
// `unwrap_or_else(fresh_compat_placeholder)` where a downstream API
// needs a concrete VarId; `OptionVarIdGet::get`, `VarId::get` and
// `is_compat_placeholder` filter those compat-range ids back out.
thread_local! {
    static NEXT_SYNTHETIC_BINDING_ID_TLS: Cell<u32> = const { Cell::new(1_000_000_000) };
    static NEXT_COMPAT_PLACEHOLDER_ID_TLS: Cell<u32> = const { Cell::new(2_000_000_000) };
}
const AUTHORITATIVE_BINDING_START: u32 = 1_000_000_000;
const COMPAT_PLACEHOLDER_START: u32 = 2_000_000_000;
const SYNTHETIC_UPPER_EXCLUSIVE: u32 = u32::MAX;
/// Exclusive upper bound for `VarInterner` sequential IDs; it must not
/// exceed `AUTHORITATIVE_BINDING_START`, or interner IDs would collide
/// with the `fresh_binding` / `fresh_compat_placeholder` ranges.
const INTERNER_UPPER_EXCLUSIVE: u32 = AUTHORITATIVE_BINDING_START;

fn interner_next_id(id_to_name_len: usize) -> VarId {
    if id_to_name_len >= INTERNER_UPPER_EXCLUSIVE as usize {
        panic!(
            "VarInterner exhausted: id count {id_to_name_len} reached exclusive upper bound {INTERNER_UPPER_EXCLUSIVE}; \
             raising this bound requires rethinking VarId allocator ranges in pseudo/var_id.rs"
        );
    }
    VarId(id_to_name_len as u32)
}

fn allocate_from_cell(
    c: &Cell<u32>,
    lower_inclusive: u32,
    upper_exclusive: u32,
    allocator_name: &'static str,
) -> VarId {
    let current = c.get();
    if current < lower_inclusive || current >= upper_exclusive {
        panic!(
            "VarId allocator `{allocator_name}` exhausted or corrupted at raw id {current}; valid range is [{lower_inclusive}, {upper_exclusive})"
        );
    }
    let next = current
        .checked_add(1)
        .unwrap_or_else(|| panic!("VarId allocator `{allocator_name}` overflow"));
    c.set(next);
    VarId::from_raw(current)
}

fn allocate_tls_var_id(
    counter: &'static std::thread::LocalKey<Cell<u32>>,
    lower_inclusive: u32,
    upper_exclusive: u32,
    allocator_name: &'static str,
) -> VarId {
    counter.with(|c| allocate_from_cell(c, lower_inclusive, upper_exclusive, allocator_name))
}

/// Unique identifier for a variable.
///
/// Two variables with the same name in different scopes get different VarIds.
/// This eliminates the need for post-hoc uniquification passes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct VarId(u32);

impl VarId {
    /// Create a VarId from a raw u32 (for internal use and testing).
    pub(crate) fn from_raw(raw: u32) -> Self {
        Self(raw)
    }

    #[cfg(test)]
    pub(crate) fn new(raw: u32) -> Self {
        Self::from_raw(raw)
    }

    /// Allocate a VarId from the compat-placeholder range (>=`COMPAT_PLACEHOLDER_START`).
    /// For callers that synthesize AST nodes without an authoritative `VarId`.
    /// Uses a thread-local counter, for the same cross-thread isolation reason
    /// as `fresh_binding`.
    pub(crate) fn fresh_compat_placeholder() -> Self {
        allocate_tls_var_id(
            &NEXT_COMPAT_PLACEHOLDER_ID_TLS,
            COMPAT_PLACEHOLDER_START,
            SYNTHETIC_UPPER_EXCLUSIVE,
            "fresh_compat_placeholder",
        )
    }

    /// Allocate a fresh authoritative binder VarId.
    ///
    /// Uses a thread-local counter, not a process-wide atomic, so decompile
    /// work on another thread cannot reshuffle this thread's allocation order.
    pub(crate) fn fresh_binding() -> Self {
        allocate_tls_var_id(
            &NEXT_SYNTHETIC_BINDING_ID_TLS,
            AUTHORITATIVE_BINDING_START,
            COMPAT_PLACEHOLDER_START,
            "fresh_binding",
        )
    }

    /// Raise this thread's `fresh_binding` counter so the next mint is
    /// `> max_existing_id`. Never lowers it.
    ///
    /// An AST can carry fresh-range ids minted under a different counter
    /// (another thread, or earlier work this thread never saw), so a local
    /// `fresh_binding()` could re-mint an id already in the tree. Call it
    /// with the tree's maximum id before minting into it.
    pub(crate) fn ensure_binding_counter_above(max_existing_id: u32) {
        if max_existing_id >= COMPAT_PLACEHOLDER_START {
            // Compat-placeholder ids are not `fresh_binding`'s namespace.
            return;
        }
        // May set the counter to COMPAT_PLACEHOLDER_START when max ==
        // COMPAT_PLACEHOLDER_START - 1; the next mint then hits the
        // allocator's range panic instead of silently re-colliding.
        let min_next = max_existing_id
            .saturating_add(1)
            .max(AUTHORITATIVE_BINDING_START);
        NEXT_SYNTHETIC_BINDING_ID_TLS.with(|c| {
            if c.get() < min_next {
                c.set(min_next);
            }
        });
    }

    pub(crate) fn is_compat_placeholder(self) -> bool {
        self.0 >= COMPAT_PLACEHOLDER_START
    }

    /// `None` for a compat-placeholder id, `Some(self)` otherwise, so
    /// callers can treat placeholders as absent.
    pub(crate) fn get(&self) -> Option<VarId> {
        if self.is_compat_placeholder() {
            None
        } else {
            Some(*self)
        }
    }

    pub(crate) fn as_u32(self) -> u32 {
        self.0
    }
}

impl std::fmt::Display for VarId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "v{}", self.0)
    }
}

/// Mirrors `VarId::get()` on `Option<VarId>`: both a `None` id and a
/// compat-placeholder id report as `None`, so placeholder-filtering
/// callsites behave the same for optional and concrete ids.
pub(crate) trait OptionVarIdGet {
    fn get(&self) -> Option<VarId>;
}

impl OptionVarIdGet for Option<VarId> {
    #[inline]
    fn get(&self) -> Option<VarId> {
        match self {
            None => None,
            Some(vid) if vid.is_compat_placeholder() => None,
            Some(vid) => Some(*vid),
        }
    }
}

/// Bidirectional String <-> VarId mapping.
///
/// `intern()` is get-or-create; `intern_fresh()` always allocates a
/// new id, even for a duplicate name.
pub(crate) struct VarInterner {
    /// Forward mapping: name → first VarId with that name.
    /// Used by `intern()` for deduplication.
    name_to_first_id: HashMap<String, VarId>,
    /// Reverse mapping: VarId → display name (indexed by VarId.0).
    id_to_name: Vec<String>,
}

impl VarInterner {
    pub(crate) fn new() -> Self {
        Self {
            name_to_first_id: HashMap::new(),
            id_to_name: Vec::new(),
        }
    }

    /// Get or create a VarId for the given name.
    ///
    /// Use this where identity must be shared across occurrences (e.g.
    /// builtin names).
    pub(crate) fn intern(&mut self, name: &str) -> VarId {
        if let Some(&id) = self.name_to_first_id.get(name) {
            return id;
        }
        let id = interner_next_id(self.id_to_name.len());
        self.id_to_name.push(name.to_string());
        self.name_to_first_id.insert(name.to_string(), id);
        id
    }

    /// Create a fresh VarId with the given display name, even if that name
    /// is already interned. Use this for bindings where each occurrence
    /// must be unique — two different `tail` variables in sibling scopes.
    pub(crate) fn intern_fresh(&mut self, name: &str) -> VarId {
        let id = interner_next_id(self.id_to_name.len());
        // The id suffix keeps display names unique across UPLC variables at
        // different De Bruijn depths that share a name hint ("i", "v"); the
        // rename pass replaces them for readable output.
        let unique_name = format!("{}_{}", name, id.0);
        self.id_to_name.push(unique_name);
        id
    }

    pub(crate) fn resolve(&self, id: VarId) -> &str {
        &self.id_to_name[id.0 as usize]
    }

    /// Change an existing VarId's display name; its identity is unchanged.
    ///
    /// Reverse-lookup ownership follows: if this id owned the old name, the
    /// next id still carrying that display name takes over, otherwise the
    /// entry is dropped. The new name is registered only if unowned,
    /// preserving first-interned semantics.
    pub(crate) fn rename(&mut self, id: VarId, new_name: &str) {
        // Early return for same-name rename — don't disturb reverse lookups
        if self.id_to_name[id.0 as usize] == new_name {
            return;
        }
        let old_name = std::mem::replace(&mut self.id_to_name[id.0 as usize], new_name.to_string());
        if self.name_to_first_id.get(old_name.as_str()) == Some(&id) {
            // Promote the next id with the same old display name, if any.
            let promoted = self
                .id_to_name
                .iter()
                .enumerate()
                .find(|(i, n)| *i != id.0 as usize && n.as_str() == old_name.as_str())
                .map(|(i, _)| VarId(i as u32));
            match promoted {
                Some(new_owner) => {
                    self.name_to_first_id.insert(old_name.clone(), new_owner);
                }
                None => {
                    self.name_to_first_id.remove(old_name.as_str());
                }
            }
        }
        // Register new name only if no existing id owns that name
        self.name_to_first_id
            .entry(new_name.to_string())
            .or_insert(id);
    }

    pub(crate) fn len(&self) -> usize {
        self.id_to_name.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.id_to_name.is_empty()
    }
}

impl Default for VarInterner {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests;
