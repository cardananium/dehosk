//! Identifiers and provenance tracking for MidExpr nodes.

use serde::{Deserialize, Serialize};

use super::expr::MidExpr;

/// Unique identifier for a MidExpr node, assigned during UPLC → MidExpr translation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct MidExprId(u32);

impl MidExprId {
    pub(crate) fn new(raw: u32) -> Self {
        Self(raw)
    }

    pub(crate) fn as_u32(self) -> u32 {
        self.0
    }
}

impl std::fmt::Display for MidExprId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "mid_{}", self.0)
    }
}

/// Source location in decompiled output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SourceSpan {
    pub start_line: u32,
    pub start_col: u32,
    pub end_line: u32,
    pub end_col: u32,
}

/// One entry in a node's provenance, in the order it was recorded.
///
/// `Node` is a reference to another node's parts, not a copy of its ids.
/// Copying would be quadratic: absorbing a chain recopies the whole list at
/// every step, and chain length is script-controlled.
#[derive(Debug, Clone, Copy)]
enum Part {
    /// A UPLC id from [`ProvenanceBuilder::link`]. On the node that recorded
    /// it, kept even if the id appears again later.
    Linked(isize),
    /// A UPLC id from [`ProvenanceBuilder::absorb_uplc`]. Dropped at
    /// materialization if already present.
    Absorbed(isize),
    /// The parts of another node.
    Node(MidExprId),
}

/// Tracks provenance links between all representation levels.
pub(crate) struct ProvenanceBuilder {
    /// MidExprId → what contributed to this node, in order.
    parts: std::collections::HashMap<MidExprId, Vec<Part>>,
    /// UPLC uniq_id → the MidExprId that recorded it. May name a node that
    /// has since been absorbed; [`Self::mid_for_uplc`] resolves that.
    uplc_to_mid: std::collections::HashMap<isize, MidExprId>,
    /// source → the node that absorbed it. [`Self::mid_for_uplc`] follows
    /// these hops instead of rewriting every UPLC id the source owned.
    absorbed_into: std::collections::HashMap<MidExprId, MidExprId>,
    /// Counter for allocating MidExprIds.
    next_id: u32,
    /// Bumped on every mutation, so a cached materialization can tell whether
    /// it is still current.
    generation: u64,
    /// Memo for [`Self::uplc_ids`], valid only for its recorded generation.
    materialized: std::cell::RefCell<std::collections::HashMap<MidExprId, (u64, Vec<isize>)>>,
}

impl ProvenanceBuilder {
    pub(crate) fn new() -> Self {
        Self {
            parts: std::collections::HashMap::new(),
            uplc_to_mid: std::collections::HashMap::new(),
            absorbed_into: std::collections::HashMap::new(),
            next_id: 0,
            generation: 0,
            materialized: std::cell::RefCell::new(std::collections::HashMap::new()),
        }
    }

    pub(crate) fn fresh_id(&mut self) -> MidExprId {
        let id = MidExprId(self.next_id);
        self.next_id += 1;
        id
    }

    /// Record that `mid_id` was produced from `uplc_uniq_id` and owns
    /// it in the canonical `uplc -> mid` lookup.
    pub(crate) fn link(&mut self, mid_id: MidExprId, uplc_uniq_id: isize) {
        self.generation += 1;
        self.parts
            .entry(mid_id)
            .or_default()
            .push(Part::Linked(uplc_uniq_id));
        self.uplc_to_mid.insert(uplc_uniq_id, mid_id);
    }

    /// Record provenance for a synthesized node without changing the canonical
    /// uplc -> mid lookup used for original translation nodes.
    ///
    /// A snapshot by design: the derived node inherits the ids its source had
    /// at this moment, and later changes to the source do not reach it.
    pub(crate) fn link_derived(&mut self, mid_id: MidExprId, uplc_uniq_ids: &[isize]) {
        self.generation += 1;
        let mut seen = std::collections::HashSet::new();
        let mut parts = Vec::new();
        for &uplc_uniq_id in uplc_uniq_ids {
            if seen.insert(uplc_uniq_id) {
                parts.push(Part::Linked(uplc_uniq_id));
            }
        }
        self.parts.insert(mid_id, parts);
    }

    /// Attach an additional original UPLC node to an already-retained MidExpr.
    ///
    /// Translation collapses several UPLC nodes into one owner — flattened
    /// lambda chains, apply spines — so the canonical `uplc -> mid` lookup
    /// must point at the surviving MidExpr, not a dead intermediate id.
    pub(crate) fn absorb_uplc(&mut self, mid_id: MidExprId, uplc_uniq_id: isize) {
        self.generation += 1;
        self.parts
            .entry(mid_id)
            .or_default()
            .push(Part::Absorbed(uplc_uniq_id));
        self.uplc_to_mid.insert(uplc_uniq_id, mid_id);
    }

    /// Attach all original UPLC nodes currently owned by `source_mid` to the
    /// surviving retained owner `mid_id`.
    ///
    /// O(1): the source is referenced, not copied.
    pub(crate) fn absorb_mid(&mut self, mid_id: MidExprId, source_mid: MidExprId) {
        if mid_id == source_mid {
            return;
        }
        self.generation += 1;
        self.parts
            .entry(mid_id)
            .or_default()
            .push(Part::Node(source_mid));
        self.absorbed_into.entry(source_mid).or_insert(mid_id);
    }

    /// Allocate a fresh MidExprId that inherits provenance from `source_mid`.
    pub(crate) fn fresh_derived_from(&mut self, source_mid: MidExprId) -> MidExprId {
        let mid_id = self.fresh_id();
        let uplc_ids = self.uplc_ids(source_mid);
        self.link_derived(mid_id, &uplc_ids);
        mid_id
    }

    /// Allocate a fresh MidExprId that inherits provenance from several
    /// contributing MidExpr nodes.
    pub(crate) fn fresh_derived_from_many(&mut self, source_mids: &[MidExprId]) -> MidExprId {
        let mut uplc_ids: Vec<isize> = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for source_mid in source_mids {
            for uplc_id in self.uplc_ids(*source_mid) {
                if seen.insert(uplc_id) {
                    uplc_ids.push(uplc_id);
                }
            }
        }
        let mid_id = self.fresh_id();
        self.link_derived(mid_id, &uplc_ids);
        mid_id
    }

    /// The UPLC ids this node owns, in the order they were recorded.
    ///
    /// Materialized from the parts on demand. The reference graph is as deep
    /// as the eliminations that built it, so the walk is a heap stack. An id
    /// recorded by `link` on this node is kept even if it also appears later;
    /// everything reached through absorption is dropped if already present.
    pub(crate) fn uplc_ids(&self, mid_id: MidExprId) -> Vec<isize> {
        if let Some((generation, ids)) = self.materialized.borrow().get(&mid_id)
            && *generation == self.generation
        {
            return ids.clone();
        }

        let mut out: Vec<isize> = Vec::new();
        let mut seen = std::collections::HashSet::new();
        let mut visited = std::collections::HashSet::new();
        // (node, index of the next part to look at, is this the node asked for)
        let mut stack: Vec<(MidExprId, usize, bool)> = vec![(mid_id, 0, true)];
        visited.insert(mid_id);

        while let Some((node, index, is_root)) = stack.pop() {
            let Some(parts) = self.parts.get(&node) else {
                continue;
            };
            let Some(part) = parts.get(index) else {
                continue;
            };
            stack.push((node, index + 1, is_root));
            match *part {
                Part::Linked(id) => {
                    // A `link` on this node is kept even if the id appears
                    // again later; through an absorption it is dropped if
                    // already present.
                    if is_root {
                        seen.insert(id);
                        out.push(id);
                    } else if seen.insert(id) {
                        out.push(id);
                    }
                }
                Part::Absorbed(id) => {
                    if seen.insert(id) {
                        out.push(id);
                    }
                }
                Part::Node(source) => {
                    // A guard, not an expectation: absorption should not build
                    // a cycle, but materialization must terminate regardless.
                    if visited.insert(source) {
                        stack.push((source, 0, false));
                    }
                }
            }
        }

        self.materialized
            .borrow_mut()
            .insert(mid_id, (self.generation, out.clone()));
        out
    }

    pub(crate) fn mid_for_uplc(&self, uplc_id: isize) -> Option<MidExprId> {
        let mut mid = *self.uplc_to_mid.get(&uplc_id)?;
        // Follow absorptions to the surviving owner. Bounded by the number of
        // nodes, so a cycle cannot spin forever.
        for _ in 0..=self.next_id {
            match self.absorbed_into.get(&mid) {
                Some(&next) if next != mid => mid = next,
                _ => break,
            }
        }
        Some(mid)
    }

    pub(crate) fn node_count(&self) -> u32 {
        self.next_id
    }
}

/// Reassign fresh unique MidExprIds to the entire tree, preserving provenance
/// by deriving each new id from the previous node id.
pub(crate) fn refresh_mid_ids(expr: &mut MidExpr, provenance: &mut ProvenanceBuilder) {
    let taken = std::mem::replace(expr, MidExpr::Error { id: expr.id() });
    *expr = crate::pseudo::mid::rewrite::rewrite_bottom_up(taken, &mut |mut node| {
        let refreshed = provenance.fresh_derived_from(node.id());
        node.set_id(refreshed);
        node
    });
}

impl Default for ProvenanceBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests;
