//! Variable renaming pass.
//!
//! Renames every binder to a name unique across the expression, from
//! a value- or position-derived hint where there is one.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

/// Renamer for making variable names unique and meaningful.
pub(crate) struct Renamer {
    /// Counter for generating unique names
    counter: usize,
    /// Mapping from old names to new names in current scope
    scope: HashMap<String, String>,
    /// Stack of scopes for nested bindings
    scope_stack: Vec<HashMap<String, String>>,
    /// VarId-based scope (authoritative, prevents naming collisions)
    scope_by_id: HashMap<VarId, String>,
    /// Stack of id scopes for nested bindings
    scope_by_id_stack: Vec<HashMap<VarId, String>>,
    /// Track all names in use to prevent collisions
    names_in_use: std::collections::HashSet<String>,
    /// With `tag_synthetic` on, every Let binder whose name or
    /// value-derived hint looks like a Simplifier-generated helper
    /// (`f`, `fn`, `rec_fn`, `<name>_result`, …). Drained via
    /// [`Self::take_synthetic_binder_ids`] into the global
    /// `kind_annotations` map, so the recovery passes' typed
    /// predicate has an authoritative kind for these binders.
    synthetic_binder_ids: Vec<VarId>,
    /// Enables synthetic-binder tagging. Off by default: plain
    /// `rename_variables(expr)` records nothing.
    tag_synthetic: bool,
}

impl Renamer {
    pub(crate) fn new() -> Self {
        Self {
            counter: 0,
            scope: HashMap::new(),
            scope_stack: Vec::new(),
            scope_by_id: HashMap::new(),
            scope_by_id_stack: Vec::new(),
            names_in_use: std::collections::HashSet::new(),
            synthetic_binder_ids: Vec::new(),
            tag_synthetic: false,
        }
    }

    /// Switches on synthetic-binder tagging. After `fold(expr)`,
    /// drain the ids with [`Self::take_synthetic_binder_ids`] and
    /// merge them into `kind_annotations`.
    pub(crate) fn enable_synthetic_tagging(mut self) -> Self {
        self.tag_synthetic = true;
        self
    }

    pub(crate) fn take_synthetic_binder_ids(&mut self) -> Vec<VarId> {
        std::mem::take(&mut self.synthetic_binder_ids)
    }

    /// True iff `name`, with any `_<digits>` disambiguation suffix
    /// stripped, is a Simplifier-generated helper-let name — the
    /// binders to annotate as Synthetic.
    ///
    /// The stem is checked, not just the value-derived hint,
    /// because a binder can already carry the disambiguated form
    /// (`lookup_result_2`), whose hint is None at rename time.
    fn looks_like_helper_binding(name: &str) -> bool {
        let stem = Self::strip_disambiguation_suffix(name);
        stem == "f"
            || stem == "fn"
            || stem == "rec_fn"
            || stem == "self_fn"
            || stem == "helper"
            || stem.starts_with("fn_")
            || stem.starts_with("helper_")
            || stem.ends_with("_result")
            || stem.ends_with("_partial")
    }

    /// Strip a trailing `_<digits>` suffix from `name`; anything
    /// else after the last `_` leaves the name unchanged.
    fn strip_disambiguation_suffix(name: &str) -> &str {
        if let Some(idx) = name.rfind('_') {
            let suffix = &name[idx + 1..];
            if !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()) {
                return &name[..idx];
            }
        }
        name
    }

    /// Generate a new unique variable name, guaranteed not to collide.
    fn fresh_name(&mut self, hint: Option<&str>) -> String {
        let name = if let Some(h) = hint {
            // With a hint, try the bare hint first, then hint_2, hint_3, ...
            if !self.names_in_use.contains(h) {
                h.to_string()
            } else {
                let mut suffix = 2;
                loop {
                    let candidate = format!("{}_{}", h, suffix);
                    if !self.names_in_use.contains(&candidate) {
                        break candidate;
                    }
                    suffix += 1;
                }
            }
        } else {
            // Without a hint, use sequential letters: a, b, ..., z, a1, b1, ...
            loop {
                let idx = self.counter;
                self.counter += 1;
                let candidate = if idx < 26 {
                    ((b'a' + idx as u8) as char).to_string()
                } else {
                    format!("{}{}", ((b'a' + (idx % 26) as u8) as char), idx / 26)
                };
                if !self.names_in_use.contains(&candidate) {
                    break candidate;
                }
            }
        };
        self.names_in_use.insert(name.clone());
        name
    }

    /// Push a new scope.
    fn push_scope(&mut self) {
        self.scope_stack.push(self.scope.clone());
        self.scope_by_id_stack.push(self.scope_by_id.clone());
    }

    /// Pop a scope.
    fn pop_scope(&mut self) {
        if let Some(prev) = self.scope_stack.pop() {
            self.scope = prev;
        }
        if let Some(prev) = self.scope_by_id_stack.pop() {
            self.scope_by_id = prev;
        }
    }

    /// Bind a variable with VarId for collision-free tracking.
    fn bind_with_id(
        &mut self,
        old_name: &str,
        var_id: Option<VarId>,
        hint: Option<&str>,
    ) -> String {
        let new_name = self.fresh_name(hint);
        self.scope.insert(old_name.to_string(), new_name.clone());
        if let Some(vid) = var_id {
            self.scope_by_id.insert(vid, new_name.clone());
        }
        new_name
    }

    fn bind_binder(&mut self, binder: &Binder, hint: Option<&str>) -> Binder {
        binder.renamed(self.bind_with_id(binder.as_str(), Some(binder.id), hint))
    }

    /// Look up by VarId first, then by name.
    fn lookup_with_id(&self, name: &str, var_id: Option<VarId>) -> String {
        if let Some(vid) = var_id
            && let Some(renamed) = self.scope_by_id.get(&vid)
        {
            return renamed.clone();
        }
        self.lookup(name)
    }

    /// Look up a variable name.
    fn lookup(&self, name: &str) -> String {
        self.scope
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_string())
    }

    fn rename_pattern_binders(
        &mut self,
        pattern: crate::pseudo::ast::WhenPattern,
    ) -> crate::pseudo::ast::WhenPattern {
        use crate::pseudo::ast::WhenPattern;

        match pattern {
            WhenPattern::Constructor {
                type_hint,
                tag,
                fields,
                shape,
            } => WhenPattern::Constructor {
                type_hint,
                tag,
                fields: fields
                    .into_iter()
                    .map(|field| self.bind_binder(&field, Some(field.as_str())))
                    .collect(),
                shape,
            },
            WhenPattern::List { elements, tail } => WhenPattern::List {
                elements: elements
                    .into_iter()
                    .map(|element| self.bind_binder(&element, Some(element.as_str())))
                    .collect(),
                tail: tail.map(|tail| self.bind_binder(&tail, Some(tail.as_str()))),
            },
            WhenPattern::Tuple(fields) => WhenPattern::Tuple(
                fields
                    .into_iter()
                    .map(|field| self.bind_binder(&field, Some(field.as_str())))
                    .collect(),
            ),
            WhenPattern::Pair(a, b) => WhenPattern::Pair(
                self.bind_binder(&a, Some(a.as_str())),
                self.bind_binder(&b, Some(b.as_str())),
            ),
            WhenPattern::Var(name) => {
                WhenPattern::Var(self.bind_binder(&name, Some(name.as_str())))
            }
            WhenPattern::Wildcard => WhenPattern::Wildcard,
            WhenPattern::Literal(expr) => WhenPattern::Literal(self.fold(expr)),
        }
    }

    fn fold_when_scoped(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        let subject = self.fold(subject);
        self.push_scope();
        let subject_name = subject_name.map(|name| self.bind_binder(&name, Some(name.as_str())));
        let clauses = clauses
            .into_iter()
            .map(|clause| {
                self.push_scope();
                let pattern = self.rename_pattern_binders(clause.pattern);
                let guard = clause.guard.map(|guard| self.fold(guard));
                let body = self.fold(clause.body);
                self.pop_scope();
                WhenClause {
                    pattern,
                    guard,
                    body,
                }
            })
            .collect();
        self.pop_scope();
        PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name,
            clauses,
        }
    }

    /// Get a hint for the variable name based on the value.
    fn hint_from_value(&self, value: &PseudoExpr) -> Option<String> {
        match value {
            // Builtin functions get descriptive names
            PseudoExpr::Force(inner) => {
                if let PseudoExpr::Force(inner2) = inner.as_ref()
                    && let PseudoExpr::BuiltinCall { name, .. } = inner2.as_ref()
                {
                    return Some(Self::builtin_hint(name));
                }
                if let PseudoExpr::BuiltinCall { name, .. } = inner.as_ref() {
                    return Some(Self::builtin_hint(name));
                }
                None
            }
            PseudoExpr::BuiltinCall { name, args } => {
                if args.is_empty() {
                    Some(Self::builtin_hint(name))
                } else if name.starts_with("Hash.") {
                    // Hash builtins (`Hash.blake2b_256` etc.) are 1-arg, so a
                    // call WITH an arg is COMPLETE, not partial — name it by its
                    // descriptive stem (`blake2b`), not `<…>_partial`.
                    Some(Self::builtin_hint(name))
                } else {
                    // A builtin applied to some-but-maybe-not-all args; the
                    // conservative `_partial` hint, dot-free via
                    // `short_builtin_name`.
                    Some(format!("{}_partial", Self::short_builtin_name(name)))
                }
            }
            PseudoExpr::Lambda { params, .. } => {
                // `"fn"` is an keyword: `sanitize_identifier`
                // appends `_`, so a `"fn"` hint renders as `fn fn_`, a
                // helper with nothing after its name. The hints below
                // are chosen to survive sanitisation.
                if params.len() == 1 {
                    Some("f".to_string())
                } else {
                    Some("helper".to_string())
                }
            }
            PseudoExpr::RecFn { .. } => Some("rec_fn".to_string()),
            PseudoExpr::FieldAccess { selector, .. } => Some(selector.as_pretty_name().to_string()),
            PseudoExpr::IndexAccess { index, .. } => Some(format!("item_{}", index)),
            PseudoExpr::List { .. } => Some("list".to_string()),
            PseudoExpr::Apply { function, .. } => {
                if let PseudoExpr::Var { name, .. } = function.as_ref() {
                    // Helper hoisting rearranges scopes around bare
                    // `rec_fn_N` / `self_fn_N` placeholders, so a
                    // `{rec_fn_N}_result` alias in an inner scope can
                    // dangle. Only the semantically renamed `fn_*` /
                    // `helper_*` forms take a `_result` hint.
                    if name.starts_with("fn_") || name.starts_with("helper_") {
                        Some(format!("{}_result", name))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            PseudoExpr::ByteArray(_) => Some("bytes".to_string()),
            PseudoExpr::Int(_) => Some("n".to_string()),
            PseudoExpr::Bool(true) => Some("true_val".to_string()),
            PseudoExpr::Bool(false) => Some("false_val".to_string()),
            PseudoExpr::Unit => Some("unit".to_string()),
            _ => None,
        }
    }

    /// Get a short hint for a builtin name.
    fn builtin_hint(name: &str) -> String {
        Self::short_builtin_name(name)
    }

    /// Shorten builtin name for use as variable hint.
    fn short_builtin_name(name: &str) -> String {
        let stem = match name {
            "if_then_else" => "if_fn".to_string(),
            "choose_list" => "choose".to_string(),
            "choose_unit" => "seq".to_string(),
            "head_list" => "head".to_string(),
            "tail_list" => "tail".to_string(),
            "null_list" => "is_empty".to_string(),
            "cons_list" => "cons".to_string(),
            "fst_pair" => "fst".to_string(),
            "snd_pair" => "snd".to_string(),
            "Data.Int" => "to_data".to_string(),
            "Data.ByteArray" => "to_data".to_string(),
            "Data.List" => "to_data".to_string(),
            "Data.Map" => "to_data".to_string(),
            "Data.un_constr" => "unpack".to_string(),
            "Data.un_int" => "to_int".to_string(),
            "Data.un_bytearray" => "to_bytes".to_string(),
            "Data.un_list" => "to_list".to_string(),
            "Data.un_map" => "to_map".to_string(),
            "un_constr_data" => "unpack".to_string(),
            "un_i_data" => "to_int".to_string(),
            "un_b_data" => "to_bytes".to_string(),
            "un_list_data" => "to_list".to_string(),
            "un_map_data" => "to_map".to_string(),
            "equals_integer" => "eq".to_string(),
            "less_than_integer" => "lt".to_string(),
            "add_integer" => "add".to_string(),
            "subtract_integer" => "sub".to_string(),
            "multiply_integer" => "mul".to_string(),
            // Hash builtins carry a dotted display name (`Hash.blake2b_256`)
            // that the fallback would keep as an invalid identifier; map them
            // to dot-free stems.
            "Hash.blake2b_256" | "Hash.blake2b_224" => "blake2b".to_string(),
            "Hash.sha256" => "sha256".to_string(),
            "Hash.sha3_256" => "sha3".to_string(),
            "Hash.keccak_256" => "keccak".to_string(),
            "Hash.ripemd_160" => "ripemd".to_string(),
            // The `Int.*` canonical display names are dotted (the raw
            // `*_integer` forms above only match the un-prefixed spelling).
            // Map them to dot-free stems so a binop partial that SURVIVES
            // `inline_partial_binop` (used as a higher-order value) or a
            // non-foldable `Int.quot`/`Int.rem` renders a valid identifier
            // (e.g. `quot_partial`, not the invalid `Int.quot_partial`).
            "Int.add" => "add".to_string(),
            "Int.sub" => "sub".to_string(),
            "Int.mul" => "mul".to_string(),
            "Int.div" => "div".to_string(),
            "Int.mod" => "mod".to_string(),
            "Int.quot" => "quot".to_string(),
            "Int.rem" => "rem".to_string(),
            "Int.eq" => "eq".to_string(),
            "Int.lt" => "lt".to_string(),
            "Int.lte" => "lte".to_string(),
            _ => {
                // Take first word or abbreviate
                if let Some(idx) = name.find('_') {
                    name[..idx].to_string()
                } else if name.len() > 8 {
                    name[..4].to_string()
                } else {
                    name.to_string()
                }
            }
        };
        // A builtin-name hint becomes a VALUE binder (`<stem>_partial`), so the
        // stem must be a lowercase-initial identifier — uppercase is reserved
        // for types/constructors. The dotted-builtin fallback can yield an
        // uppercase stem (`ByteArray.length` → `Byte`, a `List.*` → `List`),
        // producing an invalid `let Byte_partial = …`.
        let mut chars = stem.chars();
        match chars.next() {
            Some(first) if first.is_ascii_uppercase() => {
                first.to_ascii_lowercase().to_string() + chars.as_str()
            }
            _ => stem,
        }
    }

    /// Get hint for parameter by position in a lambda.
    fn param_hint(index: usize, total: usize) -> &'static str {
        if total == 1 {
            "x"
        } else if total == 2 {
            match index {
                0 => "x",
                1 => "y",
                _ => "arg",
            }
        } else if total == 3 {
            match index {
                0 => "x",
                1 => "y",
                2 => "z",
                _ => "arg",
            }
        } else {
            match index {
                0 => "a",
                1 => "b",
                2 => "c",
                3 => "d",
                _ => "arg",
            }
        }
    }
}

impl Default for Renamer {
    fn default() -> Self {
        Self::new()
    }
}

impl ExprFolder for Renamer {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn pre_expr(&mut self, expr: &PseudoExpr) -> crate::pseudo::fold::FoldAction {
        if let PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } = expr
        {
            return crate::pseudo::fold::FoldAction::Replace(self.fold_when_scoped(
                subject.as_ref().clone(),
                subject_name.clone(),
                clauses.clone(),
            ));
        }
        crate::pseudo::fold::FoldAction::Walk
    }

    fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
        PseudoExpr::Var {
            name: self.lookup_with_id(&name, id.get()),
            id,
        }
    }

    fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
        self.push_scope();
        let total = params.len();
        params
            .iter()
            .enumerate()
            .map(|(i, p)| {
                // Preserve semantic validator-entrypoint names already set
                // by `rename_validator_params`; otherwise apply the generic
                // positional hint (x/y/z/…).
                let hint =
                    if crate::decompile::simplify::is_protected_validator_param_name(p.as_str()) {
                        p.as_str()
                    } else {
                        Self::param_hint(i, total)
                    };
                self.bind_binder(p, Some(hint))
            })
            .collect()
    }

    fn exit_lambda(&mut self, _params: &[Binder]) {
        self.pop_scope();
    }

    fn enter_let(&mut self, name: &str, id: &Option<VarId>, value: &PseudoExpr) -> String {
        let hint = self.hint_from_value(value);
        // The source binder name is checked beside the value-derived
        // hint to catch the `lookup_result_2` / `find_result_2`
        // family, which already carries the disambiguated form at
        // rename time.
        if self.tag_synthetic
            && (Self::looks_like_helper_binding(name)
                || Self::looks_like_helper_binding(hint.as_deref().unwrap_or("")))
            && let Some(vid) = id.get()
        {
            self.synthetic_binder_ids.push(vid);
        }
        self.bind_with_id(name, id.get(), hint.as_deref())
    }

    fn exit_let(&mut self, _name: &str) {
        // No-op: let scope is cumulative
    }

    fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
        self.push_scope();
        let new_name = self.bind_binder(name, Some("self_fn"));
        let new_params: Vec<Binder> = params
            .iter()
            .map(|p| self.bind_binder(p, Some(p.as_str())))
            .collect();
        (new_name, new_params)
    }

    fn exit_recfn(&mut self, _name: &Binder, _params: &[Binder]) {
        self.pop_scope();
    }

    fn post_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        let new_subject_name =
            subject_name.map(|n| n.renamed(self.lookup_with_id(n.as_ref(), Some(n.id))));
        PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name: new_subject_name,
            clauses,
        }
    }
}

/// Test-only entry point; the pipeline renames through `Renamer`.
/// Rename all variables in an expression to be unique and meaningful.
#[cfg(test)]
pub(crate) fn rename_variables(expr: PseudoExpr) -> PseudoExpr {
    let mut renamer = Renamer::new();
    renamer.fold(expr)
}

/// Variant that also annotates Simplifier-generated helper-let
/// binders (`fn_*`, `lookup_*_result`, `find_*_result`, etc.) with
/// `VarKind::Synthetic` in `kind_annotations`.
///
/// The recovery passes' typed predicate can then dispatch by
/// VarKind for these binders instead of the name-pattern heuristic.
pub(crate) fn rename_variables_with_kind_annotations(
    expr: PseudoExpr,
    kind_annotations: &mut HashMap<VarId, crate::pseudo::nameless::VarKind>,
) -> PseudoExpr {
    let mut renamer = Renamer::new().enable_synthetic_tagging();
    let renamed = renamer.fold(expr);
    for vid in renamer.take_synthetic_binder_ids() {
        kind_annotations
            .entry(vid)
            .or_insert(crate::pseudo::nameless::VarKind::Synthetic);
    }
    renamed
}

#[cfg(test)]
mod tests;
