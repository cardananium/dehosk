//! Rename binders that nothing references: synthetic placeholders
//! blank to `_`, and `when`-pattern binders with real names take a
//! leading `_`.
//!
//! Runs after the other rewrites have settled, so the reference
//! counts reflect the final render. The rename is DISPLAY only —
//! `set_display_name` keeps the original `semantic_name` and the
//! binder's `VarId` for scope and downstream inspection.
//!
//! The motivating case is PlutusTx `traceIfFalse` instrumentation:
//! `trace(@"entering X", fn(__N) { trace @"exiting X"; body },
//! Void)` binds a unit-thunk arg that is never referenced, so
//! without this pass the render fills with `fn(__2) { … }`,
//! `fn(__346) { … }` instead of `fn(_) { … }`.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::{ExprFolder, ExprVisitor};
use crate::pseudo::var_id::VarId;

pub(super) fn rename_unused_lambda_params(expr: PseudoExpr) -> PseudoExpr {
    run(expr, RenameMode::BlankPlaceholders)
}

/// `_`-prefix unused NON-placeholder `when`-pattern binders
/// (`Spending(output_reference, datum)` → `Spending(_output_reference,
/// datum)` when `output_reference` is unused). The prefix preserves a
/// possibly meaningful name while signalling "unused", so it is safe
/// regardless of blueprint provenance.
///
/// MUST run LATE — after Scott-eliminator resolution and inlining have
/// materialized their references — or the count is taken before a
/// binder's only reference exists (a record field referenced only once
/// `resolve_scott_eliminator` has lowered the eliminator would be
/// marked unused). Lambda params are left untouched: a deliberate
/// semantic name stays visible even when unused.
pub(super) fn underscore_unused_pattern_binders(expr: PseudoExpr) -> PseudoExpr {
    run(expr, RenameMode::PrefixNonPlaceholders)
}

#[derive(Clone, Copy, PartialEq)]
enum RenameMode {
    /// Blank an unused SYNTHETIC-placeholder binder to a bare `_` (the name
    /// carries no information). Applies to Lambda params + When patterns.
    BlankPlaceholders,
    /// `_`-prefix an unused NON-placeholder When-pattern binder (preserve the
    /// name). Does NOT touch Lambda params or placeholder names.
    PrefixNonPlaceholders,
}

fn run(expr: PseudoExpr, mode: RenameMode) -> PseudoExpr {
    let counts = count_var_uses(&expr);
    let name_only_counts = count_name_only_refs(&expr);
    let mut renamer = Renamer {
        counts,
        name_only_counts,
        mode,
    };
    renamer.fold(expr)
}

fn count_var_uses(expr: &PseudoExpr) -> HashMap<VarId, usize> {
    struct UseCounter {
        counts: HashMap<VarId, usize>,
    }
    impl ExprVisitor for UseCounter {
        fn visit_var(&mut self, _name: &str, id: &Option<VarId>) {
            if let Some(id) = id {
                *self.counts.entry(*id).or_insert(0) += 1;
            }
        }
    }
    let mut counter = UseCounter {
        counts: HashMap::new(),
    };
    counter.walk(expr);
    counter.counts
}

/// Count Var references that carry no `id`, keyed by name. Which
/// binder such a ref points at is unknowable once the id is lost, so
/// any name-only ref counts as evidence that the binder is used —
/// that over-counts and suppresses some `_` cleanup, but never
/// strands a free reference.
fn count_name_only_refs(expr: &PseudoExpr) -> HashMap<String, usize> {
    struct NameOnlyCounter {
        counts: HashMap<String, usize>,
    }
    impl ExprVisitor for NameOnlyCounter {
        fn visit_var(&mut self, name: &str, id: &Option<VarId>) {
            if id.is_none() {
                *self.counts.entry(name.to_string()).or_insert(0) += 1;
            }
        }
    }
    let mut counter = NameOnlyCounter {
        counts: HashMap::new(),
    };
    counter.walk(expr);
    counter.counts
}

struct Renamer {
    counts: HashMap<VarId, usize>,
    name_only_counts: HashMap<String, usize>,
    mode: RenameMode,
}

impl Renamer {
    /// Rename one `Binder` in-place if it qualifies for `_` collapse.
    ///
    /// `blueprint_safe`: when `false`, the binder lives under a
    /// `Constructor` pattern whose `type_hint` carries blueprint
    /// metadata. Skip the "common-word" placeholder names
    /// (`payload`, `variant`) in that scope — they could be
    /// user-meaningful field names from the blueprint. Digit-suffixed
    /// synthetic shapes (`x_N`, `field_N`, etc.) are still safe.
    fn maybe_rename(&self, p: &mut crate::pseudo::ast::Binder, blueprint_safe: bool) {
        let name = p.as_str();
        if name == "_" {
            return;
        }
        match self.mode {
            RenameMode::BlankPlaceholders => {
                // Only SYNTHETIC placeholder names blank to a bare `_`.
                if !looks_like_placeholder(name) {
                    return;
                }
                if !blueprint_safe && is_blueprint_leakable_placeholder(name) {
                    return;
                }
                if self.is_unused(p) {
                    p.set_display_name("_");
                }
            }
            RenameMode::PrefixNonPlaceholders => {
                // Only NON-placeholder names, `_`-prefixed (name preserved).
                // Already-`_`-prefixed names are skipped (idempotence — and the
                // synthetic `__N` placeholders are handled by the blank pass).
                if name.starts_with('_') || looks_like_placeholder(name) {
                    return;
                }
                if self.is_unused(p) {
                    let prefixed = format!("_{name}");
                    p.set_display_name(&prefixed);
                }
            }
        }
    }

    /// A binder is unused iff neither an id-keyed ref nor a name-only ref
    /// exists; the name-only half over-counts under shadowing (see
    /// `count_name_only_refs`).
    fn is_unused(&self, p: &crate::pseudo::ast::Binder) -> bool {
        let id_count = self.counts.get(&p.id).copied().unwrap_or(0);
        let name_only_count = self.name_only_counts.get(p.as_str()).copied().unwrap_or(0);
        id_count == 0 && name_only_count == 0
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
    fn post_lambda(
        &mut self,
        params: Vec<crate::pseudo::ast::Binder>,
        body: PseudoExpr,
    ) -> PseudoExpr {
        // Lambda params are only touched by the blank-placeholders mode; the
        // prefix mode is for `when`-pattern binders only, so a deliberate
        // semantic lambda param name stays visible even when unused.
        let new_params = if self.mode == RenameMode::BlankPlaceholders {
            params
                .into_iter()
                .map(|mut p| {
                    self.maybe_rename(&mut p, true);
                    p
                })
                .collect()
        } else {
            params
        };
        PseudoExpr::Lambda {
            params: new_params,
            body: PBox::new(body),
        }
    }

    fn post_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<crate::pseudo::ast::Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        // Rename clause-pattern binders the way Lambda params are
        // treated: placeholder names with zero references in the body
        // collapse to `_`.
        let new_clauses = clauses
            .into_iter()
            .map(|c| WhenClause {
                pattern: self.rename_pattern(c.pattern),
                guard: c.guard,
                body: c.body,
            })
            .collect();
        PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name,
            clauses: new_clauses,
        }
    }
}

impl Renamer {
    fn rename_pattern(&self, pattern: WhenPattern) -> WhenPattern {
        match pattern {
            WhenPattern::Constructor {
                type_hint,
                tag,
                fields,
                shape,
            } => {
                // A `type_hint` is either blueprint metadata (a
                // user-named field) or a synthetic hint from
                // `data_resolution` / `cardano_context_naming`. Any
                // `Some` counts as possibly-blueprint, so common-word
                // placeholders (payload/variant) survive; other
                // placeholder shapes collapse regardless — see
                // `is_blueprint_leakable_placeholder`.
                let blueprint_safe = type_hint.is_none();
                WhenPattern::Constructor {
                    type_hint,
                    tag,
                    fields: fields
                        .into_iter()
                        .map(|mut b| {
                            self.maybe_rename(&mut b, blueprint_safe);
                            b
                        })
                        .collect(),
                    shape,
                }
            }
            WhenPattern::List { elements, tail } => WhenPattern::List {
                elements: elements
                    .into_iter()
                    .map(|mut b| {
                        self.maybe_rename(&mut b, true);
                        b
                    })
                    .collect(),
                tail: tail.map(|mut b| {
                    self.maybe_rename(&mut b, true);
                    b
                }),
            },
            WhenPattern::Tuple(items) => WhenPattern::Tuple(
                items
                    .into_iter()
                    .map(|mut b| {
                        self.maybe_rename(&mut b, true);
                        b
                    })
                    .collect(),
            ),
            WhenPattern::Pair(mut a, mut b) => {
                self.maybe_rename(&mut a, true);
                self.maybe_rename(&mut b, true);
                WhenPattern::Pair(a, b)
            }
            WhenPattern::Var(mut b) => {
                self.maybe_rename(&mut b, true);
                WhenPattern::Var(b)
            }
            // Wildcard and Literal have no binders to rename.
            other => other,
        }
    }
}

/// `true` for the placeholder names a user blueprint could also have
/// supplied: the common English words `payload` and `variant`. Under a
/// `Constructor` pattern whose `type_hint` may be blueprint metadata,
/// those are left alone instead of collapsing to `_`.
///
/// `field_<N>` / `arg_<N>` are excluded. A blueprint generator could
/// produce them, but they are also the synthetic shapes minted by
/// `decompile::data_resolution` / `cardano_context_naming` for
/// script-context fields, which carry a synthetic `type_hint`; gating
/// them would lose the collapse on those purely structural fields. If
/// a blueprint really declares a field named `field_0`, an unused
/// binder for it collapses to `_` — nothing informative is lost.
///
/// The naming-pass shapes (`x_N`, `y_N`, …, `__N`) are reserved for the
/// decompiler's own naming and never appear in blueprint metadata, so
/// they collapse in any scope.
fn is_blueprint_leakable_placeholder(name: &str) -> bool {
    name == "payload" || name == "variant"
}

fn looks_like_placeholder(name: &str) -> bool {
    if let Some(rest) = name.strip_prefix("__") {
        return !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit() || c == '_');
    }
    // Synthetic domain placeholders.
    if name == "payload" || name == "variant" {
        return true;
    }
    for prefix in ["field_", "arg_"] {
        if let Some(rest) = name.strip_prefix(prefix)
            && !rest.is_empty()
            && rest.chars().all(|c| c.is_ascii_digit() || c == '_')
        {
            return true;
        }
    }
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !matches!(first, 'x' | 'y' | 'z' | 'v' | 'a' | 'b' | 'c' | 'd') {
        return false;
    }
    let rest: String = chars.collect();
    let Some(digits) = rest.strip_prefix('_') else {
        return false;
    };
    !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit() || c == '_')
}

#[cfg(test)]
mod tests;
