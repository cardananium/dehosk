//! Fold a top-level synthetic-alias const whose value is a named
//! recursive function into the bare `rec fn`.
//!
//! The pipeline sometimes binds a recursive helper to a synthetic
//! `field_N(_M)?` const that merely aliases an already-named `rec fn`.
//! Renaming the const binder to the inner function's name makes the
//! binding read `const any = rec fn any(…)`, which the pretty-printer's
//! `let f = rec fn f` rule (see `pseudo/pretty/mod.rs`) collapses to the
//! bare `rec fn`; every `field_N(…)` call site is rewired to `any(…)`.
//! The const's value *is* the `rec fn`, so both denote the same value.
//! The rewire is keyed by the const's `VarId`, so only genuine
//! references move.
//!
//! A skipped fold leaves the honest `field_N` name, never a wrong one:
//! - Only the top-level Let chain (module scope); nested
//!   `let field_N = rec fn …` are left alone.
//! - The const binder name must be a synthetic `field_<digits>(_<digits>)?`
//!   ([`is_synthetic_field_name`]) and the inner name must not be synthetic
//!   — the fold has to buy a real name.
//! - Collision guard: the renderer is name-only, so two bindings that
//!   render to the same identifier fuse. The inner name, after the
//!   renderer's keyword sanitization, must appear as a binder exactly
//!   once in the whole program — i.e. only as this `rec fn`'s own name.
//!   That single check covers a local binder in scope at a rewritten
//!   call site, a root-layout-hoisted helper that renders top-level,
//!   another top-level binding of the same name, and a distinct raw
//!   name that sanitizes to the same rendered identifier. Otherwise:
//!   skip.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::decompile::render::sanitize_identifier;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;

use super::rename_synthetic_field_let_binders::{is_synthetic_field_name, rename_var_in};

pub(super) fn fold_const_recfn_alias(expr: PseudoExpr) -> PseudoExpr {
    // Binder-name counts, in RENDERED form, for the collision guard.
    let binder_counts = count_all_binder_names(&expr);

    // Operate only on the top-level Let chain.
    let (mut chain, terminal) = unwind_chain(expr);

    // Decide which consts to fold: (const VarId, inner fn name).
    let mut renames: Vec<(VarId, String)> = Vec::new();
    for (name, id, value) in chain.iter() {
        let Some(const_id) = id else { continue };
        if !is_synthetic_field_name(name) {
            continue;
        }
        let PseudoExpr::RecFn { name: inner, .. } = value else {
            continue;
        };
        let inner = inner.as_str();
        if inner == name.as_str() || is_synthetic_field_name(inner) {
            continue;
        }
        // Collision guard: `inner`'s rendered identifier must occur
        // exactly once as a binder program-wide, or the name-only
        // renderer would fuse or capture references.
        if binder_counts
            .get(&sanitize_identifier(inner))
            .copied()
            .unwrap_or(0)
            != 1
        {
            continue;
        }
        renames.push((*const_id, inner.to_string()));
    }

    if renames.is_empty() {
        return rebuild_chain(chain, terminal);
    }

    // Rename each folded const's binder name in the chain.
    for (const_id, inner) in &renames {
        for (n, id, _) in chain.iter_mut() {
            if *id == Some(*const_id) {
                *n = inner.clone();
            }
        }
    }

    // Rebuild, then rewire every reference (by VarId) to the new name.
    let mut rebuilt = rebuild_chain(chain, terminal);
    for (const_id, inner) in &renames {
        rebuilt = rename_var_in(rebuilt, *const_id, inner);
    }
    rebuilt
}

/// Count occurrences of each binder name (keyed by its rendered, sanitized
/// form) anywhere in `expr` — Let/Lambda/RecFn binders, `when` subject
/// aliases, and all `when`-pattern binders.
fn count_all_binder_names(expr: &PseudoExpr) -> HashMap<String, usize> {
    struct Counter {
        counts: HashMap<String, usize>,
    }
    impl Counter {
        fn bump(&mut self, name: &str) {
            *self.counts.entry(sanitize_identifier(name)).or_insert(0) += 1;
        }
        fn bump_pattern(&mut self, pattern: &WhenPattern) {
            match pattern {
                WhenPattern::Constructor { fields, .. } => {
                    for f in fields {
                        self.bump(f.as_str());
                    }
                }
                WhenPattern::List { elements, tail } => {
                    for e in elements {
                        self.bump(e.as_str());
                    }
                    if let Some(t) = tail {
                        self.bump(t.as_str());
                    }
                }
                WhenPattern::Tuple(bs) => {
                    for b in bs {
                        self.bump(b.as_str());
                    }
                }
                WhenPattern::Pair(a, b) => {
                    self.bump(a.as_str());
                    self.bump(b.as_str());
                }
                WhenPattern::Var(b) => self.bump(b.as_str()),
                WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
            }
        }
    }
    impl ExprVisitor for Counter {
        fn visit_let_pre(&mut self, name: &str) {
            self.bump(name);
        }
        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            for p in params {
                self.bump(p.as_str());
            }
        }
        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            self.bump(name.as_str());
            for p in params {
                self.bump(p.as_str());
            }
        }
        fn visit_when_clause_pre(&mut self, _subject_name: Option<&Binder>, clause: &WhenClause) {
            self.bump_pattern(&clause.pattern);
        }
        fn visit_when(
            &mut self,
            _subject: &PseudoExpr,
            subject_name: Option<&Binder>,
            _clauses: &[WhenClause],
        ) {
            if let Some(b) = subject_name {
                self.bump(b.as_str());
            }
        }
    }
    let mut c = Counter {
        counts: HashMap::new(),
    };
    c.walk(expr);
    c.counts
}

/// Unwind the top-level `Let` chain into `(name, id, value)` triples plus
/// the terminal (non-`Let`) body.
fn unwind_chain(mut expr: PseudoExpr) -> (Vec<(String, Option<VarId>, PseudoExpr)>, PseudoExpr) {
    let mut chain = Vec::new();
    loop {
        match expr {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                chain.push((name, id, value.into_inner()));
                expr = body.into_inner();
            }
            other => return (chain, other),
        }
    }
}

/// Re-nest a `(name, id, value)` chain back into `Let`s ending in `terminal`.
fn rebuild_chain(
    chain: Vec<(String, Option<VarId>, PseudoExpr)>,
    terminal: PseudoExpr,
) -> PseudoExpr {
    let mut acc = terminal;
    for (name, id, value) in chain.into_iter().rev() {
        acc = PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(acc),
        };
    }
    acc
}

#[cfg(test)]
mod tests;
