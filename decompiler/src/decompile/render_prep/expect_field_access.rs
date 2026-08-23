//! Rewrite `FieldAccess { record: Var{name:"expect!", id:None},
//! selector }` to `PseudoExpr::Error { message: None }` (renders as
//! `fail`).
//!
//! The synthetic helper `Var "expect!"` (id: None) is the
//! simplifier's assertion sentinel: evaluating it aborts the script.
//! In rare paths it leaks into expression position bare — e.g.
//! `when ... is { Constr<1> -> expect!.fst; _ -> ... }` — which is
//! not legal surface syntax, since only the macro form `expect!(...)` is
//! rewritten downstream. Reading a field of a value that always
//! aborts never returns, so `fail` preserves the abort.
//!
//! The `id: None` gate scopes the rewrite to the synthetic helper; a
//! user-bound variable named "expect!" is not expressible in the surface's
//! surface syntax, so nothing else can collide.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::ExprFolder;

/// Rewrite `expect!.<selector>` field accesses to `fail`.
pub(super) fn rewrite_expect_field_access(expr: PseudoExpr) -> PseudoExpr {
    struct ExpectFieldAccessFolder;

    impl ExprFolder for ExpectFieldAccessFolder {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_field_access(&mut self, record: PseudoExpr, selector: FieldSelector) -> PseudoExpr {
            // Direct shape: `expect!.<selector>` → `fail`.
            if is_bare_expect_helper(&record) {
                return PseudoExpr::Error { message: None };
            }
            // Cascade: reading a field of a value that always
            // aborts is itself an abort, so `(expect!.fst).snd`
            // must collapse too — otherwise the renderer emits
            // `fail.snd`, invalid surface syntax.
            if let PseudoExpr::Error { message } = record {
                return PseudoExpr::Error { message };
            }
            PseudoExpr::field_access_typed(record, selector)
        }

        fn post_index_access(&mut self, collection: PseudoExpr, index: usize) -> PseudoExpr {
            // Indexing a value-that-aborts is itself an abort; the
            // same cascade as FieldAccess, keeping `fail[N]`
            // (invalid surface syntax) out of the renderer.
            if let PseudoExpr::Error { message } = collection {
                return PseudoExpr::Error { message };
            }
            PseudoExpr::IndexAccess {
                collection: PBox::new(collection),
                index,
            }
        }
    }

    ExpectFieldAccessFolder.fold(expr)
}

/// Returns `true` when `expr` is exactly `Var { name: "expect!",
/// id: None }` — the simplifier's bare assertion sentinel.
///
/// The `id: None` gate is load-bearing: a `Var` named "expect!"
/// carrying a `Some` id is not the synthetic helper and is left
/// alone.
fn is_bare_expect_helper(expr: &PseudoExpr) -> bool {
    matches!(
        expr,
        PseudoExpr::Var { name, id: None } if name.as_str() == "expect!"
    )
}

#[cfg(test)]
mod tests;
