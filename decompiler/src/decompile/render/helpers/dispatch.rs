//! Fail / expect!-pattern / Option-display dispatch helpers.
//!
//! These inspect AST shapes so the renderer in `pretty.rs` can choose
//! between plain `when` output, `expect!` sugar, and Option-specific
//! rewrites.

use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};

pub(in crate::decompile::render) fn is_fail_expr(expr: &PseudoExpr) -> bool {
    matches!(expr, PseudoExpr::Error { .. })
        || matches!(expr, PseudoExpr::BuiltinCall { name, .. } if *name == crate::BuiltinId::Error)
}

/// Extract a single-branch expect pattern from when clauses.
///
/// Returns `Some((pattern, body))` when exactly one clause is non-fail and
/// all others fail (wildcard fail arms included). A guard anywhere, or a
/// wildcard/var non-fail clause, gives `None`.
pub(in crate::decompile::render) fn extract_expect_pattern(
    clauses: &[WhenClause],
) -> Option<(&WhenPattern, &PseudoExpr)> {
    let mut real_clause: Option<&WhenClause> = None;

    for clause in clauses {
        if clause.guard.is_some() {
            return None;
        }
        if is_fail_expr(&clause.body) {
            continue;
        }
        if real_clause.is_some() {
            return None;
        }
        if matches!(&clause.pattern, WhenPattern::Wildcard | WhenPattern::Var(_)) {
            return None;
        }
        real_clause = Some(clause);
    }

    real_clause.map(|c| (&c.pattern, &c.body))
}

/// For an expect-sugar `when` (single real clause, all others fail), return the
/// message that represents the `expect` failure, if unambiguous.
///
/// The default `expect P = X` sugar DROPS the fail arm's message; the opt-in
/// `expect P = X or fail @"msg"` rendering uses this to preserve it. All fail
/// arms collectively cover "`X` ≠ `P`", so selection is:
///
///   1. A wildcard/var catch-all fail arm's message wins — it IS the "anything
///      else" failure (`A -> fail @"A"; B -> body; _ -> fail @"D"` → `@"D"`).
///   2. Otherwise EXACTLY ONE fail arm with a message — the unambiguous
///      complement case (`Some(v) -> v; None -> fail @"msg"`).
///   3. Otherwise SEVERAL fail arms whose messages are ALL IDENTICAL.
///   4. Otherwise (several DISTINCT non-catch-all messages) → `None`: render
///      bare `expect P = X` rather than guess.
///
/// Only `PseudoExpr::Error { message: Some(_) }` carries a message (the
/// builtin-`Error` fail form is message-less); an empty `Some("")` IS one — it
/// renders as `fail @""`.
pub(in crate::decompile::render) fn extract_expect_fail_message(
    clauses: &[WhenClause],
) -> Option<&str> {
    let mut catch_all: Option<&str> = None;
    let mut messages: Vec<&str> = Vec::new();
    for clause in clauses {
        let msg = match &clause.body {
            PseudoExpr::Error { message: Some(m) } => m.as_str(),
            _ => continue,
        };
        messages.push(msg);
        if matches!(&clause.pattern, WhenPattern::Wildcard | WhenPattern::Var(_)) {
            catch_all = Some(msg);
        }
    }
    if let Some(catch_all) = catch_all {
        return Some(catch_all);
    }
    match messages.as_slice() {
        [] => None,
        [single] => Some(single),
        // Several non-catch-all messages: unambiguous only if all identical.
        [first, rest @ ..] if rest.iter().all(|m| m == first) => Some(first),
        _ => None,
    }
}

pub(in crate::decompile::render) fn when_subject_name_matches(
    subject: &PseudoExpr,
    subject_name: &str,
) -> bool {
    matches!(subject, PseudoExpr::Var { name, .. } if name == subject_name)
}

pub(in crate::decompile::render) fn is_display_option_none_candidate(expr: &PseudoExpr) -> bool {
    matches!(expr, PseudoExpr::Bool(true))
        || matches!(
            expr,
            PseudoExpr::Constr {
                shape: ConstructorShape::Known(KnownConstructor::None),
                ..
            }
        )
        || matches!(
            expr,
            PseudoExpr::Constr {
                shape: ConstructorShape::Unknown {
                    tag: 1,
                    arity: 0,
                    ..
                },
                ..
            }
        )
}
