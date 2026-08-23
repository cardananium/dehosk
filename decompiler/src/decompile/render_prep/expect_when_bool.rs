//! Detect the Bool-shaped `When` inside an `expect!` chain and rewrite
//! it to the pattern-expect shape, so the renderer emits legal surface
//! syntax `expect P = X`.
//!
//! The chain renderer (`pseudo/pretty_helpers/traversal.rs`) turns
//! `Apply(expect!, [cond, body])` into `expect <cond>; <body>`. When
//! the simplifier leaves a Bool-valued `When` in `cond` position, that
//! becomes `expect when X is { P -> True; _ -> False }`, which is
//! invalid surface syntax. The intent was "abort if X doesn't match P,
//! else continue" — i.e. the standard `expect P = X` pattern.
//!
//! Convert the outer shape into the When-with-fail-arm form that
//! `extract_expect_pattern` (`pseudo/pretty_helpers/dispatch.rs`)
//! already recognises: the matched arm runs `tail` (the continuation
//! after the assertion succeeds) and the wildcard arm becomes `Error`.
//! That leaves exactly one non-fail clause for `extract_expect_pattern`
//! to emit as `expect P = X`, followed by `tail`.
//!
//! - The function is the bare synthetic `Var{name:"expect!"}` helper.
//! - `args.len() == 2` — cond plus tail; the 3-arg fail-message form
//!   keeps a String in `args[2]` and is out of scope.
//! - Cond is a `When` with no `subject_name` (no `as` aliasing) and no
//!   clause guards; its subject `X` may be any expression.
//! - Exactly one clause is not an abort arm (`Bool(false)` or a fail),
//!   and its pattern is neither `Wildcard` nor `Var` — an irrefutable
//!   pattern would make the assertion vacuous.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::ExprFolder;

pub(super) fn rewrite_expect_when_bool(expr: PseudoExpr) -> PseudoExpr {
    struct Folder;

    impl ExprFolder for Folder {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
            if let Some(when_expect) = try_rewrite(&function, &args) {
                return when_expect;
            }
            PseudoExpr::Apply {
                function: PBox::new(function),
                args: args.into(),
            }
        }
    }

    Folder.fold(expr)
}

fn try_rewrite(function: &PseudoExpr, args: &[PseudoExpr]) -> Option<PseudoExpr> {
    if !is_bare_expect_helper(function) {
        return None;
    }
    if args.len() != 2 {
        return None;
    }
    let when = &args[0];
    let tail = &args[1];

    let PseudoExpr::When {
        subject,
        subject_name,
        clauses,
    } = when
    else {
        return None;
    };
    if subject_name.is_some() {
        return None;
    }
    if clauses.is_empty() {
        return None;
    }
    // Bool-test shape: exactly ONE arm with a refutable pattern and
    // any body (the "matched" arm); every OTHER arm has body
    // `Bool(false)` or a fail expression (the "abort" arms).
    //
    // Shape A `P -> True; _ -> False` takes the outer `tail` as the
    // matched body; shape B `P(bindings) -> <real_body>; _ -> False`
    // keeps `<real_body>`, which may use the pattern bindings.
    let mut matched_arm: Option<&WhenClause> = None;
    for clause in clauses {
        if clause.guard.is_some() {
            return None;
        }
        let is_abort =
            matches!(&clause.body, PseudoExpr::Bool(false)) || is_fail_expr(&clause.body);
        if is_abort {
            continue;
        }
        // Non-abort arm — must be the SINGLE matched arm.
        if matched_arm.is_some() {
            return None;
        }
        if matches!(&clause.pattern, WhenPattern::Wildcard | WhenPattern::Var(_)) {
            // Refutable pattern required — wildcard/var match
            // everything, so the assertion would be vacuous.
            return None;
        }
        matched_arm = Some(clause);
    }
    let matched = matched_arm?;

    // Build the rewritten When. Semantics-preserving:
    //
    //   Apply(expect!, [When{P → body, _ → False}, tail])
    //   When{P → Apply(expect!, [body, tail]), _ → fail}
    //
    // Both abort unless X matches P and `body` is True, and then
    // run `tail`.
    //
    // If `body` is `Bool(true)` the inner
    // `Apply(expect!, [Bool(true), tail])` is redundant — use
    // `tail` directly, else the renderer emits a vacuous
    // `expect True` line.
    let new_matched_body = match &matched.body {
        PseudoExpr::Bool(true) => tail.clone(),
        body => PseudoExpr::Apply {
            function: PBox::new(function.clone()),
            args: vec![body.clone(), tail.clone()].into(),
        },
    };

    let rewritten_clauses = vec![
        WhenClause {
            pattern: matched.pattern.clone(),
            guard: None,
            body: new_matched_body,
        },
        WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body: PseudoExpr::Error { message: None },
        },
    ];
    Some(PseudoExpr::When {
        subject: subject.clone(),
        subject_name: None,
        clauses: rewritten_clauses,
    })
}

/// Helper: is this expression an abort sentinel?
fn is_fail_expr(expr: &PseudoExpr) -> bool {
    matches!(expr, PseudoExpr::Error { .. })
        || matches!(
            expr,
            PseudoExpr::BuiltinCall { name, .. } if *name == crate::BuiltinId::Error
        )
}

/// Match `Var { name: "expect!", .. }` regardless of `id` — same
/// policy as `is_expect_bang` in `pseudo/pretty_helpers/traversal.rs`.
/// The simplifier sometimes assigns a VarId to the synthetic helper,
/// so requiring `id: None` would miss those cases.
fn is_bare_expect_helper(expr: &PseudoExpr) -> bool {
    matches!(
        expr,
        PseudoExpr::Var { name, .. } if name.as_str() == "expect!"
    )
}

#[cfg(test)]
mod tests;
