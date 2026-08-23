use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

#[test]
fn rewrites_when_on_lambda_subject_with_pair_clause() {
    // `when Lambda(p, body_p) is { Pair(a, b) -> arm_body }`
    // → `Apply(Lambda(p, body_p), [Lambda([a, b], arm_body)])`.
    let p_id = VarId::new(4000);
    let a_id = VarId::new(4001);
    let b_id = VarId::new(4002);
    let subject_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("p", p_id)],
        body: PBox::new(PseudoExpr::var_with_id("p", p_id)),
    };
    let arm_body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("a", a_id)),
        args: vec![PseudoExpr::var_with_id("b", b_id)].into(),
    };
    let when_expr = PseudoExpr::When {
        subject: PBox::new(subject_lambda),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Pair(Binder::new("a", a_id), Binder::new("b", b_id)),
            arm_body,
        )],
    };

    let rewritten = undo_pair_when_on_lambda_subject(when_expr);

    let PseudoExpr::Apply { function, args } = rewritten else {
        panic!("expected Apply, got {:?}", rewritten);
    };
    assert!(matches!(function.as_ref(), PseudoExpr::Lambda { .. }));
    assert_eq!(args.len(), 1);
    let PseudoExpr::Lambda { params, .. } = &args[0] else {
        panic!("expected Lambda arg, got {:?}", args[0]);
    };
    assert_eq!(params.len(), 2);
    assert_eq!(params[0].var_id(), a_id);
    assert_eq!(params[1].var_id(), b_id);
}

#[test]
fn rewrites_when_on_recfn_subject_with_pair_clause() {
    // Same shape but subject is RecFn (Y-comb emit).
    let self_id = VarId::new(4010);
    let p_id = VarId::new(4011);
    let a_id = VarId::new(4012);
    let b_id = VarId::new(4013);

    let rec_fn = PseudoExpr::RecFn {
        name: Binder::new("self", self_id),
        params: vec![Binder::new("p", p_id)],
        body: PBox::new(PseudoExpr::var_with_id("p", p_id)),
    };
    let when_expr = PseudoExpr::When {
        subject: PBox::new(rec_fn),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Pair(Binder::new("a", a_id), Binder::new("b", b_id)),
            PseudoExpr::var_with_id("a", a_id),
        )],
    };

    let rewritten = undo_pair_when_on_lambda_subject(when_expr);
    assert!(
        matches!(rewritten, PseudoExpr::Apply { .. }),
        "RecFn subject must trigger the rewrite, got {:?}",
        rewritten
    );
}

#[test]
fn does_not_rewrite_when_on_var_subject() {
    // `when Var(x) is { Pair(a, b) -> ... }` is correct/idiomatic
    // for real Pair-typed Vars — must not be rewritten.
    let x_id = VarId::new(4020);
    let a_id = VarId::new(4021);
    let b_id = VarId::new(4022);
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Pair(Binder::new("a", a_id), Binder::new("b", b_id)),
            PseudoExpr::var_with_id("a", a_id),
        )],
    };

    let rewritten = undo_pair_when_on_lambda_subject(when_expr.clone());
    assert!(
        matches!(rewritten, PseudoExpr::When { .. }),
        "Var subject must NOT trigger the rewrite, got {:?}",
        rewritten
    );
}

#[test]
fn does_not_rewrite_when_with_multiple_clauses() {
    // Multi-arm Whens (e.g. Pair + wildcard) are out of scope.
    let p_id = VarId::new(4030);
    let a_id = VarId::new(4031);
    let b_id = VarId::new(4032);
    let subject_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("p", p_id)],
        body: PBox::new(PseudoExpr::var_with_id("p", p_id)),
    };
    let when_expr = PseudoExpr::When {
        subject: PBox::new(subject_lambda),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::Pair(Binder::new("a", a_id), Binder::new("b", b_id)),
                PseudoExpr::var_with_id("a", a_id),
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Unit),
        ],
    };

    let rewritten = undo_pair_when_on_lambda_subject(when_expr);
    assert!(
        matches!(rewritten, PseudoExpr::When { .. }),
        "multi-arm When must NOT be rewritten, got {:?}",
        rewritten
    );
}

#[test]
fn does_not_rewrite_when_with_guard() {
    // Guard clauses are out of scope.
    let p_id = VarId::new(4040);
    let a_id = VarId::new(4041);
    let b_id = VarId::new(4042);
    let subject_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("p", p_id)],
        body: PBox::new(PseudoExpr::var_with_id("p", p_id)),
    };
    let when_expr = PseudoExpr::When {
        subject: PBox::new(subject_lambda),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Pair(Binder::new("a", a_id), Binder::new("b", b_id)),
            guard: Some(PseudoExpr::bool(true)),
            body: PseudoExpr::var_with_id("a", a_id),
        }],
    };

    let rewritten = undo_pair_when_on_lambda_subject(when_expr);
    assert!(
        matches!(rewritten, PseudoExpr::When { .. }),
        "When with guard must NOT be rewritten, got {:?}",
        rewritten
    );
}

#[test]
fn does_not_rewrite_when_with_subject_name() {
    // `let pair = subject in when pair is ...` form. The subject
    // is named externally; preserving the name is safer.
    let p_id = VarId::new(4050);
    let pair_id = VarId::new(4051);
    let a_id = VarId::new(4052);
    let b_id = VarId::new(4053);
    let subject_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("p", p_id)],
        body: PBox::new(PseudoExpr::var_with_id("p", p_id)),
    };
    let when_expr = PseudoExpr::When {
        subject: PBox::new(subject_lambda),
        subject_name: Some(Binder::new("pair", pair_id)),
        clauses: vec![WhenClause::new(
            WhenPattern::Pair(Binder::new("a", a_id), Binder::new("b", b_id)),
            PseudoExpr::var_with_id("a", a_id),
        )],
    };

    let rewritten = undo_pair_when_on_lambda_subject(when_expr);
    assert!(
        matches!(rewritten, PseudoExpr::When { .. }),
        "When with subject_name must NOT be rewritten, got {:?}",
        rewritten
    );
}

#[test]
fn does_not_rewrite_when_with_non_pair_pattern() {
    // Non-Pair patterns aren't touched.
    let p_id = VarId::new(4060);
    let subject_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("p", p_id)],
        body: PBox::new(PseudoExpr::var_with_id("p", p_id)),
    };
    let when_expr = PseudoExpr::When {
        subject: PBox::new(subject_lambda),
        subject_name: None,
        clauses: vec![WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Unit)],
    };

    let rewritten = undo_pair_when_on_lambda_subject(when_expr);
    assert!(
        matches!(rewritten, PseudoExpr::When { .. }),
        "non-Pair pattern must NOT trigger rewrite, got {:?}",
        rewritten
    );
}
