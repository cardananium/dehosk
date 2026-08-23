use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::var_id::VarId;

/// Guards the `rec fn any(list, u) { … any(tail) }` mis-flatten.
/// Input is a 1-arity rec-fn wrapping a `fn(u) { … }` closure; the
/// recursive call `any(tail)` is intentionally 1-arg because `u`
/// lives in the closure. `flatten_curried_lambda_chain` inside
/// `simplify_recfn` MUST refuse to merge `u` into the outer
/// params: that leaves the recursive call under-applied and
/// silently rewrites the function's runtime arity.
#[test]
fn does_not_flatten_recfn_with_under_applied_self_call() {
    let any_id = VarId::fresh_binding();
    let list_id = VarId::fresh_binding();
    let u_id = VarId::fresh_binding();
    let head_id = VarId::fresh_binding();
    let tail_id = VarId::fresh_binding();

    // Body: when list is { [] -> False; [head, ..tail] -> if head == u
    //   { True } else { any(tail) /* 1-arg call */ } }
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("list", list_id)),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::Bool(false),
            ),
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![Binder::new("head".to_string(), head_id)],
                    tail: Some(Binder::new("tail".to_string(), tail_id)),
                },
                PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::BinOp {
                        op: BinaryOp::Eq,
                        left: PBox::new(PseudoExpr::var_with_id("head", head_id)),
                        right: PBox::new(PseudoExpr::var_with_id("u", u_id)),
                    }),
                    then_branch: PBox::new(PseudoExpr::Bool(true)),
                    else_branch: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var_with_id("any", any_id)),
                        args: vec![PseudoExpr::var_with_id("tail", tail_id)].into(),
                    }),
                },
            ),
        ],
    };

    let recfn = PseudoExpr::RecFn {
        name: Binder::new("any".to_string(), any_id),
        params: vec![Binder::new("list".to_string(), list_id)],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("u".to_string(), u_id)],
            body: PBox::new(body),
        }),
    };

    let simplified = simplify(recfn);
    let PseudoExpr::RecFn { params, body, .. } = simplified else {
        panic!("expected RecFn at top, got {simplified:?}");
    };
    assert_eq!(
        params.len(),
        1,
        "rec fn must stay 1-arity; flatten would mis-merge u into params"
    );
    assert!(
        matches!(body.as_ref(), PseudoExpr::Lambda { .. }),
        "inner Lambda(u) must be preserved when flatten is unsafe; got {body:?}"
    );
}

/// Positive control: a rec-fn whose self-call DOES match the
/// post-flatten arity is safe to flatten; each recursion here
/// explicitly passes the would-be-merged param.
#[test]
fn flattens_recfn_when_self_call_matches_merged_arity() {
    let any_id = VarId::fresh_binding();
    let list_id = VarId::fresh_binding();
    let u_id = VarId::fresh_binding();
    let head_id = VarId::fresh_binding();
    let tail_id = VarId::fresh_binding();

    // Body: when list is { [] -> False; [head, ..tail] -> if head == u
    //   { True } else { any(tail, u) /* 2-arg call */ } }
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("list", list_id)),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::Bool(false),
            ),
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![Binder::new("head".to_string(), head_id)],
                    tail: Some(Binder::new("tail".to_string(), tail_id)),
                },
                PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::BinOp {
                        op: BinaryOp::Eq,
                        left: PBox::new(PseudoExpr::var_with_id("head", head_id)),
                        right: PBox::new(PseudoExpr::var_with_id("u", u_id)),
                    }),
                    then_branch: PBox::new(PseudoExpr::Bool(true)),
                    else_branch: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var_with_id("any", any_id)),
                        args: vec![
                            PseudoExpr::var_with_id("tail", tail_id),
                            PseudoExpr::var_with_id("u", u_id),
                        ]
                        .into(),
                    }),
                },
            ),
        ],
    };

    let recfn = PseudoExpr::RecFn {
        name: Binder::new("any".to_string(), any_id),
        params: vec![Binder::new("list".to_string(), list_id)],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("u".to_string(), u_id)],
            body: PBox::new(body),
        }),
    };

    let simplified = simplify(recfn);
    let PseudoExpr::RecFn { params, .. } = simplified else {
        panic!("expected RecFn at top")
    };
    assert_eq!(
        params.len(),
        2,
        "flatten should merge u into rec-fn params when self-call arity matches"
    );
}
