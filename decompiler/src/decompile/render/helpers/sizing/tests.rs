use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::ast::PBox;
use crate::pseudo::var_id::VarId;

#[test]
fn value_renders_as_function_direct_lambda() {
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("x", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::Unit),
    };
    assert!(value_renders_as_function(&expr));
}

#[test]
fn value_renders_as_function_direct_recfn() {
    let expr = PseudoExpr::RecFn {
        name: Binder::new("f", VarId::fresh_binding()),
        params: vec![Binder::new("x", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::Unit),
    };
    assert!(value_renders_as_function(&expr));
}

#[test]
fn value_renders_as_function_let_chain_terminal_lambda() {
    // let X = (let Y = Lambda in Y) — peek through Let to inner Lambda.
    let y_id = VarId::fresh_binding();
    let inner_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("a", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::Unit),
    };
    let inner_let = PseudoExpr::Let {
        name: "Y".to_string(),
        id: Some(y_id),
        value: PBox::new(inner_lambda),
        body: PBox::new(PseudoExpr::var_with_id("Y", y_id)),
    };
    assert!(value_renders_as_function(&inner_let));
}

#[test]
fn value_renders_as_function_let_chain_with_intermediate_non_lambda() {
    // let X = (let A = Int(1) in (let Y = Lambda in Y))
    // — walks through non-Lambda intermediate let.
    let y_id = VarId::fresh_binding();
    let inner_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("a", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::Unit),
    };
    let inner_let = PseudoExpr::Let {
        name: "Y".to_string(),
        id: Some(y_id),
        value: PBox::new(inner_lambda),
        body: PBox::new(PseudoExpr::var_with_id("Y", y_id)),
    };
    let outer_let = PseudoExpr::Let {
        name: "A".to_string(),
        id: Some(VarId::fresh_binding()),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(inner_let),
    };
    assert!(value_renders_as_function(&outer_let));
}

#[test]
fn value_renders_as_function_returns_false_for_non_function() {
    assert!(!value_renders_as_function(&PseudoExpr::int(42)));
    assert!(!value_renders_as_function(&PseudoExpr::Unit));
    assert!(!value_renders_as_function(&PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![].into(),
    }));
}

#[test]
fn value_renders_as_function_when_lambda_intermediate_discarded() {
    // `let X = (let f = fn(...) { ... } in 42)`: the chain has a
    // Lambda value but the body returns 42, so X is bound to Int,
    // not a function; true here would drop a legitimate type
    // annotation.
    let f_id = VarId::fresh_binding();
    let inner_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("a", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::Unit),
    };
    let inner_let = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(inner_lambda),
        // Body returns 42, NOT Var(f) — `f` is discarded.
        body: PBox::new(PseudoExpr::int(42)),
    };
    assert!(
        !value_renders_as_function(&inner_let),
        "intermediate Lambda discarded by non-Var body must NOT suppress type"
    );
}

#[test]
fn value_renders_as_function_let_returns_lambda_via_var_ref() {
    // The let-binder returned via Var(id) — chain terminal IS the lambda.
    let f_id = VarId::fresh_binding();
    let inner_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("a", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::Unit),
    };
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(inner_lambda),
        body: PBox::new(PseudoExpr::var_with_id("f", f_id)),
    };
    assert!(value_renders_as_function(&expr));
}

#[test]
fn value_renders_as_function_f_ext4_ycomb_apply() {
    // Y-combinator application: `(fn(v) { rec fn self(x) { v(self, x) } })(driver)`.
    // Evaluates to the RecFn, so the use-site type annotation is suppressed.
    let v_id = VarId::fresh_binding();
    let self_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let recfn = PseudoExpr::RecFn {
        name: Binder::new("self", self_id),
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("v", v_id)),
            args: vec![
                PseudoExpr::var_with_id("self", self_id),
                PseudoExpr::var_with_id("x", x_id),
            ]
            .into(),
        }),
    };
    let outer_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("v", v_id)],
        body: PBox::new(recfn),
    };
    let ycomb_apply = PseudoExpr::Apply {
        function: PBox::new(outer_lambda),
        args: vec![PseudoExpr::var("driver")].into(),
    };
    assert!(
        value_renders_as_function(&ycomb_apply),
        "Y-comb application must be recognized as evaluating to a function"
    );
}

#[test]
fn value_renders_as_function_f_ext4_returns_false_for_non_lambda_apply() {
    // Apply with a non-Lambda function head — `f(x)` where `f` is a
    // Var — is not a function value: without type information `f`'s
    // result is unknown, so the type annotation stays.
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![PseudoExpr::int(42)].into(),
    };
    assert!(
        !value_renders_as_function(&expr),
        "generic Apply with Var head must return false"
    );
}

#[test]
fn value_renders_as_function_f_ext6_when_all_clauses_lambda() {
    // `when subject is { _ -> fn(x) { ... }, _ -> fn(y) { ... } }`
    // — every clause body evaluates to a function. Must return true.
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    let lambda_a = PseudoExpr::Lambda {
        params: vec![Binder::new("x", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::Unit),
    };
    let lambda_b = PseudoExpr::Lambda {
        params: vec![Binder::new("y", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::Unit),
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("s")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: lambda_a,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: lambda_b,
            },
        ],
    };
    assert!(
        value_renders_as_function(&expr),
        "When with all-lambda clauses must be recognized as function-valued"
    );
}

#[test]
fn value_renders_as_function_f_ext6_when_skips_fail_picks_lambda() {
    // `when s is { _ -> fail, _ -> fn(x) {...} }` — fail clauses
    // are skipped; the first non-fail body decides.
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::Unit),
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("s")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Error { message: None },
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: lambda,
            },
        ],
    };
    assert!(
        value_renders_as_function(&expr),
        "When with leading fail-clause and trailing lambda-clause must return true"
    );
}

#[test]
fn value_renders_as_function_f_ext6_when_int_clause_returns_false() {
    // `when s is { A -> 42 }` — clause returns Int, not a function.
    // Must return false.
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("s")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body: PseudoExpr::int(42),
        }],
    };
    assert!(
        !value_renders_as_function(&expr),
        "When with Int-valued clause must return false"
    );
}

#[test]
fn value_renders_as_function_f_ext6_if_both_lambda() {
    // `if cond then fn(x) {...} else fn(y) {...}` — both branches
    // are functions; must return true.
    let lambda_a = PseudoExpr::Lambda {
        params: vec![Binder::new("x", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::Unit),
    };
    let lambda_b = PseudoExpr::Lambda {
        params: vec![Binder::new("y", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::Unit),
    };
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Bool(true)),
        then_branch: PBox::new(lambda_a),
        else_branch: PBox::new(lambda_b),
    };
    assert!(
        value_renders_as_function(&expr),
        "If with both branches lambda must return true"
    );
}

#[test]
fn value_renders_as_function_f_ext4_lambda_returning_int_apply() {
    // Negative: applying a Lambda returning an Int yields an Int.
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::int(99)),
    };
    let apply = PseudoExpr::Apply {
        function: PBox::new(lambda),
        args: vec![PseudoExpr::Unit].into(),
    };
    assert!(
        !value_renders_as_function(&apply),
        "Lambda returning Int via Apply must NOT be treated as function"
    );
}
