use super::*;
use crate::pseudo::ast::{Binder, WhenClause};

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn wrap_decompiled(params: Vec<Binder>, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "decompiled".to_string(),
        id: Some(VarId::new(99_000)),
        value: PBox::new(PseudoExpr::Lambda {
            params,
            body: PBox::new(body),
        }),
        body: PBox::new(PseudoExpr::Unit),
    }
}

fn count_result_lets(expr: &PseudoExpr) -> usize {
    let mut n = 0;
    walk_lets(expr, &mut |name, _| {
        if name.ends_with("_result") || name.ends_with("_call") {
            n += 1;
        }
    });
    n
}

fn walk_lets<F: FnMut(&str, &PseudoExpr)>(expr: &PseudoExpr, f: &mut F) {
    if let PseudoExpr::Let { name, value, .. } = expr {
        f(name, value);
    }
    for c in children(expr) {
        walk_lets(c, f);
    }
}

/// 3+ identical single-arg calls `f(p)` inside an inner Lambda body where
/// `p` is the Lambda's param. Hoist must fire inside the inner Lambda.
#[test]
fn inner_lambda_single_arg_hoist() {
    let entry_param = binder("ctx", 100);
    let inner_param = binder("p", 200);
    let f_id = VarId::new(60);

    let call = || PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("f", f_id)),
        args: vec![PseudoExpr::var_with_id("p", VarId::new(200))].into(),
    };
    let inner_body = PseudoExpr::Let {
        name: "a".into(),
        id: Some(VarId::new(300)),
        value: PBox::new(call()),
        body: PBox::new(PseudoExpr::Let {
            name: "b".into(),
            id: Some(VarId::new(301)),
            value: PBox::new(call()),
            body: PBox::new(PseudoExpr::Let {
                name: "c".into(),
                id: Some(VarId::new(302)),
                value: PBox::new(call()),
                body: PBox::new(PseudoExpr::var_with_id("p", VarId::new(200))),
            }),
        }),
    };
    let inner_lambda = PseudoExpr::Lambda {
        params: vec![inner_param],
        body: PBox::new(inner_body),
    };
    let expr = wrap_decompiled(vec![entry_param], inner_lambda);

    let out = hoist_entry_param_chain_calls(expr);
    assert_eq!(
        count_result_lets(&out),
        1,
        "expected 1 single-arg hoist (f_result) inside inner Lambda body"
    );
}

/// Running the single-arg pass twice produces the same number of hoists.
#[test]
fn idempotence_single_arg() {
    let entry_param = binder("ctx", 100);
    let inner_param = binder("p", 200);
    let f_id = VarId::new(60);

    let call = || PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("f", f_id)),
        args: vec![PseudoExpr::var_with_id("p", VarId::new(200))].into(),
    };
    let inner_body = PseudoExpr::Let {
        name: "a".into(),
        id: Some(VarId::new(300)),
        value: PBox::new(call()),
        body: PBox::new(PseudoExpr::Let {
            name: "b".into(),
            id: Some(VarId::new(301)),
            value: PBox::new(call()),
            body: PBox::new(PseudoExpr::Let {
                name: "c".into(),
                id: Some(VarId::new(302)),
                value: PBox::new(call()),
                body: PBox::new(PseudoExpr::var_with_id("p", VarId::new(200))),
            }),
        }),
    };
    let inner_lambda = PseudoExpr::Lambda {
        params: vec![inner_param],
        body: PBox::new(inner_body),
    };
    let expr = wrap_decompiled(vec![entry_param], inner_lambda);

    let once = hoist_entry_param_chain_calls(expr);
    let count_once = count_result_lets(&once);
    let twice = hoist_entry_param_chain_calls(once);
    assert_eq!(
        count_once,
        count_result_lets(&twice),
        "second run must not change the number of hoisted lets"
    );
}

/// When-clause pattern binders join the inner scope's stable set.
/// `fn(ctx) { when ctx is { Pair(a, b) -> f(a); f(a); f(a) } }` —
/// 3 `f(a)` calls inside Pair clause body → 1 hoist inside the clause body.
#[test]
fn when_clause_pattern_binder_in_scope() {
    let entry_param = binder("ctx", 100);
    let pair_left = binder("a", 200);
    let pair_right = binder("b", 201);
    let f_id = VarId::new(60);

    let call = || PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("f", f_id)),
        args: vec![PseudoExpr::var_with_id("a", VarId::new(200))].into(),
    };
    let clause_body = PseudoExpr::Let {
        name: "x1".into(),
        id: Some(VarId::new(310)),
        value: PBox::new(call()),
        body: PBox::new(PseudoExpr::Let {
            name: "x2".into(),
            id: Some(VarId::new(311)),
            value: PBox::new(call()),
            body: PBox::new(PseudoExpr::Let {
                name: "x3".into(),
                id: Some(VarId::new(312)),
                value: PBox::new(call()),
                body: PBox::new(PseudoExpr::var_with_id("a", VarId::new(200))),
            }),
        }),
    };
    let entry_body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("ctx", VarId::new(100))),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: crate::pseudo::ast::WhenPattern::Pair(pair_left, pair_right),
            guard: None,
            body: clause_body,
        }],
    };
    let expr = wrap_decompiled(vec![entry_param], entry_body);

    let out = hoist_entry_param_chain_calls(expr);
    assert_eq!(
        count_result_lets(&out),
        1,
        "expected 1 hoist inside the Pair clause body — pattern binders must enter the scope's stable set"
    );
}
