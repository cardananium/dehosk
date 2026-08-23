use super::*;
use crate::pseudo::ast::Binder;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// Wrap a body in `let decompiled = fn(<params>) { <body> } in Unit`,
/// matching the AST shape the pass scans for.
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

/// Count `let` bindings named `*_args` / `*_args_N`.
fn count_args_lets(expr: &PseudoExpr) -> usize {
    let mut n = 0;
    walk_lets(expr, &mut |name, _| {
        if name.ends_with("_args") || name.contains("_args_") {
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

/// Three identical multi-arg calls inside an inner Lambda body must hoist
/// inside that body. The args are the Lambda's param plus an Int literal,
/// which supplies the non-Var arg the matcher requires.
#[test]
fn inner_lambda_scope_multi_arg_hoist() {
    let entry_param = binder("ctx", 100);
    let inner_lambda_param = binder("p", 200);
    let helper_id = VarId::new(60);

    // Build: helper(Int(5), Var(p))
    let call = || PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("helper", helper_id)),
        args: vec![
            PseudoExpr::int(5),
            PseudoExpr::var_with_id("p", VarId::new(200)),
        ]
        .into(),
    };
    // Inner Lambda body: `fn(p) { call; call; call; p }` (sequential via lets).
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
                body: PBox::new(varref("p", 200)),
            }),
        }),
    };
    let inner_lambda = PseudoExpr::Lambda {
        params: vec![inner_lambda_param],
        body: PBox::new(inner_body),
    };
    let entry_body = inner_lambda;
    let expr = wrap_decompiled(vec![entry_param], entry_body);

    let out = hoist_pure_multi_arg_calls(expr);
    assert_eq!(
        count_args_lets(&out),
        1,
        "expected exactly 1 `_args` hoist inside inner Lambda body"
    );
}

/// A second run over the pass's output must add no further hoists.
#[test]
fn idempotence() {
    let entry_param = binder("ctx", 100);
    let inner_lambda_param = binder("p", 200);
    let helper_id = VarId::new(60);

    let call = || PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("helper", helper_id)),
        args: vec![
            PseudoExpr::int(5),
            PseudoExpr::var_with_id("p", VarId::new(200)),
        ]
        .into(),
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
                body: PBox::new(varref("p", 200)),
            }),
        }),
    };
    let inner_lambda = PseudoExpr::Lambda {
        params: vec![inner_lambda_param],
        body: PBox::new(inner_body),
    };
    let expr = wrap_decompiled(vec![entry_param], inner_lambda);

    let once = hoist_pure_multi_arg_calls(expr.clone());
    let twice = hoist_pure_multi_arg_calls(once.clone());
    assert_eq!(
        count_args_lets(&once),
        count_args_lets(&twice),
        "second run must not produce additional `_args` hoists"
    );
}

/// Two hoists of the SAME helper with different argument lists, built at a
/// caller-chosen id offset. Returns the binding names for `helper(5, p)`
/// and `helper(7, q)`: which keeps the unsuffixed `helper_args`, and which
/// becomes `helper_args_2`.
///
/// The offset stands in for process state: `VarId`s come from a
/// thread-local counter that keeps climbing, so a second decompilation in
/// one process sees the same program under larger ids.
fn hoist_names_at_offset(offset: u32) -> (String, String) {
    let p_id = VarId::new(offset + 200);
    let q_id = VarId::new(offset + 201);
    let helper_id = VarId::new(offset + 60);
    let params = vec![
        binder("ctx", offset + 100),
        binder("p", offset + 200),
        binder("q", offset + 201),
    ];

    // `helper(5, p)` occurs first, `helper(7, q)` second.
    let call_p = || PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("helper", helper_id)),
        args: vec![PseudoExpr::int(5), PseudoExpr::var_with_id("p", p_id)].into(),
    };
    let call_q = || PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("helper", helper_id)),
        args: vec![PseudoExpr::int(7), PseudoExpr::var_with_id("q", q_id)].into(),
    };

    let mut body = PseudoExpr::var_with_id("p", p_id);
    // Build the let chain bottom-up, so the LAST one built is the outermost
    // and therefore the first in reading order. `is_p` picks which call
    // this link holds: three of each, the pass's hoist threshold.
    for (i, is_p) in [
        (0, false),
        (1, false),
        (2, false),
        (3, true),
        (4, true),
        (5, true),
    ] {
        body = PseudoExpr::Let {
            name: format!("u{i}"),
            id: Some(VarId::new(offset + 300 + i)),
            value: PBox::new(if is_p { call_p() } else { call_q() }),
            body: PBox::new(body),
        };
    }

    let out = hoist_pure_multi_arg_calls(wrap_decompiled(params, body));

    let mut name_for_p = None;
    let mut name_for_q = None;
    walk_lets(&out, &mut |name, value| {
        if !(name.ends_with("_args") || name.contains("_args_")) {
            return;
        }
        if let PseudoExpr::Apply { args, .. } = value {
            match args.first() {
                Some(PseudoExpr::Int(n)) if n.to_string() == "5" => {
                    name_for_p = Some(name.to_string())
                }
                Some(PseudoExpr::Int(n)) if n.to_string() == "7" => {
                    name_for_q = Some(name.to_string())
                }
                _ => {}
            }
        }
    });
    (
        name_for_p.expect("helper(5, p) must be hoisted"),
        name_for_q.expect("helper(7, q) must be hoisted"),
    )
}

/// Which hoist keeps the plain `helper_args` name must be a fact about the
/// program, not about how many `VarId`s the process has already handed out.
///
/// A plan order of `(fn_id, args_hash)` hashes the arguments' free
/// `VarId`s, so shifting every id — what a second decompilation in the
/// same process does — reshuffles the hashes and swaps the two names.
#[test]
fn hoist_naming_survives_a_shifted_var_id_counter() {
    let expected = hoist_names_at_offset(0);
    assert_eq!(
        expected,
        ("helper_args".to_string(), "helper_args_2".to_string()),
        "the first call in reading order keeps the unsuffixed name"
    );
    // A hash-ordered sort agrees with first-occurrence order about half the
    // time, so one offset proves nothing; 40 of them settle it.
    for offset in 1..40u32 {
        assert_eq!(
            hoist_names_at_offset(offset * 1_000),
            expected,
            "hoist naming drifted at id offset {}",
            offset * 1_000
        );
    }
}
