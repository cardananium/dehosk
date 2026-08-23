use super::*;

use crate::pseudo::ast::WhenClause;
use crate::pseudo::constructor::ConstructorShape;

fn ident(x: VarId) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![Binder::new("x", x)],
        body: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(x),
        }),
    }
}

fn fail() -> PseudoExpr {
    PseudoExpr::Error {
        message: Some("PT1".to_string()),
    }
}

fn ctor_pat() -> WhenPattern {
    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![])
}

/// `when Var(subj) is { Ctor -> <body>; _ -> <fallback> }`.
fn when2(subj: VarId, ctor_body: PseudoExpr, fallback: PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "s".to_string(),
            id: Some(subj),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: ctor_pat(),
                guard: None,
                body: ctor_body,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: fallback,
            },
        ],
    }
}

/// Build the program:
///   let f = fn(p0, p_id, p2) { p_id(1) }
///   in let r = f(arg0, slot1_arg, 2) in r
fn program(arg0: PseudoExpr, slot1_arg: PseudoExpr) -> (PseudoExpr, VarId, VarId) {
    let fid = VarId::fresh_binding();
    let rid = VarId::fresh_binding();
    let (p0, p_id, p2, x) = (
        VarId::fresh_binding(),
        VarId::fresh_binding(),
        VarId::fresh_binding(),
        VarId::fresh_binding(),
    );
    let f_body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: "p_id".to_string(),
            id: Some(p_id),
        }),
        args: vec![PseudoExpr::int(1)].into(),
    };
    let _ = x;
    let f_lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("p0", p0),
            Binder::new("p_id", p_id),
            Binder::new("p2", p2),
        ],
        body: PBox::new(f_body),
    };
    let call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: "f".to_string(),
            id: Some(fid),
        }),
        args: vec![arg0, slot1_arg, PseudoExpr::int(2)].into(),
    };
    let call_let = PseudoExpr::Let {
        name: "r".to_string(),
        id: Some(rid),
        value: PBox::new(call),
        body: PBox::new(PseudoExpr::Var {
            name: "r".to_string(),
            id: Some(rid),
        }),
    };
    let prog = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(fid),
        value: PBox::new(f_lambda),
        body: PBox::new(call_let),
    };
    (prog, fid, rid)
}

#[test]
fn folds_selector_identity_param() {
    let subj0 = VarId::fresh_binding();
    let redeemer = VarId::fresh_binding();
    let xid = VarId::fresh_binding();
    let arg0 = when2(subj0, PseudoExpr::int(0), fail()); // impure preceding slot
    let selector = when2(redeemer, ident(xid), fail()); // Shape B identity
    let (prog, fid, _rid) = program(arg0, selector);
    let out = inline_identity_params(prog);

    // f def: param p_id (slot 1) dropped → 2 params; body inlined to `1`.
    let PseudoExpr::Let {
        id: Some(out_fid),
        value,
        body,
        ..
    } = out
    else {
        panic!("expected f let");
    };
    assert_eq!(out_fid, fid);
    let PseudoExpr::Lambda {
        params,
        body: fbody,
    } = value.into_inner()
    else {
        panic!("f value should stay a Lambda");
    };
    assert_eq!(params.len(), 2, "p_id param dropped");
    assert!(
        matches!(fbody.as_ref(), PseudoExpr::Int(_)),
        "p_id(1) inlined to 1"
    );

    // Call site: outermost is `let arg_0 = <impure when>`, then a guard
    // When on the selector subject.
    let PseudoExpr::Let {
        name: pre_name,
        body: after_prebind,
        ..
    } = body.into_inner()
    else {
        panic!("expected the arg_0 pre-bind let");
    };
    assert_eq!(pre_name, "arg_0", "impure preceding slot pre-bound");
    let PseudoExpr::When { clauses, .. } = after_prebind.into_inner() else {
        panic!("expected the guard When");
    };
    assert_eq!(clauses.len(), 2);
    // Ctor clause body: `let r = f(arg_0, 2); r` — the reduced 2-arg call.
    let PseudoExpr::Let {
        value: call_val, ..
    } = &clauses[0].body
    else {
        panic!("guard ctor-clause body should be the `let r = f(...)`");
    };
    let PseudoExpr::Apply { args, .. } = call_val.as_ref() else {
        panic!("expected the reduced call");
    };
    assert_eq!(args.len(), 2, "slot dropped → 2 args");
    // fallback clause is the preserved fail.
    assert!(matches!(clauses[1].body, PseudoExpr::Error { .. }));
}

#[test]
fn bare_identity_arg_dropped_without_guard() {
    // slot arg is a bare `fn(x){x}` → dropped, NO guard When introduced.
    let xid = VarId::fresh_binding();
    // arg0 pure (an int) so no pre-bind either.
    let (prog, _fid, _rid) = program(PseudoExpr::int(7), ident(xid));
    let out = inline_identity_params(prog);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("f let");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Let { value, .. }
            if matches!(value.as_ref(), PseudoExpr::Apply { args, .. } if args.len() == 2)),
        "bare-identity slot dropped → plain 2-arg call, no guard, got {body:?}"
    );
}

#[test]
fn bails_when_param_used_as_value() {
    // f body uses p_id as a BARE value (not p_id(arg)) → not application-only → bail.
    let fid = VarId::fresh_binding();
    let rid = VarId::fresh_binding();
    let (p0, p_id, x) = (
        VarId::fresh_binding(),
        VarId::fresh_binding(),
        VarId::fresh_binding(),
    );
    let f_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("p0", p0), Binder::new("p_id", p_id)],
        body: PBox::new(PseudoExpr::Var {
            name: "p_id".to_string(),
            id: Some(p_id),
        }),
    };
    let call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: "f".to_string(),
            id: Some(fid),
        }),
        args: vec![PseudoExpr::int(0), ident(x)].into(),
    };
    let prog = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(fid),
        value: PBox::new(f_lambda),
        body: PBox::new(PseudoExpr::Let {
            name: "r".to_string(),
            id: Some(rid),
            value: PBox::new(call),
            body: PBox::new(PseudoExpr::Var {
                name: "r".to_string(),
                id: Some(rid),
            }),
        }),
    };
    let out = inline_identity_params(prog.clone());
    assert_eq!(out, prog, "param used as bare value must NOT fold");
}

#[test]
fn bails_on_trace_in_sibling_arg() {
    let redeemer = VarId::fresh_binding();
    let xid = VarId::fresh_binding();
    // sibling slot 0 carries a Trace → never-reorder-traces → bail.
    let arg0 = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::string("m")),
        value: PBox::new(PseudoExpr::int(0)),
    };
    let selector = when2(redeemer, ident(xid), fail());
    let (prog, _fid, _rid) = program(arg0, selector);
    let out = inline_identity_params(prog.clone());
    assert_eq!(out, prog, "trace in a sibling arg must block the fold");
}

#[test]
fn bails_on_wildcard_first_selector() {
    // `when s is { _ -> fail; Ctor -> identity }` ALWAYS fails (wildcard first),
    // so it must NOT fold (reordering to Ctor-first would change behavior).
    let redeemer = VarId::fresh_binding();
    let xid = VarId::fresh_binding();
    let reversed = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "s".to_string(),
            id: Some(redeemer),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: fail(),
            },
            WhenClause {
                pattern: ctor_pat(),
                guard: None,
                body: ident(xid),
            },
        ],
    };
    let (prog, _fid, _rid) = program(PseudoExpr::int(0), reversed);
    let out = inline_identity_params(prog.clone());
    assert_eq!(out, prog, "wildcard-first selector must NOT fold");
}

#[test]
fn fresh_name_avoids_collision() {
    let mut used = std::collections::HashSet::new();
    assert_eq!(super::fresh_name("arg_0", &used), "arg_0");
    used.insert("arg_0".to_string());
    assert_eq!(super::fresh_name("arg_0", &used), "arg_0_2");
    used.insert("arg_0_2".to_string());
    assert_eq!(super::fresh_name("arg_0", &used), "arg_0_3");
}

#[test]
fn wildcards_ctor_fields_to_discard() {
    // A named constructor field is discarded to `_` (it was provably unused by
    // the identity branch) so the widened guard can't capture a continuation ref.
    let f = VarId::fresh_binding();
    let pat = WhenPattern::constructor(
        ConstructorShape::unknown_data(0, 1),
        vec![Binder::new("field_99", f)],
    );
    let WhenPattern::Constructor { fields, .. } = super::wildcard_ctor_fields(pat) else {
        panic!("constructor");
    };
    assert_eq!(fields[0].as_str(), "_", "named field discarded");
}

#[test]
fn bails_on_multi_call_site() {
    // Two call sites of f → not single-call-site → bail.
    let fid = VarId::fresh_binding();
    let xid = VarId::fresh_binding();
    let (p0, p_id) = (VarId::fresh_binding(), VarId::fresh_binding());
    let f_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("p0", p0), Binder::new("p_id", p_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Var {
                name: "p_id".to_string(),
                id: Some(p_id),
            }),
            args: vec![PseudoExpr::int(1)].into(),
        }),
    };
    let mk_call = || PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: "f".to_string(),
            id: Some(fid),
        }),
        args: vec![PseudoExpr::int(0), ident(xid)].into(),
    };
    let prog = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(fid),
        value: PBox::new(f_lambda),
        body: PBox::new(PseudoExpr::Tuple((vec![mk_call(), mk_call()]).into())),
    };
    let out = inline_identity_params(prog.clone());
    assert_eq!(out, prog, "multiple call sites must NOT fold");
}
