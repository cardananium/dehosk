use super::*;
use crate::pseudo::ast::WhenPattern;

#[test]
fn test_simple_rename() {
    let expr = PseudoExpr::Let {
        name: "i".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::int(42)),
        body: PBox::new(PseudoExpr::var("i")),
    };

    let renamed = rename_variables(expr);

    if let PseudoExpr::Let { name, body, .. } = renamed {
        // Name should be changed from "i"
        assert_ne!(name, "i");
        // Body should reference the new name
        if let PseudoExpr::Var { name: var_name, .. } = body.into_inner() {
            assert_eq!(name, var_name);
        }
    }
}

#[test]
fn test_nested_scopes() {
    // let i = 1 in let i = 2 in i
    let expr = PseudoExpr::Let {
        name: "i".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "i".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::int(2)),
            body: PBox::new(PseudoExpr::var("i")),
        }),
    };

    let renamed = rename_variables(expr);
    let output = renamed.to_pretty();

    assert!(output.contains("let "));
}

#[test]
fn rename_variables_uniquifies_duplicate_let_names() {
    let outer_id = VarId::new(7101);
    let inner_id = VarId::new(7102);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(inner_id),
            value: PBox::new(PseudoExpr::int(2)),
            body: PBox::new(PseudoExpr::var_with_id("x", inner_id)),
        }),
    };

    let renamed = rename_variables(expr);

    let PseudoExpr::Let {
        name: outer_name,
        body,
        ..
    } = renamed
    else {
        panic!("expected outer let");
    };
    let PseudoExpr::Let {
        name: inner_name,
        body: inner_body,
        ..
    } = body.into_inner()
    else {
        panic!("expected inner let");
    };
    assert_ne!(
        outer_name, inner_name,
        "rename_variables should allocate globally unique let names"
    );
    assert!(
        matches!(inner_body.as_ref(), PseudoExpr::Var { name, id } if name == &inner_name && *id == Some(inner_id)),
        "expected inner body ref to follow renamed inner let, got {inner_body:?}"
    );
}

#[test]
fn test_lambda_params() {
    let expr = PseudoExpr::Lambda {
        params: vec!["i".to_string().into(), "i".to_string().into()],
        body: PBox::new(PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Add,
            left: PBox::new(PseudoExpr::var("i")),
            right: PBox::new(PseudoExpr::var("i")),
        }),
    };

    let renamed = rename_variables(expr);

    if let PseudoExpr::Lambda { params, .. } = renamed {
        assert_eq!(params.len(), 2);
        // Params should have different names
        assert_ne!(params[0], params[1]);
    }
}

#[test]
fn test_recfn_params_preserve_original_hints_in_early_rename() {
    let fn_id = VarId::new(300);
    let acc_id = VarId::new(301);
    let list_id = VarId::new(302);
    let expr = PseudoExpr::RecFn {
        name: Binder::new("rec_fn_2", fn_id),
        params: vec![
            Binder::new("acc_33", acc_id),
            Binder::new("items_44", list_id),
        ],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("rec_fn_2", fn_id)),
            args: vec![
                PseudoExpr::var_with_id("acc_33", acc_id),
                PseudoExpr::var_with_id("items_44", list_id),
            ]
            .into(),
        }),
    };

    let renamed = rename_variables(expr);
    let rendered = renamed.to_pretty();

    assert!(
        rendered.contains("rec fn self_fn(acc_33, items_44)")
            && rendered.contains("self_fn(acc_33, items_44)"),
        "early rename should preserve original recursive param hints instead of forcing semantic list/acc guesses: {rendered}"
    );
}

#[test]
fn test_when_pair_pattern_binders_rename_clause_body_by_var_id() {
    let left_id = VarId::new(200);
    let right_id = VarId::new(201);

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("pair")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Pair(Binder::new("x", left_id), Binder::new("y", right_id)),
            PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("x", left_id),
                    PseudoExpr::var_with_id("y", right_id),
                ]
                .into(),
            ),
        )],
    };

    let renamed = rename_variables(expr);

    let PseudoExpr::When { clauses, .. } = renamed else {
        panic!("expected when expression");
    };
    let Some(WhenClause { pattern, body, .. }) = clauses.first() else {
        panic!("expected one clause");
    };
    let WhenPattern::Pair(left, right) = pattern else {
        panic!("expected pair pattern");
    };
    let PseudoExpr::Tuple(items) = body else {
        panic!("expected tuple body");
    };
    assert!(
        matches!(items.first(), Some(PseudoExpr::Var { name, id, .. }) if name == left.as_str() && id.get() == Some(left.id)),
        "expected first body var to follow renamed left binder, got: {:?}",
        items.first()
    );
    assert!(
        matches!(items.get(1), Some(PseudoExpr::Var { name, id, .. }) if name == right.as_str() && id.get() == Some(right.id)),
        "expected second body var to follow renamed right binder, got: {:?}",
        items.get(1)
    );
}

#[test]
fn test_when_subject_name_renames_clause_refs_by_var_id() {
    let subject_id = VarId::new(202);

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("payload")),
        subject_name: Some(Binder::new("payload", subject_id)),
        clauses: vec![WhenClause::new(
            WhenPattern::Wildcard,
            PseudoExpr::var_with_id("payload", subject_id),
        )],
    };

    let renamed = rename_variables(expr);

    let PseudoExpr::When {
        subject_name,
        clauses,
        ..
    } = renamed
    else {
        panic!("expected when expression");
    };
    let subject_name = subject_name.expect("expected renamed subject binder");
    let Some(WhenClause { body, .. }) = clauses.first() else {
        panic!("expected one clause");
    };
    assert!(
        matches!(body, PseudoExpr::Var { name, id, .. } if name == subject_name.as_str() && id.get() == Some(subject_name.id)),
        "expected clause body ref to follow renamed subject binder, got: {body:?}"
    );
}

#[test]
fn short_builtin_name_dot_free_for_dotted_builtins() {
    // Hash + Int.* canonical display names are dotted; the hint must be a
    // valid (dot-free) identifier stem.
    assert_eq!(Renamer::short_builtin_name("Hash.blake2b_256"), "blake2b");
    assert_eq!(Renamer::short_builtin_name("Hash.blake2b_224"), "blake2b");
    assert_eq!(Renamer::short_builtin_name("Hash.sha256"), "sha256");
    assert_eq!(Renamer::short_builtin_name("Hash.keccak_256"), "keccak");
    assert_eq!(Renamer::short_builtin_name("Hash.ripemd_160"), "ripemd");
    assert_eq!(Renamer::short_builtin_name("Int.quot"), "quot");
    assert_eq!(Renamer::short_builtin_name("Int.rem"), "rem");
    assert_eq!(Renamer::short_builtin_name("Int.lt"), "lt");
    // Un-prefixed raw names map via the same table.
    assert_eq!(Renamer::short_builtin_name("add_integer"), "add");
}

#[test]
fn short_builtin_name_lowercases_initial_for_value_binder() {
    // The dotted-builtin fallback (`name[..4]`) yields an uppercase stem, but
    // the result becomes a VALUE binder (`<stem>_partial`) and uppercase is
    // reserved for types/constructors — not `let Byte_partial`.
    assert_eq!(Renamer::short_builtin_name("ByteArray.length"), "byte");
    assert_eq!(Renamer::short_builtin_name("List.push"), "list");
    // Already-lowercase stems are unchanged.
    assert_eq!(Renamer::short_builtin_name("Int.lt"), "lt");
    assert_eq!(
        Renamer::short_builtin_name("verify_ed25519_signature"),
        "verify"
    );
}
