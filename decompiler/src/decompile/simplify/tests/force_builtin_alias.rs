use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_force_if_via_forced_builtin_alias_call() {
    let expr = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if_then_else"),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("a")))),
            args: vec![
                PseudoExpr::Bool(true),
                PseudoExpr::Delay(PBox::new(PseudoExpr::int(1))),
                PseudoExpr::Delay(PBox::new(PseudoExpr::int(2))),
            ]
            .into(),
        }))),
    };

    let simplified = simplify(expr);
    let dbg = format!("{simplified:?}");
    assert!(!dbg.contains("Force(Force("));
}

#[test]
fn test_force_if_then_else_var_call() {
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("if_then_else")),
        args: vec![
            PseudoExpr::Bool(true),
            PseudoExpr::Delay(PBox::new(PseudoExpr::int(1))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::int(2))),
        ]
        .into(),
    }));

    let simplified = simplify(expr);
    let dbg = format!("{simplified:?}");
    assert!(!dbg.contains("Force(Force("));
}

#[test]
fn test_force_choose_list_via_forced_builtin_alias_call() {
    let expr = PseudoExpr::Let {
        name: "h".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("choose_list"),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("h")))),
            args: vec![
                PseudoExpr::var("xs"),
                PseudoExpr::Delay(PBox::new(PseudoExpr::int(0))),
                PseudoExpr::Delay(PBox::new(PseudoExpr::int(1))),
            ]
            .into(),
        }))),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::When { .. } => {}
        PseudoExpr::Let { body, .. } => {
            assert!(matches!(body.as_ref(), PseudoExpr::When { .. }));
        }
        _ => panic!("expected when form"),
    }
}

#[test]
fn test_force_partial_if_via_forced_builtin_alias_call() {
    let expr = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if_then_else"),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "p".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("a")))),
                args: vec![PseudoExpr::var("c")].into(),
            }),
            body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("p")))),
                args: vec![
                    PseudoExpr::Delay(PBox::new(PseudoExpr::int(1))),
                    PseudoExpr::Delay(PBox::new(PseudoExpr::int(2))),
                ]
                .into(),
            }))),
        }),
    };

    let simplified = simplify(expr);
    let dbg = format!("{simplified:?}");
    assert!(!dbg.contains("Force(Force("));
}

#[test]
fn test_force_partial_choose_list_via_forced_builtin_alias_call() {
    let expr = PseudoExpr::Let {
        name: "h".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("choose_list"),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "p".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("h")))),
                args: vec![PseudoExpr::var("xs")].into(),
            }),
            body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("p")))),
                args: vec![
                    PseudoExpr::Delay(PBox::new(PseudoExpr::int(0))),
                    PseudoExpr::Delay(PBox::new(PseudoExpr::int(1))),
                ]
                .into(),
            }))),
        }),
    };

    let simplified = simplify(expr);
    assert!(matches!(simplified, PseudoExpr::When { .. }));
}

#[test]
fn test_force_inline_partial_if_via_forced_builtin_alias_call() {
    let expr = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if_then_else"),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("a")))),
                args: vec![PseudoExpr::var("c")].into(),
            }))),
            args: vec![
                PseudoExpr::Delay(PBox::new(PseudoExpr::int(1))),
                PseudoExpr::Delay(PBox::new(PseudoExpr::int(2))),
            ]
            .into(),
        }))),
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::If { .. } => {}
        PseudoExpr::Let { body, .. } => {
            assert!(matches!(body.as_ref(), PseudoExpr::If { .. }));
        }
        _ => panic!("expected if form"),
    }

    let dbg = format!("{simplified:?}");
    assert!(!dbg.contains("Force("));
}

#[test]
fn test_force_inline_partial_choose_list_via_forced_builtin_alias_call() {
    let expr = PseudoExpr::Let {
        name: "h".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("choose_list"),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("h")))),
                args: vec![PseudoExpr::var("xs")].into(),
            }))),
            args: vec![
                PseudoExpr::Delay(PBox::new(PseudoExpr::int(0))),
                PseudoExpr::Delay(PBox::new(PseudoExpr::int(1))),
            ]
            .into(),
        }))),
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When { .. } => {}
        PseudoExpr::Let { body, .. } => {
            assert!(matches!(body.as_ref(), PseudoExpr::When { .. }));
        }
        _ => panic!("expected when form"),
    }

    let dbg = format!("{simplified:?}");
    assert!(!dbg.contains("Force("));
}
