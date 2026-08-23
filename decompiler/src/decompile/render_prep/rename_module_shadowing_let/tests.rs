use super::*;
use crate::pseudo::ast::Binder;

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `const list = []; (fn(v) { list.map(v) })` — `list` shadows the module.
#[test]
fn renames_const_shadowing_used_module() {
    let list_id = VarId::new(1);
    let expr = PseudoExpr::Let {
        name: "list".to_string(),
        id: Some(list_id),
        value: PBox::new(PseudoExpr::List {
            elements: vec![].into(),
            tail: None,
        }),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("v", VarId::new(9))],
            body: PBox::new(PseudoExpr::Apply {
                // `list.map(v, list)` — qualifier head + a real use of the const.
                function: PBox::new(var("list.map", 0)),
                args: vec![var("v", 9), var("list", 1)].into(),
            }),
        }),
    };
    let out = rename_module_shadowing_lets(expr);
    let PseudoExpr::Let { name, body, .. } = out else {
        panic!("Let")
    };
    assert_eq!(name, "list_2", "const binder renamed");
    // The use of the const is rewired; the `list.map` qualifier is untouched.
    let PseudoExpr::Lambda { body, .. } = body.into_inner() else {
        panic!("Lambda")
    };
    let PseudoExpr::Apply { function, args } = body.into_inner() else {
        panic!("Apply")
    };
    assert!(matches!(*function, PseudoExpr::Var { ref name, .. } if name == "list.map"));
    assert!(matches!(&args[1], PseudoExpr::Var { name, .. } if name == "list_2"));
}

/// A value named `list` with NO `list.<fn>` qualifier in scope is left alone.
#[test]
fn keeps_const_when_module_not_used_as_qualifier() {
    let expr = PseudoExpr::Let {
        name: "list".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::List {
            elements: vec![].into(),
            tail: None,
        }),
        body: PBox::new(var("list", 1)),
    };
    let out = rename_module_shadowing_lets(expr.clone());
    assert_eq!(out, expr, "no qualifier in scope → no rename");
}

/// Fresh name must avoid a colliding `when`-pattern binder, not just lets.
#[test]
fn fresh_name_avoids_pattern_binder_collision() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    let list_id = VarId::new(1);
    // An inner clause binds `list_2`; renaming `const list` must skip to
    // `list_3` so the rewired const use does not capture the pattern binder.
    let expr = PseudoExpr::Let {
        name: "list".to_string(),
        id: Some(list_id),
        value: PBox::new(PseudoExpr::List {
            elements: vec![].into(),
            tail: None,
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("list.map", 0)), // qualifier → `used`
            args: vec![
                var("list", 1), // a real (id-tagged) use of the const
                PseudoExpr::When {
                    subject: PBox::new(var("z", 8)),
                    subject_name: None,
                    clauses: vec![WhenClause {
                        pattern: WhenPattern::Var(Binder::new("list_2", VarId::new(7))),
                        guard: None,
                        body: PseudoExpr::Unit,
                    }],
                },
            ]
            .into(),
        }),
    };
    let out = rename_module_shadowing_lets(expr);
    let PseudoExpr::Let { name, .. } = out else {
        panic!("Let")
    };
    assert_eq!(name, "list_3", "must skip the `list_2` pattern binder");
}

/// Fail-closed: if a ref to the const sits in a `WhenPattern::Literal` (which
/// the VarId rewrite cannot reach), skip the rename rather than strand it.
#[test]
fn skips_rename_when_ref_is_in_literal_pattern() {
    let list_id = VarId::new(1);
    let expr = PseudoExpr::Let {
        name: "list".to_string(),
        id: Some(list_id),
        value: PBox::new(PseudoExpr::List {
            elements: vec![].into(),
            tail: None,
        }),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("v", VarId::new(9))],
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(var("list.map", 0)), // qualifier present → `used`
                subject_name: None,
                clauses: vec![crate::pseudo::ast::WhenClause {
                    // a ref to the const, BURIED in a literal pattern
                    pattern: crate::pseudo::ast::WhenPattern::Literal(var("list", 1)),
                    guard: None,
                    body: PseudoExpr::Unit,
                }],
            }),
        }),
    };
    let out = rename_module_shadowing_lets(expr.clone());
    assert_eq!(
        out, expr,
        "must not rename when a ref hides in a literal pattern"
    );
}

/// A function param named like a module is NOT renamed (only `Let` bindings).
#[test]
fn keeps_param_named_like_module() {
    // fn(list) { list.map(list) } — here `list` is a PARAM, not a Let.
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("list", VarId::new(1))],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("list.map", 0)),
            args: vec![var("list", 1)].into(),
        }),
    };
    let out = rename_module_shadowing_lets(expr.clone());
    assert_eq!(out, expr, "params are not renamed by this pass");
}
