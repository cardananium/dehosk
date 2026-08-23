use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_data_constr_fields_folding() {
    // let t = Data.Constr(0, [a, b]) in t.fields -> [a, b]
    // The Data.Constr.fields access should be folded away, eliminating t via DCE.
    let expr = PseudoExpr::Let {
        name: "t".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.Constr"),
            args: vec![
                PseudoExpr::Int(0.into()),
                PseudoExpr::List {
                    elements: vec![PseudoExpr::var("a"), PseudoExpr::var("b")].into(),
                    tail: None,
                },
            ]
            .into(),
        }),
        body: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("t"),
            "fields".to_string(),
        )),
    };

    let simplified = simplify(expr);
    // Should fold to just the list [a, b], with the let eliminated by DCE
    assert!(
        matches!(simplified, PseudoExpr::List { ref elements, tail: None } if elements.len() == 2),
        "expected [a, b] list, got: {:?}",
        simplified
    );
}

#[test]
fn test_data_constr_tag_folding() {
    // let t = Data.Constr(0, [a]) in t.tag -> 0
    let expr = PseudoExpr::Let {
        name: "t".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.Constr"),
            args: vec![
                PseudoExpr::Int(0.into()),
                PseudoExpr::List {
                    elements: vec![PseudoExpr::var("a")].into(),
                    tail: None,
                },
            ]
            .into(),
        }),
        body: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("t"),
            "tag".to_string(),
        )),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Int(ref n) if *n == 0.into()),
        "expected Int(0), got: {:?}",
        simplified
    );
}

#[test]
fn test_data_constr_fields_folding_through_let() {
    // let t = (let x = val in Data.Constr(0, [x])) in t.fields
    // Should fold through the Let wrapper
    let expr = PseudoExpr::Let {
        name: "t".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::var("val")),
            body: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.Constr"),
                args: vec![
                    PseudoExpr::Int(0.into()),
                    PseudoExpr::List {
                        elements: vec![PseudoExpr::var("x")].into(),
                        tail: None,
                    },
                ]
                .into(),
            }),
        }),
        body: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("t"),
            "fields".to_string(),
        )),
    };

    let simplified = simplify(expr);
    // Should fold to: let x = val in [x]
    // The outer 't' let is DCE'd, inner 'x' remains because it's used in the list
    match simplified {
        PseudoExpr::Let { name, body, .. } => {
            assert_eq!(name, "x");
            assert!(
                matches!(*body, PseudoExpr::List { ref elements, tail: None } if elements.len() == 1),
                "expected list body, got: {:?}",
                body
            );
        }
        // x might get aliased away if val is a simple var
        PseudoExpr::List {
            ref elements,
            tail: None,
        } if elements.len() == 1 => {
            // This is also acceptable - if x was inlined
        }
        _ => panic!(
            "expected let x = val in [x] or [val], got: {:?}",
            simplified
        ),
    }
}
