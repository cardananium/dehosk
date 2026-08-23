use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn flattens_list_cons_into_literal() {
    let input = PseudoExpr::BuiltinCall {
        name: BuiltinId::expect_known("List.cons"),
        args: vec![
            PseudoExpr::int(1),
            PseudoExpr::List {
                elements: vec![].into(),
                tail: None,
            },
        ]
        .into(),
    };
    let out = normalize_list_cons_literals(input);
    assert!(
        matches!(
            out,
            PseudoExpr::List { ref elements, tail: None } if elements.len() == 1
        ),
        "List.cons(1, []) should become [1], got: {out:?}"
    );
}

#[test]
fn flattens_curried_list_prepend_into_literal() {
    let input = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: BuiltinId::expect_known("List.prepend"),
            args: vec![].into(),
        }),
        args: vec![
            PseudoExpr::int(1),
            PseudoExpr::List {
                elements: vec![PseudoExpr::int(2)].into(),
                tail: None,
            },
        ]
        .into(),
    };
    let out = normalize_list_cons_literals(input);
    assert!(
        matches!(
            out,
            PseudoExpr::List { ref elements, tail: None } if elements.len() == 2
        ),
        "List.prepend()(1, [2]) should become [1, 2], got: {out:?}"
    );
}

#[test]
fn identity_when_no_list_cons_marker() {
    let input = PseudoExpr::int(42);
    assert_eq!(normalize_list_cons_literals(input.clone()), input);
}
