use super::*;
use crate::builtins::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

#[test]
fn list_head_argument_handles_direct_and_apply_forms() {
    let direct = PseudoExpr::builtin_id(BuiltinId::ListHead, vec![PseudoExpr::var("xs")]);
    let apply_builtin = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::builtin_id(BuiltinId::ListHead, vec![])),
        args: vec![PseudoExpr::var("ys")].into(),
    };
    let apply_var = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("List.head")),
        args: vec![PseudoExpr::var("zs")].into(),
    };

    assert!(
        matches!(list_head_argument(&direct), Some(PseudoExpr::Var { name, .. }) if name == "xs")
    );
    assert!(
        matches!(list_head_argument(&apply_builtin), Some(PseudoExpr::Var { name, .. }) if name == "ys")
    );
    assert!(
        matches!(list_head_argument(&apply_var), Some(PseudoExpr::Var { name, .. }) if name == "zs")
    );
}

#[test]
fn list_cons_parts_handles_builtin_apply_cons_operator_and_list_sugar() {
    let builtin = PseudoExpr::builtin_id(
        BuiltinId::ListCons,
        vec![PseudoExpr::var("head"), PseudoExpr::var("tail")],
    );
    let apply_builtin = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::builtin_id(BuiltinId::ListCons, vec![])),
        args: vec![PseudoExpr::var("head"), PseudoExpr::var("tail")].into(),
    };
    let binop = PseudoExpr::BinOp {
        op: crate::pseudo::ast::BinaryOp::Cons,
        left: PBox::new(PseudoExpr::var("head")),
        right: PBox::new(PseudoExpr::var("tail")),
    };
    let list_sugar = PseudoExpr::List {
        elements: vec![PseudoExpr::var("head")].into(),
        tail: Some(PBox::new(PseudoExpr::var("tail"))),
    };

    for expr in [&builtin, &apply_builtin, &binop, &list_sugar] {
        let Some((head, tail)) = list_cons_parts(expr) else {
            panic!("expected list cons parts");
        };
        assert!(matches!(head, PseudoExpr::Var { name, .. } if name == "head"));
        assert!(matches!(tail, PseudoExpr::Var { name, .. } if name == "tail"));
    }
}

#[test]
fn list_literal_parts_flattens_closed_spreads_and_constr_chains() {
    let spread = PseudoExpr::List {
        elements: vec![PseudoExpr::var("a")].into(),
        tail: Some(PBox::new(PseudoExpr::builtin_id(
            BuiltinId::ListCons,
            vec![
                PseudoExpr::var("b"),
                PseudoExpr::List {
                    elements: vec![].into(),
                    tail: None,
                },
            ],
        ))),
    };
    let constr_chain = PseudoExpr::constr(
        ConstructorShape::unknown_data(1, 2),
        vec![
            PseudoExpr::var("x"),
            PseudoExpr::constr(
                ConstructorShape::unknown_data(1, 2),
                vec![
                    PseudoExpr::var("y"),
                    PseudoExpr::constr(ConstructorShape::unknown_data(0, 0), vec![]),
                ],
            ),
        ],
    );

    let (spread_elements, spread_tail) =
        list_literal_parts(&spread).expect("spread form should be recognized");
    let (constr_elements, constr_tail) =
        list_literal_parts(&constr_chain).expect("constr chain should be recognized");

    assert!(spread_tail.is_none());
    assert!(constr_tail.is_none());
    assert_eq!(spread_elements.len(), 2);
    assert_eq!(constr_elements.len(), 2);
    assert!(matches!(&spread_elements[0], PseudoExpr::Var { name, .. } if name == "a"));
    assert!(matches!(&spread_elements[1], PseudoExpr::Var { name, .. } if name == "b"));
    assert!(matches!(&constr_elements[0], PseudoExpr::Var { name, .. } if name == "x"));
    assert!(matches!(&constr_elements[1], PseudoExpr::Var { name, .. } if name == "y"));
}

#[test]
fn list_subject_and_tail_depth_handles_direct_and_apply_tail_forms() {
    let direct_single = PseudoExpr::builtin_id(BuiltinId::ListTail, vec![PseudoExpr::var("xs")]);
    let direct = PseudoExpr::builtin_id(
        BuiltinId::ListTail,
        vec![PseudoExpr::builtin_id(
            BuiltinId::ListTail,
            vec![PseudoExpr::var("xs")],
        )],
    );
    let apply = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::builtin_id(BuiltinId::ListTail, vec![])),
        args: vec![PseudoExpr::var("xs")].into(),
    };
    let apply_var = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("List.tail")),
        args: vec![PseudoExpr::var("ys")].into(),
    };

    let (direct_subject, direct_depth) = list_subject_and_tail_depth(&direct);
    let (apply_subject, apply_depth) = list_subject_and_tail_depth(&apply);
    let (apply_var_subject, apply_var_depth) = list_subject_and_tail_depth(&apply_var);

    assert_eq!(direct_depth, 2);
    assert_eq!(apply_depth, 1);
    assert_eq!(apply_var_depth, 1);
    assert!(matches!(direct_subject, PseudoExpr::Var { name, .. } if name == "xs"));
    assert!(matches!(apply_subject, PseudoExpr::Var { name, .. } if name == "xs"));
    assert!(matches!(apply_var_subject, PseudoExpr::Var { name, .. } if name == "ys"));
    assert!(is_list_tail_call(&direct_single));
    assert!(is_list_tail_call(&direct));
    assert!(is_list_tail_call(&apply));
    assert!(is_list_tail_call(&apply_var));
    assert!(is_list_tail_of_var(&apply_var, "ys"));
    assert!(is_list_tail_of_var(&direct_single, "xs"));
    assert!(!is_list_tail_of_var(&apply_var, "xs"));
}

#[test]
fn list_subject_and_tail_depth_owned_moves_subject_and_preserves_id() {
    let xs_id = VarId::from_raw(9970);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::builtin_id(BuiltinId::ListTail, vec![])),
        args: vec![PseudoExpr::builtin_id(
            BuiltinId::ListTail,
            vec![PseudoExpr::var_with_id("xs", xs_id)],
        )]
        .into(),
    };

    let (subject, depth) = list_subject_and_tail_depth_owned(expr);

    assert_eq!(depth, 2);
    assert!(
        matches!(subject, PseudoExpr::Var { name, id } if name == "xs" && id == Some(xs_id)),
        "owned tail traversal should move the final subject with id intact"
    );
}
