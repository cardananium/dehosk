use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_tail_chain_expression_collapse() {
    // List.tail(List.tail(x))[0] → x[2]
    let inner_tail = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![PseudoExpr::var("x")].into(),
    };
    let outer_tail = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![inner_tail].into(),
    };
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(outer_tail),
        index: 0,
    };
    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::IndexAccess { collection, index } => {
            assert_eq!(*index, 2);
            assert!(
                matches!(collection.as_ref(), PseudoExpr::Var { name, .. } if name == "x"),
                "expected Var(x), got: {:?}",
                collection
            );
        }
        _ => panic!("expected IndexAccess, got: {:?}", simplified),
    }
}

#[test]
fn test_tail_chain_expression_collapse_with_offset() {
    // List.tail(List.tail(List.tail(x)))[1] → x[4]
    let tail1 = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![PseudoExpr::var("x")].into(),
    };
    let tail2 = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![tail1].into(),
    };
    let tail3 = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![tail2].into(),
    };
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(tail3),
        index: 1,
    };
    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::IndexAccess { collection, index } => {
            assert_eq!(*index, 4);
            assert!(
                matches!(collection.as_ref(), PseudoExpr::Var { name, .. } if name == "x"),
                "expected Var(x), got: {:?}",
                collection
            );
        }
        _ => panic!("expected IndexAccess, got: {:?}", simplified),
    }
}

#[test]
fn test_tail_chain_expression_collapse_apply_form() {
    // Apply(BuiltinCall("List.tail", []), [Apply(BuiltinCall("List.tail", []), [x])])[0] → x[2]
    let inner_tail = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("List.tail"),
            args: vec![].into(),
        }),
        args: vec![PseudoExpr::var("x")].into(),
    };
    let outer_tail = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("List.tail"),
            args: vec![].into(),
        }),
        args: vec![inner_tail].into(),
    };
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(outer_tail),
        index: 0,
    };
    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::IndexAccess { collection, index } => {
            assert_eq!(*index, 2);
            assert!(
                matches!(collection.as_ref(), PseudoExpr::Var { name, .. } if name == "x"),
                "expected Var(x), got: {:?}",
                collection
            );
        }
        _ => panic!("expected IndexAccess, got: {:?}", simplified),
    }
}

#[test]
fn test_tail_chain_through_let_binding() {
    // let l1 = List.tail(b1) in List.tail(List.tail(List.tail(l1)))[0]
    // Should collapse to b1[4] (1 from let + 3 from expression + 0 from index)
    let tail_b1 = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![PseudoExpr::var("b1")].into(),
    };
    let tail_l1 = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![PseudoExpr::var("l1")].into(),
    };
    let tail_tail_l1 = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![tail_l1].into(),
    };
    let tail_tail_tail_l1 = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![tail_tail_l1].into(),
    };
    let index_access = PseudoExpr::IndexAccess {
        collection: PBox::new(tail_tail_tail_l1),
        index: 0,
    };
    let let_expr = PseudoExpr::Let {
        name: "l1".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(tail_b1),
        body: PBox::new(index_access),
    };
    let simplified = simplify(let_expr);
    // Should produce b1[4] — dead code eliminates the let since l1 is fully resolved
    match &simplified {
        PseudoExpr::IndexAccess { collection, index } => {
            assert_eq!(*index, 4, "expected index 4, got {}", index);
            assert!(
                matches!(collection.as_ref(), PseudoExpr::Var { name, .. } if name == "b1"),
                "expected Var(b1), got: {:?}",
                collection
            );
        }
        _ => panic!("expected IndexAccess, got: {:?}", simplified),
    }
}

#[test]
fn test_tail_chain_in_builtin_arg() {
    // Data.to_map(let l1 = List.tail(b1) in List.tail(List.tail(List.tail(l1)))[0])
    // Should collapse inner to b1[4]
    let tail_b1 = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![PseudoExpr::var("b1")].into(),
    };
    let tail_l1 = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![PseudoExpr::var("l1")].into(),
    };
    let tail_tail_l1 = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![tail_l1].into(),
    };
    let tail_tail_tail_l1 = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![tail_tail_l1].into(),
    };
    let index_access = PseudoExpr::IndexAccess {
        collection: PBox::new(tail_tail_tail_l1),
        index: 0,
    };
    let let_expr = PseudoExpr::Let {
        name: "l1".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(tail_b1),
        body: PBox::new(index_access),
    };
    let data_to_map = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.to_map"),
        args: vec![let_expr].into(),
    };
    let simplified = simplify(data_to_map);
    // Should be Data.to_map(b1[4])
    match &simplified {
        PseudoExpr::BuiltinCall { name, args } => {
            assert_eq!(name, "Data.to_map");
            assert_eq!(args.len(), 1);
            match &args[0] {
                PseudoExpr::IndexAccess { collection, index } => {
                    assert_eq!(*index, 4, "expected index 4, got {}", index);
                    assert!(
                        matches!(collection.as_ref(), PseudoExpr::Var { name, .. } if name == "b1"),
                        "expected Var(b1), got: {:?}",
                        collection
                    );
                }
                _ => panic!(
                    "expected IndexAccess inside Data.to_map, got: {:?}",
                    args[0]
                ),
            }
        }
        _ => panic!("expected BuiltinCall, got: {:?}", simplified),
    }
}

#[test]
fn test_tail_chain_in_apply_form_through_let() {
    // Same as above but using Apply(BuiltinCall("List.tail",[]),[arg]) form
    // Data.to_map(let l1 = Apply(List.tail,[b1]) in Apply(List.tail,[Apply(List.tail,[Apply(List.tail,[l1])])])[0])
    let mk_tail_apply = |arg: PseudoExpr| PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("List.tail"),
            args: vec![].into(),
        }),
        args: vec![arg].into(),
    };
    let tail_b1 = mk_tail_apply(PseudoExpr::var("b1"));
    let tail_l1 = mk_tail_apply(PseudoExpr::var("l1"));
    let tail_tail_l1 = mk_tail_apply(tail_l1);
    let tail_tail_tail_l1 = mk_tail_apply(tail_tail_l1);
    let index_access = PseudoExpr::IndexAccess {
        collection: PBox::new(tail_tail_tail_l1),
        index: 0,
    };
    let let_expr = PseudoExpr::Let {
        name: "l1".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(tail_b1),
        body: PBox::new(index_access),
    };
    let data_to_map = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.to_map"),
        args: vec![let_expr].into(),
    };
    let simplified = simplify(data_to_map);
    // Should be Data.to_map(b1[4])
    match &simplified {
        PseudoExpr::BuiltinCall { name, args } => {
            assert_eq!(name, "Data.to_map");
            assert_eq!(args.len(), 1);
            match &args[0] {
                PseudoExpr::IndexAccess { collection, index } => {
                    assert_eq!(*index, 4, "expected index 4, got {}", index);
                    assert!(
                        matches!(collection.as_ref(), PseudoExpr::Var { name, .. } if name == "b1"),
                        "expected Var(b1), got: {:?}",
                        collection
                    );
                }
                _ => panic!(
                    "expected IndexAccess inside Data.to_map, got: {:?}",
                    args[0]
                ),
            }
        }
        _ => panic!("expected BuiltinCall, got: {:?}", simplified),
    }
}

#[test]
fn test_index_access_floated_into_let_body() {
    // IndexAccess { collection: Let("l1", List.tail(b1), List.tail(List.tail(List.tail(l1)))), index: 0 }
    // Floating the IndexAccess into the Let body gives Let("l1", ..., body[0]);
    // tail_chain_offsets then resolves l1 → (b1, 1), depth=3 → b1[4].
    let tail_b1 = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![PseudoExpr::var("b1")].into(),
    };
    let tail_l1 = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![PseudoExpr::var("l1")].into(),
    };
    let tail_tail_l1 = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![tail_l1].into(),
    };
    let tail_tail_tail_l1 = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.tail"),
        args: vec![tail_tail_l1].into(),
    };
    // Key: the Let is the *collection* of IndexAccess, not wrapping it
    let let_collection = PseudoExpr::Let {
        name: "l1".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(tail_b1),
        body: PBox::new(tail_tail_tail_l1),
    };
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(let_collection),
        index: 0,
    };
    let simplified = simplify(expr);
    // Should produce b1[4]
    match &simplified {
        PseudoExpr::IndexAccess { collection, index } => {
            assert_eq!(*index, 4, "expected index 4, got {}", index);
            assert!(
                matches!(collection.as_ref(), PseudoExpr::Var { name, .. } if name == "b1"),
                "expected Var(b1), got: {:?}",
                collection
            );
        }
        _ => panic!("expected IndexAccess, got: {:?}", simplified),
    }
}

#[test]
fn test_index_access_let_collection_no_tail_chain() {
    // IndexAccess { collection: Let("x", 42, Var("x")), index: 3 }
    // Floats to Let("x", 42, Var("x")[3]); x is used once and is simple,
    // so it inlines to 42[3]. 42 is an Int, not a collection — the
    // simplifier must not crash on it.
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::int(42)),
            body: PBox::new(PseudoExpr::var("x")),
        }),
        index: 3,
    };
    let simplified = simplify(expr);
    // 42 is not a Var, so no aliasing and the Let stays; x is used once
    // and is simple, so it inlines to IndexAccess(42, 3).
    match &simplified {
        PseudoExpr::IndexAccess { collection, index } => {
            assert_eq!(*index, 3);
            assert!(
                matches!(collection.as_ref(), PseudoExpr::Int(n) if *n == 42.into()),
                "expected Int(42), got: {:?}",
                collection
            );
        }
        _ => panic!("expected IndexAccess, got: {:?}", simplified),
    }
}
