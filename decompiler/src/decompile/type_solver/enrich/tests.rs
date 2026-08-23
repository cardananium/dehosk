use super::super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, PseudoType};
use crate::pseudo::var_id::VarId;
use std::rc::Rc;

#[test]
fn slice_c_refines_ret_to_int_for_literal_int_body() {
    // `let f = fn(x) { 42 } in f`
    // Baseline: Function([Unknown], Unknown).
    let f_id = VarId::new(2400);
    let x_id = VarId::new(2401);
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::int(42)),
        }),
        body: PBox::new(PseudoExpr::var_with_id("f", f_id)),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);
    let ty = table.type_of_var(f_id).expect("f_id must be in the table");

    match ty.as_ref() {
        PseudoType::Function { params, ret } => {
            assert_eq!(params.len(), 1);
            assert!(
                matches!(ret.as_ref(), PseudoType::Int),
                "ret must be refined to Int from the literal body, got {:?}",
                ret
            );
        }
        other => panic!("expected Function, got {other:?}"),
    }
}

#[test]
fn slice_c_refines_ret_to_bool_for_literal_bool_body() {
    let f_id = VarId::new(2410);
    let x_id = VarId::new(2411);
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::bool(true)),
        }),
        body: PBox::new(PseudoExpr::var_with_id("f", f_id)),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);
    let ty = table.type_of_var(f_id).unwrap();
    let PseudoType::Function { ret, .. } = ty.as_ref() else {
        panic!("expected Function");
    };
    assert!(matches!(ret.as_ref(), PseudoType::Bool));
}

#[test]
fn slice_c_keeps_ret_unknown_for_unrecognized_body_shape() {
    // The callee `opaque` has no type, so the Apply body derives nothing.
    let f_id = VarId::new(2420);
    let x_id = VarId::new(2421);
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("opaque")),
                args: vec![PseudoExpr::var_with_id("x", x_id)].into(),
            }),
        }),
        body: PBox::new(PseudoExpr::var_with_id("f", f_id)),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);
    let ty = table.type_of_var(f_id).unwrap();
    let PseudoType::Function { ret, .. } = ty.as_ref() else {
        panic!("expected Function");
    };
    assert!(
        matches!(ret.as_ref(), PseudoType::Unknown),
        "Apply body is out of Slice C scope, ret must remain Unknown, got {:?}",
        ret
    );
}

#[test]
fn slice_c_post_order_refines_outer_function_from_inner_let_lambda() {
    // `let f = fn(x) { let g = fn(y) { 0 } in g } in f`
    // Pre-order would record `f: fn(_) -> fn(_) -> _` because `g`
    // is still unrefined when f's body is derived; post-order
    // refines g first, so f's ret is `Function([Unknown], Int)`.
    let f_id = VarId::new(2500);
    let x_id = VarId::new(2501);
    let g_id = VarId::new(2502);
    let y_id = VarId::new(2503);
    let inner_let = PseudoExpr::Let {
        name: "g".to_string(),
        id: Some(g_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("y", y_id)],
            body: PBox::new(PseudoExpr::int(0)),
        }),
        body: PBox::new(PseudoExpr::var_with_id("g", g_id)),
    };
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(inner_let),
        }),
        body: PBox::new(PseudoExpr::var_with_id("f", f_id)),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);
    let f_ty = table.type_of_var(f_id).unwrap();
    let PseudoType::Function { ret: f_ret, .. } = f_ty.as_ref() else {
        panic!("expected f to be Function");
    };
    let PseudoType::Function { ret: g_ret, .. } = f_ret.as_ref() else {
        panic!(
            "expected f.ret to be Function (the inner Lambda's type), got {:?}",
            f_ret
        );
    };
    assert!(
        matches!(g_ret.as_ref(), PseudoType::Int),
        "post-order must have refined inner g before deriving f.ret, expected Int got {:?}",
        g_ret
    );
}

#[test]
fn slice_c_refines_ret_from_binop_eq_to_bool() {
    // `let cmp = fn(x) { x == 0 } in cmp`
    use crate::pseudo::ast::BinaryOp;
    let f_id = VarId::new(2510);
    let x_id = VarId::new(2511);
    let expr = PseudoExpr::Let {
        name: "cmp".to_string(),
        id: Some(f_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::var_with_id("x", x_id)),
                right: PBox::new(PseudoExpr::int(0)),
            }),
        }),
        body: PBox::new(PseudoExpr::var_with_id("cmp", f_id)),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);
    let ty = table.type_of_var(f_id).unwrap();
    let PseudoType::Function { ret, .. } = ty.as_ref() else {
        panic!("expected Function");
    };
    assert!(
        matches!(ret.as_ref(), PseudoType::Bool),
        "BinOp::Eq body → ret should be Bool, got {:?}",
        ret
    );
}

#[test]
fn slice_c_refines_ret_from_unop_not_to_bool() {
    // `let neg = fn(x) { not(x) } in neg` → ret = Bool.
    use crate::pseudo::ast::UnaryOp;
    let f_id = VarId::new(2520);
    let x_id = VarId::new(2521);
    let expr = PseudoExpr::Let {
        name: "neg".to_string(),
        id: Some(f_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::UnOp {
                op: UnaryOp::Not,
                operand: PBox::new(PseudoExpr::var_with_id("x", x_id)),
            }),
        }),
        body: PBox::new(PseudoExpr::var_with_id("neg", f_id)),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);
    let ty = table.type_of_var(f_id).unwrap();
    let PseudoType::Function { ret, .. } = ty.as_ref() else {
        panic!("expected Function");
    };
    assert!(
        matches!(ret.as_ref(), PseudoType::Bool),
        "UnOp::Not body → ret should be Bool, got {:?}",
        ret
    );
}

#[test]
fn slice_c_refines_param_from_param_id_evidence() {
    // `let f = fn(x) { not(x) } in f`: Not constrains `x` to Bool,
    // and params[0] is harvested from the param VarId's entry.
    use crate::pseudo::ast::UnaryOp;
    let f_id = VarId::new(2430);
    let x_id = VarId::new(2431);
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::UnOp {
                op: UnaryOp::Not,
                operand: PBox::new(PseudoExpr::var_with_id("x", x_id)),
            }),
        }),
        body: PBox::new(PseudoExpr::var_with_id("f", f_id)),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);
    assert!(
        matches!(table.type_of_var(x_id).as_deref(), Some(PseudoType::Bool)),
        "x_id should be Bool from Not, got {:?}",
        table.type_of_var(x_id)
    );

    let ty = table.type_of_var(f_id).unwrap();
    let PseudoType::Function { params, ret } = ty.as_ref() else {
        panic!("expected Function");
    };
    assert!(
        matches!(params[0].as_ref(), PseudoType::Bool),
        "params[0] must be refined to Bool from x_id evidence, got {:?}",
        params[0]
    );
    let _ = ret; // ret is derived Bool from `not`, but not asserted here
}

// ────────────────────────────────────────────────────────────
// Apply chain propagation tests.
//

#[test]
fn slice_cplus_apply_full_consumes_args_returns_ret() {
    // `let id = fn(x) { x } in let r = fn(y) { id(0) } in r`
    // Expected: id is Function([Int], Int), r is
    // Function([Unknown], Int).
    let id_id = VarId::new(2600);
    let x_id = VarId::new(2601);
    let r_id = VarId::new(2602);
    let y_id = VarId::new(2603);
    let id_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
    };
    let r_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("y", y_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("id", id_id)),
            args: vec![PseudoExpr::int(0)].into(),
        }),
    };
    let expr = PseudoExpr::Let {
        name: "id".into(),
        id: Some(id_id),
        value: PBox::new(id_lambda),
        body: PBox::new(PseudoExpr::Let {
            name: "r".into(),
            id: Some(r_id),
            value: PBox::new(r_lambda),
            body: PBox::new(PseudoExpr::var_with_id("r", r_id)),
        }),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);

    // The call site `id(0)` refines id.params[0] to Int; the
    // next iteration derives id's body under an overlay
    // {x_id → Int}, so `Var(x_id)` resolves to Int without
    // mutating the global table, and id.ret refines to Int.
    let id_ty = table.type_of_var(id_id).unwrap();
    let PseudoType::Function {
        params: id_params,
        ret: id_ret,
    } = id_ty.as_ref()
    else {
        panic!("expected id to be Function");
    };
    assert!(
        matches!(id_params[0].as_ref(), PseudoType::Int),
        "id's params[0] must be refined to Int from call-site `id(0)`, got {:?}",
        id_params[0]
    );
    assert!(
        matches!(id_ret.as_ref(), PseudoType::Int),
        "id's ret must refine to Int via param overlay, got {:?}",
        id_ret
    );

    // The Apply consumes id's only param, so r.ret = Int.
    let r_ty = table.type_of_var(r_id).unwrap();
    let PseudoType::Function {
        params: r_params,
        ret: r_ret,
    } = r_ty.as_ref()
    else {
        panic!("expected r to be Function");
    };
    assert_eq!(r_params.len(), 1, "r preserves its single y param");
    assert!(
        matches!(r_ret.as_ref(), PseudoType::Int),
        "r.ret must propagate from id.ret via Apply forward, got {:?}",
        r_ret
    );
}

#[test]
fn slice_cplus_apply_partial_returns_residual_function() {
    // `let add = fn(a, b) { a + b } in let add3 = fn() { add(3) } in add3`
    // add is Function([Int, Int], Int); `add(3)` consumes one param, so
    // add3's body type is the residual Function([Int], Int).
    use crate::pseudo::ast::BinaryOp;
    let add_id = VarId::new(2610);
    let a_id = VarId::new(2611);
    let b_id = VarId::new(2612);
    let add3_id = VarId::new(2613);
    let add_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("a", a_id), Binder::new("b", b_id)],
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::var_with_id("a", a_id)),
            right: PBox::new(PseudoExpr::var_with_id("b", b_id)),
        }),
    };
    let add3_lambda = PseudoExpr::Lambda {
        params: vec![],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("add", add_id)),
            args: vec![PseudoExpr::int(3)].into(),
        }),
    };
    let expr = PseudoExpr::Let {
        name: "add".into(),
        id: Some(add_id),
        value: PBox::new(add_lambda),
        body: PBox::new(PseudoExpr::Let {
            name: "add3".into(),
            id: Some(add3_id),
            value: PBox::new(add3_lambda),
            body: PBox::new(PseudoExpr::var_with_id("add3", add3_id)),
        }),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);

    // add's ret comes from BinOp::Add → Int.
    let add_ty = table.type_of_var(add_id).unwrap();
    let PseudoType::Function {
        params: add_params,
        ret: add_ret,
    } = add_ty.as_ref()
    else {
        panic!("expected add to be Function");
    };
    assert!(matches!(add_ret.as_ref(), PseudoType::Int));
    assert!(
        matches!(add_params[0].as_ref(), PseudoType::Int),
        "params[0] must be refined from call site `add(3)`, got {:?}",
        add_params[0]
    );

    // add3's body is the Apply, so derive_body_type returns the
    // residual Function([params[1]], ret).
    let add3_ty = table.type_of_var(add3_id).unwrap();
    let PseudoType::Function { ret: add3_ret, .. } = add3_ty.as_ref() else {
        panic!("expected add3 to be Function");
    };
    let PseudoType::Function {
        params: residual_params,
        ret: residual_ret,
    } = add3_ret.as_ref()
    else {
        panic!(
            "expected add3.ret to be partial Function after add(3), got {:?}",
            add3_ret
        );
    };
    assert_eq!(
        residual_params.len(),
        1,
        "residual must have 1 unconsumed param"
    );
    assert!(matches!(residual_ret.as_ref(), PseudoType::Int));
}

#[test]
fn slice_cplus_apply_call_site_refines_param_slot() {
    // `let f = fn(x) { 0 } in f(42)`, inside an outer Lambda: the
    // call site refines params[0] though f's body ignores `x`.
    let f_id = VarId::new(2620);
    let x_id = VarId::new(2621);
    let g_id = VarId::new(2622);
    let z_id = VarId::new(2623);
    let f_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::int(0)),
    };
    let g_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("z", z_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("f", f_id)),
            args: vec![PseudoExpr::int(42)].into(),
        }),
    };
    let expr = PseudoExpr::Let {
        name: "f".into(),
        id: Some(f_id),
        value: PBox::new(f_lambda),
        body: PBox::new(PseudoExpr::Let {
            name: "g".into(),
            id: Some(g_id),
            value: PBox::new(g_lambda),
            body: PBox::new(PseudoExpr::var_with_id("g", g_id)),
        }),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);

    let f_ty = table.type_of_var(f_id).unwrap();
    let PseudoType::Function { params, .. } = f_ty.as_ref() else {
        panic!("expected Function");
    };
    assert!(
        matches!(params[0].as_ref(), PseudoType::Int),
        "call-site `f(42)` must refine f.params[0] to Int, got {:?}",
        params[0]
    );
}

#[test]
fn slice_cplus_apply_curried_chain_flattens_to_terminal_target() {
    // `let f = fn(a, b) { a + b } in Apply(Apply(f, [1]), [2])`
    // Curried — the chain flattens to (f, [1, 2]).
    use crate::pseudo::ast::BinaryOp;
    let f_id = VarId::new(2630);
    let a_id = VarId::new(2631);
    let b_id = VarId::new(2632);
    let f_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("a", a_id), Binder::new("b", b_id)],
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::var_with_id("a", a_id)),
            right: PBox::new(PseudoExpr::var_with_id("b", b_id)),
        }),
    };
    let curried_apply = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("f", f_id)),
            args: vec![PseudoExpr::int(1)].into(),
        }),
        args: vec![PseudoExpr::int(2)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "f".into(),
        id: Some(f_id),
        value: PBox::new(f_lambda),
        body: PBox::new(curried_apply),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);

    let f_ty = table.type_of_var(f_id).unwrap();
    let PseudoType::Function { params, .. } = f_ty.as_ref() else {
        panic!("expected Function");
    };
    assert!(
        matches!(params[0].as_ref(), PseudoType::Int),
        "curried call must refine params[0] to Int, got {:?}",
        params[0]
    );
    assert!(
        matches!(params[1].as_ref(), PseudoType::Int),
        "curried call must refine params[1] to Int, got {:?}",
        params[1]
    );
}

#[test]
fn slice_cplus_overlay_does_not_leak_across_lambda_boundaries() {
    // Overlay-locality invariant: `f`'s overlay {x_f → Int} is used
    // only while deriving f's body. `g` has a distinct `x` VarId and
    // an opaque body, so nothing from f's overlay may reach it.
    let f_id = VarId::new(2670);
    let x_f = VarId::new(2671);
    let g_id = VarId::new(2672);
    let x_g = VarId::new(2673);

    let expr = PseudoExpr::Let {
        name: "f".into(),
        id: Some(f_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_f)],
            body: PBox::new(PseudoExpr::var_with_id("x", x_f)),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "g".into(),
            id: Some(g_id),
            value: PBox::new(PseudoExpr::Lambda {
                params: vec![Binder::new("x", x_g)],
                body: PBox::new(PseudoExpr::var("opaque_outer")),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("f", f_id)),
                args: vec![PseudoExpr::int(0)].into(),
            }),
        }),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);

    // f.ret = Int via overlay through f's body's Var(x_f).
    let f_ty = table.type_of_var(f_id).unwrap();
    let PseudoType::Function { ret: f_ret, .. } = f_ty.as_ref() else {
        panic!("expected f Function");
    };
    assert!(matches!(f_ret.as_ref(), PseudoType::Int));

    // g is never called, so its params and ret stay Unknown.
    let g_ty = table.type_of_var(g_id).unwrap();
    let PseudoType::Function {
        params: g_params,
        ret: g_ret,
    } = g_ty.as_ref()
    else {
        panic!("expected g Function");
    };
    assert!(
        matches!(g_params[0].as_ref(), PseudoType::Unknown),
        "g.params[0] must stay Unknown (no overlay leak from f), got {:?}",
        g_params[0]
    );
    assert!(matches!(g_ret.as_ref(), PseudoType::Unknown));
}

#[test]
fn slice_cplus_merge_refines_list_inner_from_unknown_to_concrete() {
    // `merge_more_concrete` recurses through wrapper types:
    // `List<Unknown> ⊓ List<Int> → List<Int>`, so the call-site
    // arg refines the param's inner type, not just its shape.
    let f_id = VarId::new(2650);
    let x_id = VarId::new(2651);
    let f_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
    };
    // Call site: `f([1, 2])` — a List<Int> arg.
    let call_site = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("f", f_id)),
        args: vec![PseudoExpr::List {
            elements: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
            tail: None,
        }]
        .into(),
    };
    let expr = PseudoExpr::Let {
        name: "f".into(),
        id: Some(f_id),
        value: PBox::new(f_lambda),
        body: PBox::new(call_site),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);
    let f_ty = table.type_of_var(f_id).unwrap();
    let PseudoType::Function { params, .. } = f_ty.as_ref() else {
        panic!("expected Function");
    };
    let PseudoType::List(inner) = params[0].as_ref() else {
        panic!("expected params[0] to be List<...>, got {:?}", params[0]);
    };
    assert!(
        matches!(inner.as_ref(), PseudoType::Int),
        "List inner must refine to Int through wrapper recursion, got {:?}",
        inner
    );
}

#[test]
fn slice_cplus_fixed_point_terminates_on_no_refinement() {
    // `Unknown ⊓ Unknown` must not count as a change, so a script
    // with no refinable evidence — only opaque Vars — converges
    // instead of running to the iteration cap.
    let f_id = VarId::new(2660);
    let x_id = VarId::new(2661);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::var("opaque")),
    };
    let expr = PseudoExpr::Let {
        name: "f".into(),
        id: Some(f_id),
        value: PBox::new(lambda),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("f", f_id)),
            args: vec![PseudoExpr::var("opaque_arg")].into(),
        }),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);
    let f_ty = table.type_of_var(f_id).unwrap();
    // Function shape preserved; children stay Unknown.
    let PseudoType::Function { params, ret } = f_ty.as_ref() else {
        panic!("expected Function");
    };
    assert!(matches!(params[0].as_ref(), PseudoType::Unknown));
    assert!(matches!(ret.as_ref(), PseudoType::Unknown));
}

#[test]
fn slice_cplus_fixed_point_does_not_demote_concrete_params() {
    // A param slot already concrete (Bool from solver
    // constraints) must not be demoted by an Apply call site with
    // an Int arg; only Unknown slots are overwritten.
    use crate::pseudo::ast::UnaryOp;
    let f_id = VarId::new(2640);
    let x_id = VarId::new(2641);
    // f: fn(x) { not(x) }  →  x must be Bool (from Not constraint).
    let f_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::UnOp {
            op: UnaryOp::Not,
            operand: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        }),
    };
    // `f(42)` is ill-typed on purpose: the merge must neither
    // crash nor demote f's param slot from Bool to Int.
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("f", f_id)),
        args: vec![PseudoExpr::int(42)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "f".into(),
        id: Some(f_id),
        value: PBox::new(f_lambda),
        body: PBox::new(body),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);
    let f_ty = table.type_of_var(f_id).unwrap();
    let PseudoType::Function { params, .. } = f_ty.as_ref() else {
        panic!("expected Function");
    };
    assert!(
        matches!(params[0].as_ref(), PseudoType::Bool),
        "params[0] must stay Bool (concrete from Not constraint) — must NOT demote to Int from call site, got {:?}",
        params[0]
    );
}

#[test]
fn slice_c_let_chain_body_propagates_to_ret() {
    // `let f = fn(x) { let y = 1 in y } in f` → ret = Int (Let body chain).
    let f_id = VarId::new(2440);
    let x_id = VarId::new(2441);
    let y_id = VarId::new(2442);
    let inner_let = PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(y_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::var_with_id("y", y_id)),
    };
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(inner_let),
        }),
        body: PBox::new(PseudoExpr::var_with_id("f", f_id)),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);
    let ty = table.type_of_var(f_id).unwrap();
    let PseudoType::Function { ret, .. } = ty.as_ref() else {
        panic!("expected Function");
    };
    assert!(
        matches!(ret.as_ref(), PseudoType::Int),
        "Let chain inside the Lambda body should propagate Int to ret, got {:?}",
        ret
    );
    // Silence unused warning for the Rc reference.
    let _ = Rc::clone(&ty);
}
