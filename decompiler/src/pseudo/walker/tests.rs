use super::{FoldAction, WalkVisitor, Walker};
use crate::pseudo::ast::{BinaryOp, PseudoExpr};
use crate::pseudo::var_id::VarId;

#[test]
fn identity_walker_preserves_expression() {
    struct Identity;
    impl Walker for Identity {}

    let expr = PseudoExpr::let_bind(
        "x",
        PseudoExpr::int(1),
        PseudoExpr::binop(BinaryOp::Add, PseudoExpr::var("x"), PseudoExpr::int(2)),
    );

    let mut w = Identity;
    assert_eq!(w.fold(expr.clone()), expr);
}

#[test]
fn pre_hook_replace_short_circuits_recursion() {
    struct ReplaceApply {
        pre_visits: usize,
        post_int_calls: usize,
    }
    impl Walker for ReplaceApply {
        fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
            self.pre_visits += 1;
            if matches!(expr, PseudoExpr::Apply { .. }) {
                FoldAction::Replace(PseudoExpr::int(0))
            } else {
                FoldAction::Walk
            }
        }

        fn post_int(&mut self, n: num_bigint::BigInt) -> PseudoExpr {
            self.post_int_calls += 1;
            PseudoExpr::Int(n)
        }
    }

    let expr = PseudoExpr::apply(
        PseudoExpr::var("f"),
        vec![PseudoExpr::int(1), PseudoExpr::int(2)],
    );

    let mut w = ReplaceApply {
        pre_visits: 0,
        post_int_calls: 0,
    };
    let result = w.fold(expr);

    assert_eq!(result, PseudoExpr::int(0));
    assert_eq!(w.pre_visits, 1, "Replace must skip recursion into children");
    assert_eq!(
        w.post_int_calls, 0,
        "post_int must not fire for skipped children"
    );
}

#[test]
fn scope_hooks_fire_in_enter_exit_order_around_body() {
    struct Tracer {
        events: Vec<String>,
    }
    impl Walker for Tracer {
        fn enter_let(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) -> String {
            self.events.push(format!("enter_let:{name}"));
            name.to_string()
        }

        fn exit_let(&mut self, name: &str) {
            self.events.push(format!("exit_let:{name}"));
        }

        fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
            self.events.push(format!("post_var:{name}"));
            PseudoExpr::Var { name, id }
        }
    }

    let expr = PseudoExpr::let_bind("a", PseudoExpr::int(1), PseudoExpr::var("a"));

    let mut w = Tracer { events: Vec::new() };
    w.fold(expr);

    assert_eq!(
        w.events,
        vec![
            "enter_let:a".to_string(),
            "post_var:a".to_string(),
            "exit_let:a".to_string(),
        ],
        "scope hooks must bracket body traversal"
    );
}

#[test]
fn post_expr_runs_once_per_node_after_reconstruction() {
    struct CountNodes {
        post_expr_calls: usize,
    }
    impl Walker for CountNodes {
        fn post_expr(&mut self, expr: PseudoExpr) -> PseudoExpr {
            self.post_expr_calls += 1;
            expr
        }
    }

    // Let { value=Int, body=Var } -> 3 nodes.
    let expr = PseudoExpr::let_bind("a", PseudoExpr::int(7), PseudoExpr::var("a"));

    let mut w = CountNodes { post_expr_calls: 0 };
    w.fold(expr);

    assert_eq!(
        w.post_expr_calls, 3,
        "post_expr fires once per reconstructed node"
    );
}

#[test]
fn walk_visitor_reexport_is_read_only() {
    struct CountVars {
        count: usize,
    }
    impl WalkVisitor for CountVars {
        fn visit_var(&mut self, _name: &str, _id: &Option<VarId>) {
            self.count += 1;
        }
    }

    let expr = PseudoExpr::apply(
        PseudoExpr::var("f"),
        vec![PseudoExpr::var("x"), PseudoExpr::var("y")],
    );

    let mut v = CountVars { count: 0 };
    v.walk(&expr);

    assert_eq!(v.count, 3);
}
