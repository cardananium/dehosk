use super::*;
use crate::pseudo::ast::PBox;

// `Walker` adapter parity tests: a Walker-driven `fold()` must
// produce exactly the same result as the public `simplify()` entry
// for representative inputs.

#[test]
fn walker_adapter_matches_simplify_on_leaves() {
    use crate::pseudo::ast::PseudoData;
    use crate::pseudo::walker::Walker;

    let inputs = vec![
        PseudoExpr::int(42),
        PseudoExpr::Bool(true),
        PseudoExpr::Unit,
        PseudoExpr::String("hello".to_string()),
        PseudoExpr::ByteArray(vec![0x01, 0x02]),
        // Extended leaf coverage.
        PseudoExpr::Error {
            message: Some("boom".to_string()),
        },
        PseudoExpr::Error { message: None },
        PseudoExpr::Raw {
            uplc: "(con integer 7)".to_string(),
            reason: "placeholder".to_string(),
        },
        PseudoExpr::Data(Box::new(PseudoData::Integer(num_bigint::BigInt::from(9)))),
    ];

    for expr in inputs {
        let via_simplify = simplify(expr.clone());
        let via_walker = Simplifier::with_safe_mode(false).fold(expr.clone());
        assert_eq!(
            via_walker, via_simplify,
            "Walker adapter must match simplify() for {:?}",
            expr
        );
    }
}

#[test]
fn walker_adapter_leaf_enter_owned_returns_walk() {
    // Leaves must route through the Walker's native `post_*` hooks, not
    // through a `simplify_*` helper. Both paths are identity on leaves,
    // so behavioural parity cannot distinguish routing; this pins
    // `enter_owned`'s decision directly.
    use crate::pseudo::ast::PseudoData;
    use crate::pseudo::walker::{Entered, Walker};

    let mut simplifier = Simplifier::with_safe_mode(false);

    let leaves = vec![
        PseudoExpr::int(42),
        PseudoExpr::ByteArray(vec![0xaa]),
        PseudoExpr::String("x".to_string()),
        PseudoExpr::Bool(false),
        PseudoExpr::Unit,
        PseudoExpr::Error { message: None },
        PseudoExpr::Raw {
            uplc: "()".to_string(),
            reason: "test".to_string(),
        },
        PseudoExpr::Data(Box::new(PseudoData::Integer(num_bigint::BigInt::from(0)))),
    ];

    for leaf in leaves {
        match simplifier.enter_owned(leaf.clone()) {
            Entered::Walk(_) => {}
            Entered::Done(_) | Entered::Await(_) => panic!(
                "leaf {:?} must return Entered::Walk from Simplifier::enter_owned",
                leaf
            ),
        }
    }
}

#[test]
fn walker_adapter_matches_simplify_on_force_delay() {
    use crate::pseudo::walker::Walker;

    // Force(delay(x)) → x is a canonical simplification.
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::int(7)))));

    let via_simplify = simplify(expr.clone());
    let via_walker = Simplifier::with_safe_mode(false).fold(expr);

    assert_eq!(via_walker, via_simplify);
    assert!(matches!(via_walker, PseudoExpr::Int(_)));
}

#[test]
fn walker_adapter_matches_simplify_on_let_apply() {
    use crate::pseudo::walker::Walker;

    // `let x = 1 in f(x, 2)` — exercises both the Let and Apply
    // hook paths through the adapter.
    let expr = PseudoExpr::let_bind(
        "x",
        PseudoExpr::int(1),
        PseudoExpr::apply(
            PseudoExpr::var("f"),
            vec![PseudoExpr::var("x"), PseudoExpr::int(2)],
        ),
    );

    let via_simplify = simplify(expr.clone());
    let via_walker = Simplifier::with_safe_mode(false).fold(expr);

    assert_eq!(
        via_walker, via_simplify,
        "Walker adapter must preserve Let/Apply task-queue semantics"
    );
}

#[test]
fn walker_adapter_post_hooks_walk_structural_variants() {
    // These structural variants must return `Entered::Walk` from
    // `enter_owned`, so the Walker recurses into children and fires the
    // overridden `post_*` hooks.
    use crate::pseudo::walker::{Entered, Walker};

    let mut simplifier = Simplifier::with_safe_mode(false);

    let structural = vec![
        PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::int(1)),
            right: PBox::new(PseudoExpr::int(2)),
        },
        PseudoExpr::constr(
            ConstructorShape::unknown_data(0, 1),
            vec![PseudoExpr::int(5)],
        ),
        PseudoExpr::List {
            elements: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
            tail: None,
        },
        PseudoExpr::Tuple((vec![PseudoExpr::int(1), PseudoExpr::int(2)]).into()),
        PseudoExpr::Pair(PBox::new(PseudoExpr::int(1)), PBox::new(PseudoExpr::int(2))),
        PseudoExpr::Delay(PBox::new(PseudoExpr::int(3))),
        PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::String("msg".to_string())),
            value: PBox::new(PseudoExpr::int(7)),
        },
    ];

    for expr in structural {
        match simplifier.enter_owned(expr.clone()) {
            Entered::Walk(_) => {}
            Entered::Done(_) | Entered::Await(_) => panic!(
                "structural variant {:?} must return Entered::Walk from Simplifier::enter_owned",
                expr
            ),
        }
    }

    // `FieldAccess` and `IndexAccess` may re-simplify what they rebuild,
    // `Let` processes its binding around the value and the body, and
    // `Apply` runs the `simplify_apply_match` loop: each has the machine
    // fold its children and finishes in a continuation.
    let awaiting = vec![
        PseudoExpr::field_access(
            PseudoExpr::Pair(PBox::new(PseudoExpr::int(1)), PBox::new(PseudoExpr::int(2))),
            "fst".to_string(),
        ),
        PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::List {
                elements: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
                tail: None,
            }),
            index: 0,
        },
        PseudoExpr::let_bind("x", PseudoExpr::int(1), PseudoExpr::var("x")),
        PseudoExpr::apply(PseudoExpr::var("f"), vec![PseudoExpr::int(1)]),
    ];

    for expr in awaiting {
        match simplifier.enter_owned(expr.clone()) {
            Entered::Await(_) => {}
            Entered::Walk(_) | Entered::Done(_) => panic!(
                "{:?} must return Entered::Await from Simplifier::enter_owned",
                expr
            ),
        }
    }
}

#[test]
fn walker_adapter_matches_simplify_on_structural_variants() {
    // Behavioural parity: the Walker's `post_*` path and `simplify()`
    // must agree on all 9 structural variants, via the shared
    // `simplify_*` helpers.
    use crate::pseudo::walker::Walker;

    let inputs = vec![
        // BinOp: Int(0) - x collapses to UnOp::Negate(x).
        PseudoExpr::BinOp {
            op: BinaryOp::Sub,
            left: PBox::new(PseudoExpr::int(0)),
            right: PBox::new(PseudoExpr::int(3)),
        },
        // BinOp: false && x → false.
        PseudoExpr::BinOp {
            op: BinaryOp::And,
            left: PBox::new(PseudoExpr::Bool(false)),
            right: PBox::new(PseudoExpr::var("x")),
        },
        // Constr<1> cons/nil pair collapses to list literal.
        PseudoExpr::constr(
            ConstructorShape::unknown_data(1, 2),
            vec![
                PseudoExpr::int(1),
                PseudoExpr::constr(ConstructorShape::unknown_data(0, 0), vec![]),
            ],
        ),
        // List reconstruction with nested BinOp.
        PseudoExpr::List {
            elements: vec![PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::int(1)),
                right: PBox::new(PseudoExpr::int(2)),
            }]
            .into(),
            tail: None,
        },
        PseudoExpr::Tuple((vec![PseudoExpr::int(1), PseudoExpr::int(2)]).into()),
        PseudoExpr::Pair(PBox::new(PseudoExpr::int(1)), PBox::new(PseudoExpr::int(2))),
        // Delay around simple value unwraps.
        PseudoExpr::Delay(PBox::new(PseudoExpr::int(3))),
        // Trace(literal_string, Error) collapses to Error with message.
        PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::String("boom".to_string())),
            value: PBox::new(PseudoExpr::Error { message: None }),
        },
        // Pair.fst on a Pair literal.
        PseudoExpr::field_access(
            PseudoExpr::Pair(PBox::new(PseudoExpr::int(1)), PBox::new(PseudoExpr::int(2))),
            "fst".to_string(),
        ),
        // IndexAccess on List.
        PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::List {
                elements: vec![PseudoExpr::int(10), PseudoExpr::int(20)].into(),
                tail: None,
            }),
            index: 0,
        },
    ];

    for expr in inputs {
        let via_simplify = simplify(expr.clone());
        let via_walker = Simplifier::with_safe_mode(false).fold(expr.clone());
        assert_eq!(
            via_walker, via_simplify,
            "Walker post_* hooks must match simplify() for {:?}",
            expr
        );
    }
}

#[test]
fn walker_adapter_helper_variants_route_via_simplify_helpers() {
    // `Var` / `Force` / `Lambda` / `If` / `When` / `UnOp` /
    // `BuiltinCall` / `RecFn` must not be walked: their `simplify_*`
    // helpers decide which children to simplify, and when, so they
    // answer `Entered::Done` or `Entered::Await` from `enter_owned`.
    // `walker_adapter_post_hooks_walk_structural_variants` asserts
    // the opposite decision for the structural variants.
    use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
    use crate::pseudo::walker::{Entered, Walker};

    let mut simplifier = Simplifier::with_safe_mode(false);

    let helper_variants = vec![
        PseudoExpr::var("x"),
        PseudoExpr::Force(PBox::new(PseudoExpr::int(1))),
        PseudoExpr::Lambda {
            params: vec![Binder::from("x")],
            body: PBox::new(PseudoExpr::var("x")),
        },
        PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Bool(true)),
            then_branch: PBox::new(PseudoExpr::int(1)),
            else_branch: PBox::new(PseudoExpr::int(2)),
        },
        PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("s")),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::int(0),
            }],
        },
        PseudoExpr::UnOp {
            op: UnaryOp::Not,
            operand: PBox::new(PseudoExpr::Bool(true)),
        },
        PseudoExpr::BuiltinCall {
            name: crate::builtins::BuiltinId::IntAdd,
            args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
        },
        PseudoExpr::RecFn {
            name: Binder::from("f"),
            params: vec![Binder::from("x")],
            body: PBox::new(PseudoExpr::var("x")),
        },
    ];

    for expr in helper_variants {
        match simplifier.enter_owned(expr.clone()) {
            Entered::Done(_) | Entered::Await(_) => {}
            Entered::Walk(_) => panic!(
                "helper-delegated variant {:?} must not return Entered::Walk from Simplifier::enter_owned",
                expr
            ),
        }
    }
}

#[test]
fn walker_adapter_matches_simplify_on_helper_variants() {
    // Behavioural parity: the Walker's `enter_owned` helper path and
    // `simplify()` must agree on every helper-delegated variant.
    use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
    use crate::pseudo::walker::Walker;

    let inputs = vec![
        // Var with no rename/alias — passes through unchanged.
        PseudoExpr::var("x"),
        // Force(Delay(x)) collapses to x.
        PseudoExpr::Force(PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::int(7))))),
        // Lambda body is simplified through simplify_lambda.
        PseudoExpr::Lambda {
            params: vec![Binder::from("x")],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::int(0)),
                right: PBox::new(PseudoExpr::var("x")),
            }),
        },
        // If(true, then, else) constant-folds to `then`.
        PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Bool(true)),
            then_branch: PBox::new(PseudoExpr::int(1)),
            else_branch: PBox::new(PseudoExpr::int(2)),
        },
        // If(false, then, else) constant-folds to `else`.
        PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Bool(false)),
            then_branch: PBox::new(PseudoExpr::int(1)),
            else_branch: PBox::new(PseudoExpr::int(2)),
        },
        // When with single wildcard clause — body becomes the result.
        PseudoExpr::When {
            subject: PBox::new(PseudoExpr::int(0)),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::int(42),
            }],
        },
        // !!x → x.
        PseudoExpr::UnOp {
            op: UnaryOp::Not,
            operand: PBox::new(PseudoExpr::UnOp {
                op: UnaryOp::Not,
                operand: PBox::new(PseudoExpr::var("x")),
            }),
        },
        // !true → false.
        PseudoExpr::UnOp {
            op: UnaryOp::Not,
            operand: PBox::new(PseudoExpr::Bool(true)),
        },
        // RecFn body passes through.
        PseudoExpr::RecFn {
            name: Binder::from("f"),
            params: vec![Binder::from("x")],
            body: PBox::new(PseudoExpr::var("x")),
        },
    ];

    for expr in inputs {
        let via_simplify = simplify(expr.clone());
        let via_walker = Simplifier::with_safe_mode(false).fold(expr.clone());
        assert_eq!(
            via_walker, via_simplify,
            "Walker enter_owned helper-variant routing must match simplify() for {:?}",
            expr
        );
    }
}

#[test]
fn walker_adapter_let_routes_via_simplify_let_expr() {
    // `Let` flows through `simplify_let_expr`: pre-processing, the
    // value, the binding, the body, then post-processing; a simple
    // Let folding to the `simplify()` result exercises all of it.
    use crate::pseudo::walker::Walker;

    // Trivial Let → body substitution path: after simplification,
    // `let x = 1 in x` collapses to `1`.
    let expr = PseudoExpr::let_bind("x", PseudoExpr::int(1), PseudoExpr::var("x"));
    let via_walker = Simplifier::with_safe_mode(false).fold(expr.clone());
    let via_simplify = simplify(expr);
    assert_eq!(
        via_walker, via_simplify,
        "Walker Let routing must match simplify() for trivial Let"
    );
}

#[test]
fn walker_adapter_matches_simplify_on_let_variants() {
    // Behavioural parity: the `simplify_let_expr` flow must agree with
    // `simplify()` across representative Let shapes — inlinable
    // bindings, let-in-value, let-in-body, and nested Lets, which
    // exercise the continuation stack's push/pop discipline.
    use crate::pseudo::walker::Walker;

    let inputs = vec![
        // Trivial: `let x = 1 in x` → `1` (body substitution).
        PseudoExpr::let_bind("x", PseudoExpr::int(1), PseudoExpr::var("x")),
        // Non-referenced body: `let x = 1 in 42` → `42` (dead let drop).
        PseudoExpr::let_bind("x", PseudoExpr::int(1), PseudoExpr::int(42)),
        // Let-in-value: simplified value feeds body.
        PseudoExpr::let_bind(
            "y",
            PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::int(1)),
                right: PBox::new(PseudoExpr::int(2)),
            },
            PseudoExpr::var("y"),
        ),
        // Let-in-body: body itself contains a simplifiable expr.
        PseudoExpr::let_bind(
            "z",
            PseudoExpr::int(5),
            PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::int(0)),
                right: PBox::new(PseudoExpr::var("z")),
            },
        ),
        // Nested Lets — exercises the continuation stack's push/pop
        // invariants.
        PseudoExpr::let_bind(
            "a",
            PseudoExpr::int(1),
            PseudoExpr::let_bind(
                "b",
                PseudoExpr::int(2),
                PseudoExpr::BinOp {
                    op: BinaryOp::Add,
                    left: PBox::new(PseudoExpr::var("a")),
                    right: PBox::new(PseudoExpr::var("b")),
                },
            ),
        ),
    ];

    for expr in inputs {
        let via_simplify = simplify(expr.clone());
        let via_walker = Simplifier::with_safe_mode(false).fold(expr.clone());
        assert_eq!(
            via_walker, via_simplify,
            "Walker Let routing must match simplify() for {:?}",
            expr
        );
    }
}
