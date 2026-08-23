use super::*;
use crate::pseudo::ast::Binder;
use std::rc::Rc;

fn constr_tag_pattern(tag: usize) -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag,
        fields: vec![],
        shape: ConstructorShape::unknown_data(tag, 0),
    }
}

/// `when (a == b) is { Constr<1> -> T; _ -> E }` →
/// `if (a == b) { T } else { E }` — structural Bool subject.
#[test]
fn collapses_tag_one_with_structural_bool_subject() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::Int(1.into())),
            right: PBox::new(PseudoExpr::Int(2.into())),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: constr_tag_pattern(1),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Bool(false),
            },
        ],
    };
    let final_types = FinalTypeTable::new();
    let result = bool_constr_collapse(expr, &final_types);
    let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = result
    else {
        panic!("expected If at top level");
    };
    assert!(matches!(
        condition.as_ref(),
        PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            ..
        }
    ));
    assert!(matches!(then_branch.as_ref(), PseudoExpr::Bool(true)));
    assert!(matches!(else_branch.as_ref(), PseudoExpr::Bool(false)));
}

/// `Constr<0> -> T` arm + Wildcard else → `If { Not(subject),
/// T, E }`.
#[test]
fn collapses_tag_zero_negates_subject() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::Int(1.into())),
            right: PBox::new(PseudoExpr::Int(2.into())),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: constr_tag_pattern(0),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Bool(false),
            },
        ],
    };
    let final_types = FinalTypeTable::new();
    let result = bool_constr_collapse(expr, &final_types);
    let PseudoExpr::If { condition, .. } = result else {
        panic!("expected If");
    };
    assert!(matches!(
        condition.as_ref(),
        PseudoExpr::UnOp {
            op: UnaryOp::Not,
            ..
        }
    ));
}

/// Safety: `when` clauses are ordered, so a wildcard-FIRST
/// layout makes the tag arm unreachable; rewriting it to `if X
/// { Constr-arm } else { Wildcard-arm }` would invert the
/// original semantics, which always ran the wildcard body.
#[test]
fn refuses_wildcard_first_order_is_unsound() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Bool(true)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Int(0.into()),
            },
            WhenClause {
                pattern: constr_tag_pattern(1),
                guard: None,
                body: PseudoExpr::Int(1.into()),
            },
        ],
    };
    let final_types = FinalTypeTable::new();
    let result = bool_constr_collapse(expr, &final_types);
    // MUST stay as When — wildcard-first is ordered and the
    // tag-1 arm is unreachable; rewriting would change semantics.
    assert!(
        matches!(result, PseudoExpr::When { .. }),
        "Wildcard-first When must NOT collapse — ordered \
         clauses mean the wildcard wins. Got:\n{result:?}"
    );
}

/// Safety: clause bodies of `when x as y is { ... }` may
/// reference `y`; an `if x { ... }` rewrite leaves those
/// unbound, so the collapse must refuse this shape.
#[test]
fn refuses_when_subject_name_is_set() {
    use crate::pseudo::ast::Binder;
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Bool(true)),
        subject_name: Some(Binder::synthetic("y")),
        clauses: vec![
            WhenClause {
                pattern: constr_tag_pattern(1),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let final_types = FinalTypeTable::new();
    let result = bool_constr_collapse(expr, &final_types);
    assert!(
        matches!(result, PseudoExpr::When { .. }),
        "`when x as y is ...` MUST stay When — branches may \
         reference `y`, which becomes unbound under If. Got:\n{result:?}"
    );
}

/// Opaque `Var` subject collapses only when
/// `FinalTypeTable` resolves it to `Bool`.
#[test]
fn collapses_var_subject_when_final_types_says_bool() {
    let vid = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("flag", vid)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: constr_tag_pattern(1),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let mut final_types = FinalTypeTable::new();
    final_types.bind_var(vid, Rc::new(PseudoType::Bool));
    final_types.freeze();
    let result = bool_constr_collapse(expr, &final_types);
    assert!(matches!(result, PseudoExpr::If { .. }));
}

/// Safety: an opaque `Var` with unknown / non-Bool type
/// does not collapse.
#[test]
fn refuses_var_subject_without_bool_in_final_types() {
    let vid = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("opaque", vid)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: constr_tag_pattern(1),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let final_types = FinalTypeTable::new(); // no binding for vid
    let result = bool_constr_collapse(expr, &final_types);
    assert!(matches!(result, PseudoExpr::When { .. }));
}

/// Safety: a 3-clause When stays a When — only the 2-clause
/// shape qualifies.
#[test]
fn does_not_collapse_three_clause_when() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Bool(true)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: constr_tag_pattern(1),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: constr_tag_pattern(0),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let final_types = FinalTypeTable::new();
    let result = bool_constr_collapse(expr, &final_types);
    assert!(matches!(result, PseudoExpr::When { .. }));
}

/// Safety: a clause with field binders (`Constr<1>(x)`) does
/// not qualify — only tag-only Constructors with no fields.
#[test]
fn does_not_collapse_clause_with_field_binders() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Bool(true)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint: None,
                    tag: 1,
                    fields: vec![Binder::synthetic("x")],
                    shape: ConstructorShape::unknown_data(1, 1),
                },
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let final_types = FinalTypeTable::new();
    let result = bool_constr_collapse(expr, &final_types);
    assert!(matches!(result, PseudoExpr::When { .. }));
}

/// Opaque `Var` subject whose let-binding value is
/// structurally Bool-producing (`let condition_ok = a == X &&
/// b == Y; when condition_ok is { ... }`) collapses even
/// without `FinalTypeTable` typing `condition_ok` as Bool.
#[test]
fn collapses_var_subject_via_let_bound_bool_value() {
    let vid = VarId::fresh_binding();
    // let condition_ok = (a == b); when condition_ok is { Constr<1> -> T; _ -> E }
    let expr = PseudoExpr::let_bind_with_id(
        "condition_ok",
        vid,
        PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::Int(1.into())),
            right: PBox::new(PseudoExpr::Int(2.into())),
        },
        PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("condition_ok", vid)),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: constr_tag_pattern(1),
                    guard: None,
                    body: PseudoExpr::Bool(true),
                },
                WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: None,
                    body: PseudoExpr::Bool(false),
                },
            ],
        },
    );
    let final_types = FinalTypeTable::new(); // empty — proves the let-bool path
    let result = bool_constr_collapse(expr, &final_types);
    // Outer is still a Let; body inside should now be `If`.
    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected Let at top level");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::If { .. }),
        "When inside let-Bool scope must collapse to If: {body:?}"
    );
}

/// `Known(True)` / `Known(False)` ConstructorShape also
/// counts.
#[test]
fn collapses_known_true_constructor_shape() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Bool(true)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint: None,
                    tag: 1,
                    fields: vec![],
                    shape: ConstructorShape::Known(KnownConstructor::True),
                },
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let final_types = FinalTypeTable::new();
    let result = bool_constr_collapse(expr, &final_types);
    assert!(matches!(result, PseudoExpr::If { .. }));
}

/// A let-value that is a chain of leading `Let` bindings ending in
/// a Bool-producing tail (`let item_1 = …; item_1.foo == bar`):
/// `value_is_structurally_bool` peers through the leading Lets so
/// the `when is_equal is { Constr<1> -> T; _ -> E }` collapses.
#[test]
fn collapses_var_subject_via_let_chain_tail_bool() {
    let vid = VarId::fresh_binding();
    let inner = VarId::fresh_binding();
    // let is_equal = (let item_1 = 3; item_1_expr == 4);
    // when is_equal is { Constr<1> -> T; _ -> E }
    let bool_chain = PseudoExpr::let_bind_with_id(
        "item_1",
        inner,
        PseudoExpr::Int(3.into()),
        PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::var_with_id("item_1", inner)),
            right: PBox::new(PseudoExpr::Int(4.into())),
        },
    );
    let expr = PseudoExpr::let_bind_with_id(
        "is_equal",
        vid,
        bool_chain,
        PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("is_equal", vid)),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: constr_tag_pattern(1),
                    guard: None,
                    body: PseudoExpr::Bool(true),
                },
                WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: None,
                    body: PseudoExpr::Unit,
                },
            ],
        },
    );
    let final_types = FinalTypeTable::new(); // empty — proves the let-chain-tail path
    let result = bool_constr_collapse(expr, &final_types);
    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected outer Let");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::If { .. }),
        "When on a let-chain-tail Bool subject must collapse to If: {body:?}"
    );
}

/// Safety: a let-value whose leading-Let tail is NOT
/// Bool-producing (a raw Constr / data value) must NOT be treated
/// as Bool — the When stays a When.
#[test]
fn refuses_let_chain_tail_non_bool() {
    let vid = VarId::fresh_binding();
    let inner = VarId::fresh_binding();
    // let v = (let a = 3; SomeConstr(a));  -- tail is a Constr, NOT Bool
    let non_bool_chain = PseudoExpr::let_bind_with_id(
        "a",
        inner,
        PseudoExpr::Int(3.into()),
        PseudoExpr::Constr {
            type_hint: None,
            tag: 0,
            fields: vec![PseudoExpr::var_with_id("a", inner)].into(),
            shape: ConstructorShape::unknown_data(0, 1),
        },
    );
    let expr = PseudoExpr::let_bind_with_id(
        "v",
        vid,
        non_bool_chain,
        PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("v", vid)),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: constr_tag_pattern(1),
                    guard: None,
                    body: PseudoExpr::Unit,
                },
                WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: None,
                    body: PseudoExpr::Unit,
                },
            ],
        },
    );
    let final_types = FinalTypeTable::new();
    let result = bool_constr_collapse(expr, &final_types);
    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected outer Let");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::When { .. }),
        "non-Bool let-chain tail must NOT collapse: {body:?}"
    );
}
