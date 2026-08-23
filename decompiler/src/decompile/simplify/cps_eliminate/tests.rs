use super::*;
use crate::pseudo::ast::PBox;

fn compat_known_bindings(names: &[&str]) -> KnownBindings {
    let mut bindings = KnownBindings::default();
    for name in names {
        bindings.compat_names.insert((*name).to_string());
    }
    bindings
}

fn compat_classifications(bindings: &[(&str, usize)]) -> ClassifiedBindings {
    let mut classifications = ClassifiedBindings::default();
    for (name, param_count) in bindings {
        classifications.compat.insert(
            (*name).to_string(),
            CpsClassification {
                param_count: *param_count,
            },
        );
    }
    classifications
}

/// Helper: build a fst selector `fn(x, _) { x }`
fn make_fst_selector() -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec!["x".to_string().into(), "_".to_string().into()],
        body: PBox::new(PseudoExpr::var("x")),
    }
}

/// Helper: build a snd selector `fn(_, y) { y }`
fn make_snd_selector() -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec!["_".to_string().into(), "y".to_string().into()],
        body: PBox::new(PseudoExpr::var("y")),
    }
}

#[test]
fn test_is_fst_selector() {
    assert!(is_fst_selector(&make_fst_selector()));
    assert!(!is_fst_selector(&make_snd_selector()));
}

#[test]
fn test_is_snd_selector() {
    assert!(is_snd_selector(&make_snd_selector()));
    assert!(!is_snd_selector(&make_fst_selector()));
}

#[test]
fn test_selector_detection_rejects_same_name_foreign_body_id() {
    let x_id = VarId::new(9410);
    let y_id = VarId::new(9411);
    let foreign_id = VarId::new(9412);

    let foreign_fst = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id), Binder::new("_", VarId::new(9413))],
        body: PBox::new(PseudoExpr::var_with_id("x", foreign_id)),
    };
    assert!(!is_fst_selector(&foreign_fst));

    let matching_fst = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id), Binder::new("_", VarId::new(9414))],
        body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
    };
    assert!(is_fst_selector(&matching_fst));

    let compat_fst = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id), Binder::new("_", VarId::new(9415))],
        body: PBox::new(PseudoExpr::compat_var("x")),
    };
    assert!(is_fst_selector(&compat_fst));

    let foreign_snd = PseudoExpr::Lambda {
        params: vec![Binder::new("_", VarId::new(9416)), Binder::new("y", y_id)],
        body: PBox::new(PseudoExpr::var_with_id("y", foreign_id)),
    };
    assert!(!is_snd_selector(&foreign_snd));

    let matching_snd = PseudoExpr::Lambda {
        params: vec![Binder::new("_", VarId::new(9417)), Binder::new("y", y_id)],
        body: PBox::new(PseudoExpr::var_with_id("y", y_id)),
    };
    assert!(is_snd_selector(&matching_snd));
}

#[test]
fn test_collect_selector_names() {
    // let choose_fst = fn(x, _) { x } in
    // let choose_snd = fn(_, y) { y } in body
    let expr = PseudoExpr::let_bind(
        "choose_fst",
        make_fst_selector(),
        PseudoExpr::let_bind("choose_snd", make_snd_selector(), PseudoExpr::Unit),
    );
    let (fst, snd) = collect_selector_names(&expr);
    assert!(fst.compat_names.contains("choose_fst"));
    assert!(snd.compat_names.contains("choose_snd"));
}

#[test]
fn test_classify_simple_cps_function() {
    // let choose_fst = fn(x, _) { x }
    // let choose_snd = fn(_, y) { y }
    // let is_positive = fn(n) { if n > 0 { choose_fst } else { choose_snd } }
    // body
    let cps_body = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Gt,
            left: PBox::new(PseudoExpr::var("n")),
            right: PBox::new(PseudoExpr::int(0)),
        }),
        then_branch: PBox::new(PseudoExpr::var("choose_fst")),
        else_branch: PBox::new(PseudoExpr::var("choose_snd")),
    };
    let is_positive = PseudoExpr::Lambda {
        params: vec!["n".to_string().into()],
        body: PBox::new(cps_body),
    };
    let expr = PseudoExpr::let_bind(
        "choose_fst",
        make_fst_selector(),
        PseudoExpr::let_bind(
            "choose_snd",
            make_snd_selector(),
            PseudoExpr::let_bind("is_positive", is_positive, PseudoExpr::Unit),
        ),
    );
    let (fst, snd) = collect_selector_names(&expr);
    let cls = classify_functions(&expr, &fst, &snd);
    assert!(cls.compat.contains_key("is_positive"));
    assert_eq!(cls.compat["is_positive"].param_count, 1);
}

#[test]
fn test_eliminate_cps_full_pipeline() {
    // Build:
    //   let choose_fst = fn(x, _) { x }
    //   let choose_snd = fn(_, y) { y }
    //   let is_positive = fn(n) { if n > 0 { choose_fst } else { choose_snd } }
    //   is_positive(42)(delay(a), delay(b))
    let cps_body = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Gt,
            left: PBox::new(PseudoExpr::var("n")),
            right: PBox::new(PseudoExpr::int(0)),
        }),
        then_branch: PBox::new(PseudoExpr::var("choose_fst")),
        else_branch: PBox::new(PseudoExpr::var("choose_snd")),
    };
    let is_positive = PseudoExpr::Lambda {
        params: vec!["n".to_string().into()],
        body: PBox::new(cps_body),
    };
    let call_site = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("is_positive")),
        args: vec![
            PseudoExpr::int(42),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("a"))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("b"))),
        ]
        .into(),
    };
    let expr = PseudoExpr::let_bind(
        "choose_fst",
        make_fst_selector(),
        PseudoExpr::let_bind(
            "choose_snd",
            make_snd_selector(),
            PseudoExpr::let_bind("is_positive", is_positive, call_site),
        ),
    );

    let result = eliminate_cps_selectors(expr, None);

    // The call site should now be: if is_positive(42) { a } else { b },
    // with the body of is_positive using Bool instead of selectors.
    fn find_if(expr: &PseudoExpr) -> Option<&PseudoExpr> {
        match expr {
            e @ PseudoExpr::If { .. } => Some(e),
            PseudoExpr::Let { body, .. } => find_if(body),
            _ => None,
        }
    }
    let if_node = find_if(&result).expect("Expected an If expression in result");
    if let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = if_node
    {
        // condition should be Apply(is_positive, [42])
        assert!(matches!(condition.as_ref(), PseudoExpr::Apply { .. }));
        assert_eq!(**then_branch, PseudoExpr::var("a"));
        assert_eq!(**else_branch, PseudoExpr::var("b"));
    } else {
        panic!("Expected If node");
    }
}

#[test]
fn test_body_rewrite_simplifies_to_condition() {
    // A function body: if n > 0 { fst } else { snd }
    // After rewrite: if n > 0 { True } else { False } -> n > 0
    let body = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Gt,
            left: PBox::new(PseudoExpr::var("n")),
            right: PBox::new(PseudoExpr::int(0)),
        }),
        then_branch: PBox::new(PseudoExpr::var("choose_fst")),
        else_branch: PBox::new(PseudoExpr::var("choose_snd")),
    };

    let fst_names = compat_known_bindings(&["choose_fst"]);
    let snd_names = compat_known_bindings(&["choose_snd"]);

    let result = rewrite_selector_body(&body, &fst_names, &snd_names);
    assert!(matches!(
        result,
        PseudoExpr::BinOp {
            op: BinaryOp::Gt,
            ..
        }
    ));
}

#[test]
fn test_body_rewrite_keeps_non_bool_typed_condition_as_if() {
    // An unknown-typed Var is allowed as a boolean condition and would
    // collapse, so the condition is a Data literal — a known non-bool
    // that must stay an If.
    let body = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Data(Box::new(
            crate::pseudo::ast::PseudoData::Integer(0.into()),
        ))),
        then_branch: PBox::new(PseudoExpr::var("choose_fst")),
        else_branch: PBox::new(PseudoExpr::var("b")),
    };

    let fst_names = compat_known_bindings(&["choose_fst"]);
    let snd_names = KnownBindings::default();

    let result = rewrite_selector_body(&body, &fst_names, &snd_names);
    assert!(
        matches!(result, PseudoExpr::If { .. }),
        "expected non-bool condition to stay as If, got: {result:?}"
    );
}

#[test]
fn test_body_rewrite_keeps_apply_condition_as_if() {
    let body = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("scan")),
            args: vec![PseudoExpr::var("xs")].into(),
        }),
        then_branch: PBox::new(PseudoExpr::var("choose_fst")),
        else_branch: PBox::new(PseudoExpr::var("b")),
    };

    let fst_names = compat_known_bindings(&["choose_fst"]);
    let snd_names = KnownBindings::default();

    let result = rewrite_selector_body(&body, &fst_names, &snd_names);
    assert!(
        matches!(result, PseudoExpr::If { .. }),
        "expected apply condition to stay as If, got: {result:?}"
    );
}

#[test]
fn test_call_site_rewrite_keeps_classified_helper_var_even_with_stale_type() {
    let function = PseudoExpr::var("e4_is_equal");
    let args = vec![
        PseudoExpr::Delay(PBox::new(PseudoExpr::var("a"))),
        PseudoExpr::Delay(PBox::new(PseudoExpr::var("b"))),
    ];

    let classifications = compat_classifications(&[("e4_is_equal", 0)]);
    let fst_names = KnownBindings::default();
    let snd_names = KnownBindings::default();

    let mut rewriter = RewriteCallSites {
        classifications: &classifications,
        fst_names: &fst_names,
        snd_names: &snd_names,
    };

    let result = rewriter.post_apply(function, args);
    assert!(
        matches!(result, PseudoExpr::If { .. }),
        "expected classified helper var to still rewrite as If despite stale type, got: {result:?}"
    );
}

#[test]
fn test_call_site_rewrite_keeps_classified_helper_var_with_unknown_type() {
    let function = PseudoExpr::var("e4_is_equal");
    let args = vec![
        PseudoExpr::Delay(PBox::new(PseudoExpr::var("a"))),
        PseudoExpr::Delay(PBox::new(PseudoExpr::var("b"))),
    ];

    let classifications = compat_classifications(&[("e4_is_equal", 0)]);
    let fst_names = KnownBindings::default();
    let snd_names = KnownBindings::default();

    let mut rewriter = RewriteCallSites {
        classifications: &classifications,
        fst_names: &fst_names,
        snd_names: &snd_names,
    };

    let result = rewriter.post_apply(function, args);
    assert!(
        matches!(result, PseudoExpr::If { .. }),
        "expected classified helper var to still rewrite as If with unknown type, got: {result:?}"
    );
}

#[test]
fn test_body_rewrite_ignores_shadowed_same_name_selector_binding() {
    let outer_selector_id = VarId::fresh_binding();
    let inner_selector_id = VarId::fresh_binding();
    let body = PseudoExpr::Lambda {
        params: vec![Binder::new("choose_fst", inner_selector_id)],
        body: PBox::new(PseudoExpr::Var {
            name: "choose_fst".to_string(),
            id: Some(inner_selector_id),
        }),
    };

    let mut fst_names = KnownBindings::default();
    fst_names.insert_binding("choose_fst", Some(outer_selector_id));

    let result = rewrite_selector_body(&body, &fst_names, &KnownBindings::default());
    assert!(
        matches!(
            &result,
            PseudoExpr::Lambda { params, body }
                if params.len() == 1
                    && params[0].as_str() == "choose_fst"
                    && params[0].var_id() == inner_selector_id
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Var { name, id, .. }
                            if name == "choose_fst" && *id == Some(inner_selector_id)
                    )
        ),
        "expected shadowed selector binding to stay intact, got: {result:?}"
    );
}

#[test]
fn test_call_site_rewrite_ignores_same_name_different_id_classified_helper() {
    let outer_helper_id = VarId::fresh_binding();
    let inner_helper_id = VarId::fresh_binding();
    let function = PseudoExpr::var_with_id("e4_is_equal", inner_helper_id);
    let args = vec![
        PseudoExpr::Delay(PBox::new(PseudoExpr::var("a"))),
        PseudoExpr::Delay(PBox::new(PseudoExpr::var("b"))),
    ];

    let mut classifications = ClassifiedBindings::default();
    classifications.insert_binding(
        "e4_is_equal",
        Some(outer_helper_id),
        CpsClassification { param_count: 0 },
    );
    let fst_names = KnownBindings::default();
    let snd_names = KnownBindings::default();

    let mut rewriter = RewriteCallSites {
        classifications: &classifications,
        fst_names: &fst_names,
        snd_names: &snd_names,
    };

    let result = rewriter.post_apply(function.clone(), args.clone());
    assert_eq!(
        result,
        PseudoExpr::Apply {
            function: PBox::new(function),
            args: args.into(),
        }
    );
}

#[test]
fn test_body_rewrite_negation() {
    // if n > 0 { snd } else { fst } -> !(n > 0) -> n <= 0
    let body = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Gt,
            left: PBox::new(PseudoExpr::var("n")),
            right: PBox::new(PseudoExpr::int(0)),
        }),
        then_branch: PBox::new(PseudoExpr::var("choose_snd")),
        else_branch: PBox::new(PseudoExpr::var("choose_fst")),
    };

    let fst_names = compat_known_bindings(&["choose_fst"]);
    let snd_names = compat_known_bindings(&["choose_snd"]);

    let result = rewrite_selector_body(&body, &fst_names, &snd_names);
    assert!(matches!(
        result,
        PseudoExpr::BinOp {
            op: BinaryOp::Lte,
            ..
        }
    ));
}

#[test]
fn test_delay_wrapped_selector() {
    // let choose_fst = delay(fn(x, _) { x })
    let expr = PseudoExpr::let_bind(
        "choose_fst",
        PseudoExpr::Delay(PBox::new(make_fst_selector())),
        PseudoExpr::Unit,
    );
    let (fst, _snd) = collect_selector_names(&expr);
    assert!(fst.compat_names.contains("choose_fst"));
}

#[test]
fn test_no_rewrite_when_used_as_value() {
    // If is_positive is passed as an argument (not just called),
    // it should NOT be rewritten.
    let cps_body = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Gt,
            left: PBox::new(PseudoExpr::var("n")),
            right: PBox::new(PseudoExpr::int(0)),
        }),
        then_branch: PBox::new(PseudoExpr::var("choose_fst")),
        else_branch: PBox::new(PseudoExpr::var("choose_snd")),
    };
    let is_positive = PseudoExpr::Lambda {
        params: vec!["n".to_string().into()],
        body: PBox::new(cps_body),
    };
    // Usage: some_fn(is_positive) — passing as value, not calling
    let value_use = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("some_fn")),
        args: vec![PseudoExpr::var("is_positive")].into(),
    };
    let expr = PseudoExpr::let_bind(
        "choose_fst",
        make_fst_selector(),
        PseudoExpr::let_bind(
            "choose_snd",
            make_snd_selector(),
            PseudoExpr::let_bind("is_positive", is_positive, value_use),
        ),
    );

    let result = eliminate_cps_selectors(expr.clone(), None);
    // The expression should be unchanged because is_positive is used as a value
    assert_eq!(result, expr);
}

#[test]
fn test_no_selectors_is_noop() {
    let expr = PseudoExpr::let_bind("x", PseudoExpr::int(1), PseudoExpr::var("x"));
    let result = eliminate_cps_selectors(expr.clone(), None);
    assert_eq!(result, expr);
}

#[test]
fn test_or_pattern_in_body_rewrite() {
    // if cond { fst } else { expr } -> cond || expr
    let body = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("a")),
        then_branch: PBox::new(PseudoExpr::var("choose_fst")),
        else_branch: PBox::new(PseudoExpr::var("b")),
    };

    let fst_names = compat_known_bindings(&["choose_fst"]);
    let snd_names = KnownBindings::default();

    let result = rewrite_selector_body(&body, &fst_names, &snd_names);
    assert!(matches!(
        result,
        PseudoExpr::BinOp {
            op: BinaryOp::Or,
            ..
        }
    ));
}

#[test]
fn test_and_pattern_in_body_rewrite() {
    // if cond { expr } else { snd } -> cond && expr
    let body = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("a")),
        then_branch: PBox::new(PseudoExpr::var("b")),
        else_branch: PBox::new(PseudoExpr::var("choose_snd")),
    };

    let fst_names = KnownBindings::default();
    let snd_names = compat_known_bindings(&["choose_snd"]);

    let result = rewrite_selector_body(&body, &fst_names, &snd_names);
    assert!(matches!(
        result,
        PseudoExpr::BinOp {
            op: BinaryOp::And,
            ..
        }
    ));
}

#[test]
fn test_structural_if_selector() {
    // (if cond { choose_fst } else { choose_snd })(delay(a), delay(b))
    // > if cond { a } else { b }
    let selector = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(PseudoExpr::var("choose_fst")),
        else_branch: PBox::new(PseudoExpr::var("choose_snd")),
    };
    let apply = PseudoExpr::Apply {
        function: PBox::new(selector),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("a"))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("b"))),
        ]
        .into(),
    };
    let expr = PseudoExpr::let_bind(
        "choose_fst",
        make_fst_selector(),
        PseudoExpr::let_bind("choose_snd", make_snd_selector(), apply),
    );

    let result = eliminate_cps_selectors(expr, None);

    fn find_if(expr: &PseudoExpr) -> Option<&PseudoExpr> {
        match expr {
            e @ PseudoExpr::If { .. } => Some(e),
            PseudoExpr::Let { body, .. } => find_if(body),
            _ => None,
        }
    }
    let if_node = find_if(&result).expect("Expected an If expression in result");
    if let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = if_node
    {
        assert_eq!(**condition, PseudoExpr::var("cond"));
        assert_eq!(**then_branch, PseudoExpr::var("a"));
        assert_eq!(**else_branch, PseudoExpr::var("b"));
    } else {
        panic!("Expected If node");
    }
}

#[test]
fn test_structural_if_selector_inverted() {
    // (if cond { choose_snd } else { choose_fst })(delay(a), delay(b))
    // > if !cond { a } else { b }
    let selector = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(PseudoExpr::var("choose_snd")),
        else_branch: PBox::new(PseudoExpr::var("choose_fst")),
    };
    let apply = PseudoExpr::Apply {
        function: PBox::new(selector),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("a"))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("b"))),
        ]
        .into(),
    };
    let expr = PseudoExpr::let_bind(
        "choose_fst",
        make_fst_selector(),
        PseudoExpr::let_bind("choose_snd", make_snd_selector(), apply),
    );

    let result = eliminate_cps_selectors(expr, None);

    fn find_if(expr: &PseudoExpr) -> Option<&PseudoExpr> {
        match expr {
            e @ PseudoExpr::If { .. } => Some(e),
            PseudoExpr::Let { body, .. } => find_if(body),
            _ => None,
        }
    }
    let if_node = find_if(&result).expect("Expected an If expression in result");
    if let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = if_node
    {
        assert!(
            matches!(
                condition.as_ref(),
                PseudoExpr::UnOp {
                    op: UnaryOp::Not,
                    ..
                }
            ),
            "Expected negated condition, got: {:?}",
            condition
        );
        assert_eq!(**then_branch, PseudoExpr::var("a"));
        assert_eq!(**else_branch, PseudoExpr::var("b"));
    } else {
        panic!("Expected If node");
    }
}

#[test]
fn test_structural_when_selector() {
    // (when x is { Constr<0> -> choose_fst; Constr<1> -> choose_snd })(delay(a), delay(b))
    // > if (when x is { Constr<0> -> True; Constr<1> -> False }) { a } else { b }
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;

    let selector = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::var("choose_fst"),
            ),
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                PseudoExpr::var("choose_snd"),
            ),
        ],
    };
    let apply = PseudoExpr::Apply {
        function: PBox::new(selector),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("a"))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("b"))),
        ]
        .into(),
    };
    let expr = PseudoExpr::let_bind(
        "choose_fst",
        make_fst_selector(),
        PseudoExpr::let_bind("choose_snd", make_snd_selector(), apply),
    );

    let result = eliminate_cps_selectors(expr, None);

    fn find_if(expr: &PseudoExpr) -> Option<&PseudoExpr> {
        match expr {
            e @ PseudoExpr::If { .. } => Some(e),
            PseudoExpr::Let { body, .. } => find_if(body),
            _ => None,
        }
    }
    let if_node = find_if(&result).expect("Expected an If expression in result");
    if let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = if_node
    {
        assert!(
            matches!(condition.as_ref(), PseudoExpr::When { .. }),
            "Expected When condition, got: {:?}",
            condition
        );
        if let PseudoExpr::When { clauses, .. } = condition.as_ref() {
            assert_eq!(clauses.len(), 2);
            assert_eq!(clauses[0].body, PseudoExpr::Bool(true));
            assert_eq!(clauses[1].body, PseudoExpr::Bool(false));
        }
        assert_eq!(**then_branch, PseudoExpr::var("a"));
        assert_eq!(**else_branch, PseudoExpr::var("b"));
    } else {
        panic!("Expected If node");
    }
}

#[test]
fn test_structural_no_match_without_delay() {
    // (if cond { choose_fst } else { choose_snd })(a, b) -- NOT rewritten (no Delay wrappers)
    let selector = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(PseudoExpr::var("choose_fst")),
        else_branch: PBox::new(PseudoExpr::var("choose_snd")),
    };
    let apply = PseudoExpr::Apply {
        function: PBox::new(selector.clone()),
        args: vec![PseudoExpr::var("a"), PseudoExpr::var("b")].into(),
    };
    let expr = PseudoExpr::let_bind(
        "choose_fst",
        make_fst_selector(),
        PseudoExpr::let_bind("choose_snd", make_snd_selector(), apply),
    );

    let result = eliminate_cps_selectors(expr, None);

    fn find_apply(expr: &PseudoExpr) -> Option<&PseudoExpr> {
        match expr {
            e @ PseudoExpr::Apply { .. } => Some(e),
            PseudoExpr::Let { body, .. } => find_apply(body),
            _ => None,
        }
    }
    let apply_node = find_apply(&result);
    assert!(
        apply_node.is_some(),
        "Expected Apply to remain (no Delay wrappers), got: {:?}",
        result
    );
}

#[test]
fn test_structural_works_with_empty_classifications() {
    // The structural rewrite fires even when no function is classified.
    let selector = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(PseudoExpr::var("choose_fst")),
        else_branch: PBox::new(PseudoExpr::var("choose_snd")),
    };
    let apply = PseudoExpr::Apply {
        function: PBox::new(selector),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("a"))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("b"))),
        ]
        .into(),
    };
    let expr = PseudoExpr::let_bind(
        "choose_fst",
        make_fst_selector(),
        PseudoExpr::let_bind("choose_snd", make_snd_selector(), apply),
    );

    let result = eliminate_cps_selectors(expr, None);

    fn find_if(expr: &PseudoExpr) -> Option<&PseudoExpr> {
        match expr {
            e @ PseudoExpr::If { .. } => Some(e),
            PseudoExpr::Let { body, .. } => find_if(body),
            _ => None,
        }
    }
    let if_node =
        find_if(&result).expect("Expected an If expression even with empty classifications");
    if let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = if_node
    {
        assert_eq!(**condition, PseudoExpr::var("cond"));
        assert_eq!(**then_branch, PseudoExpr::var("a"));
        assert_eq!(**else_branch, PseudoExpr::var("b"));
    } else {
        panic!("Expected If node");
    }
}

#[test]
fn test_structural_inline_selector_branches_without_named_selectors() {
    let selector = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(make_fst_selector()),
        else_branch: PBox::new(make_snd_selector()),
    };
    let expr = PseudoExpr::Apply {
        function: PBox::new(selector),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("a"))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("b"))),
        ]
        .into(),
    };

    let result = eliminate_cps_selectors(expr, None);

    match result {
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            assert_eq!(*condition, PseudoExpr::var("cond"));
            assert_eq!(*then_branch, PseudoExpr::var("a"));
            assert_eq!(*else_branch, PseudoExpr::var("b"));
        }
        other => panic!("expected structural inline selector rewrite, got: {other:?}"),
    }
}

#[test]
fn test_rewrite_inline_selector_returning_function_to_bool() {
    let expr = PseudoExpr::let_bind(
        "pick",
        PseudoExpr::Lambda {
            params: vec!["cond".to_string().into()],
            body: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::var("cond")),
                then_branch: PBox::new(make_fst_selector()),
                else_branch: PBox::new(make_snd_selector()),
            }),
        },
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("pick")),
            args: vec![PseudoExpr::var("x")].into(),
        },
    );

    let result = eliminate_cps_selectors(expr, None);

    match result {
        PseudoExpr::Let { value, body, .. } => {
            assert!(
                matches!(
                    value.as_ref(),
                    PseudoExpr::Lambda { params, body }
                        if params == &vec!["cond".to_string()]
                            && matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "cond")
                ),
                "expected inline selector function to rewrite to boolean identity, got: {value:?}"
            );
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::Apply { function, args }
                        if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "pick")
                            && matches!(args.as_slice(), [PseudoExpr::Var { name, .. }] if name == "x")
                ),
                "expected pick(x) body to stay intact, got: {body:?}"
            );
        }
        other => panic!("expected let-bound rewritten function, got: {other:?}"),
    }
}

#[test]
fn test_rewrite_delay_wrapped_inline_selector_function_to_bool() {
    let expr = PseudoExpr::let_bind(
        "pick",
        PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
            params: vec!["cond".to_string().into()],
            body: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::var("cond")),
                then_branch: PBox::new(make_fst_selector()),
                else_branch: PBox::new(make_snd_selector()),
            }),
        })),
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("pick")))),
            args: vec![PseudoExpr::var("x")].into(),
        },
    );

    let result = eliminate_cps_selectors(expr, None);

    match result {
        PseudoExpr::Let { value, .. } => {
            assert!(
                matches!(
                    value.as_ref(),
                    PseudoExpr::Delay(inner)
                        if matches!(
                            inner.as_ref(),
                            PseudoExpr::Lambda { params, body }
                                if params == &vec!["cond".to_string()]
                                    && matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "cond")
                        )
                ),
                "expected delayed selector function to rewrite to delayed boolean identity, got: {value:?}"
            );
        }
        other => panic!("expected let-bound delayed function, got: {other:?}"),
    }
}

#[test]
fn test_eliminate_cps_selectors_env_refines_tipo_for_non_bool_guard() {
    use crate::decompile::mid::type_env::TypeEnvironment;
    use std::rc::Rc;

    let payload_id = VarId::new(42);

    let handler = PseudoExpr::Lambda {
        params: vec!["payload".to_string().into()],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Var {
                name: "payload".to_string(),
                id: Some(payload_id),
            }),
            then_branch: PBox::new(PseudoExpr::var("choose_fst")),
            else_branch: PBox::new(PseudoExpr::var("choose_snd")),
        }),
    };

    let call_site = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("handler")),
            args: vec![PseudoExpr::var("input")].into(),
        }),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("a"))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("b"))),
        ]
        .into(),
    };

    let expr = PseudoExpr::let_bind(
        "choose_fst",
        make_fst_selector(),
        PseudoExpr::let_bind(
            "choose_snd",
            make_snd_selector(),
            PseudoExpr::let_bind("handler", handler, call_site),
        ),
    );

    let result_no_env = eliminate_cps_selectors(expr.clone(), None);

    let mut env = TypeEnvironment::new();
    env.bind_var(payload_id, Rc::new(PseudoType::Int));
    let result_with_env = eliminate_cps_selectors(expr, Some(&env));

    // `eliminate_cps_selectors` ignores its env argument, and a Var carries
    // no inline type, so refining `payload` to `Int` cannot change the
    // outcome: both paths produce the same tree.
    assert!(
        result_no_env.structural_eq(&result_with_env),
        "without inline tipo, both paths should produce the same output"
    );
}
