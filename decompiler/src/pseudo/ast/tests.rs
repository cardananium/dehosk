use super::*;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;

#[test]
fn test_binder_var_id_accessor() {
    let id = VarId::from_raw(42);
    let b = Binder::new("x", id);
    assert_eq!(b.var_id(), id);
}

#[test]
fn test_binder_eq_by_var_id_same_id() {
    let id = VarId::from_raw(7);
    let a = Binder::new("x", id);
    let b = Binder::new("y", id);
    assert!(a.eq_by_var_id(&b));
    // Default PartialEq is VarId-based: same id → equal
    assert_eq!(a, b);
}

#[test]
fn test_binder_eq_by_var_id_different_id() {
    let a = Binder::new("x", VarId::from_raw(1));
    let b = Binder::new("x", VarId::from_raw(2));
    assert!(!a.eq_by_var_id(&b));
    // Default PartialEq is VarId-based: different id → not equal
    assert_ne!(a, b);
}

#[test]
fn ast_compat_constructors_mint_placeholders_or_hidden_ids() {
    let explicit_id = VarId::from_raw(42);
    let explicit_binder = Binder::new("x", explicit_id);
    assert_eq!(explicit_binder.id, explicit_id);

    let synthetic_binder = Binder::synthetic("x");
    assert!(
        synthetic_binder.id.get().is_some(),
        "Binder::synthetic should mint an authoritative hidden binding id"
    );
    let from_string_binder: Binder = "x".to_string().into();
    let from_str_binder: Binder = "x".into();
    assert!(
        from_string_binder.id.get().is_some() && from_str_binder.id.get().is_some(),
        "Binder From impls intentionally mint hidden binding ids"
    );
    assert_ne!(from_string_binder.id, from_str_binder.id);

    for expr in [PseudoExpr::compat_var("x"), PseudoExpr::var("x")] {
        assert!(
            matches!(expr, PseudoExpr::Var { id, .. } if id.get().is_none()),
            "compat var constructors should mint placeholder ids, got: {expr:?}"
        );
    }
    assert!(
        matches!(
            PseudoExpr::var_with_id("x", explicit_id),
            PseudoExpr::Var { id, .. } if id == Some(explicit_id)
        ),
        "var_with_id must preserve explicit identity"
    );

    for expr in [
        PseudoExpr::compat_let_bind("x", PseudoExpr::Unit, PseudoExpr::Unit),
        PseudoExpr::let_bind("x", PseudoExpr::Unit, PseudoExpr::Unit),
    ] {
        assert!(
            matches!(expr, PseudoExpr::Let { id, .. } if id.get().is_none()),
            "compat let constructors should mint placeholder ids, got: {expr:?}"
        );
    }
    assert!(
        matches!(
            PseudoExpr::let_bind_with_id("x", explicit_id, PseudoExpr::Unit, PseudoExpr::Unit),
            PseudoExpr::Let { id, .. } if id == Some(explicit_id)
        ),
        "let_bind_with_id must preserve explicit identity"
    );

    let lambda = PseudoExpr::lambda(vec!["a".to_string(), "b".to_string()], PseudoExpr::Unit);
    assert!(
        matches!(
            lambda,
            PseudoExpr::Lambda { params, .. }
                if params.len() == 2
                    && params.iter().all(|p| p.id.get().is_some())
                    && params[0].id != params[1].id
        ),
        "lambda(Vec<String>) should mint hidden binder ids"
    );

    let explicit_param = Binder::new("a", explicit_id);
    assert!(
        matches!(
            PseudoExpr::lambda_with_binders(vec![explicit_param.clone()], PseudoExpr::Unit),
            PseudoExpr::Lambda { params, .. } if params == vec![explicit_param]
        ),
        "lambda_with_binders must preserve explicit binders"
    );

    let pattern = WhenPattern::var("x");
    assert!(
        matches!(pattern, WhenPattern::Var(binder) if binder.id.get().is_some()),
        "WhenPattern::var should mint a hidden binder id"
    );
}

#[test]
fn test_binary_op_symbol() {
    assert_eq!(BinaryOp::Add.symbol(), "+");
    assert_eq!(BinaryOp::Eq.symbol(), "==");
    assert_eq!(BinaryOp::And.symbol(), "&&");
}

#[test]
fn test_field_access_typed_matches_legacy_for_structural_selectors() {
    for (legacy, typed) in [
        ("fst", FieldSelector::PairFst),
        ("snd", FieldSelector::PairSnd),
        ("head", FieldSelector::ListHead),
    ] {
        let id = VarId::from_raw(0);
        let record = PseudoExpr::var_with_id("r", id);
        let from_string = PseudoExpr::field_access(record.clone(), legacy.to_string());
        let from_typed = PseudoExpr::field_access_typed(record, typed);
        assert_eq!(
            from_string, from_typed,
            "legacy string {legacy:?} must produce same FieldAccess as typed selector"
        );
    }
}

#[test]
fn test_field_access_typed_preserves_named_and_context_selectors() {
    let id = VarId::from_raw(0);
    let record = PseudoExpr::var_with_id("r", id);
    let named =
        PseudoExpr::field_access_typed(record.clone(), FieldSelector::NamedField("tag".into()));
    let ctx = PseudoExpr::field_access_typed(record, FieldSelector::ContextField("purpose".into()));
    match &named {
        PseudoExpr::FieldAccess { selector, .. } => {
            assert_eq!(selector.as_pretty_name(), "tag");
            assert_eq!(selector, &FieldSelector::NamedField("tag".into()));
        }
        _ => panic!("expected FieldAccess"),
    }
    match &ctx {
        PseudoExpr::FieldAccess { selector, .. } => {
            assert_eq!(selector.as_pretty_name(), "purpose");
            assert_eq!(selector, &FieldSelector::ContextField("purpose".into()));
        }
        _ => panic!("expected FieldAccess"),
    }
}

#[test]
fn test_binary_op_precedence() {
    assert!(BinaryOp::Mul.precedence() > BinaryOp::Add.precedence());
    assert!(BinaryOp::Add.precedence() > BinaryOp::Eq.precedence());
}

#[test]
fn test_pseudo_type_to_string() {
    assert_eq!(PseudoType::Int.to_string(), "Int");
    assert_eq!(
        PseudoType::List(Rc::new(PseudoType::Int)).to_string(),
        "List<Int>"
    );
    assert_eq!(
        PseudoType::Option(Rc::new(PseudoType::ByteArray)).to_string(),
        "Option<ByteArray>"
    );
}

#[test]
fn test_pseudo_expr_constructors() {
    let expr = PseudoExpr::if_then_else(
        PseudoExpr::bool(true),
        PseudoExpr::int(1),
        PseudoExpr::int(0),
    );

    assert!(matches!(expr, PseudoExpr::If { .. }));
}

#[test]
fn test_when_pattern_to_string() {
    // Option: Some carries 1 field at tag 0.
    let pat =
        WhenPattern::constructor_known(KnownConstructor::Some, vec![Binder::from("x".to_string())]);
    assert_eq!(pat.to_string(), "Some(x)");

    let pat = WhenPattern::wildcard();
    assert_eq!(pat.to_string(), "_");
}

#[test]
fn test_when_pattern_to_string_uses_constr_tag_when_anonymous() {
    // No registry hint + Unknown shape → Constr{tag} fallback.
    let pat = WhenPattern::constructor(
        ConstructorShape::unknown_data(5, 1),
        vec![Binder::from("f".to_string())],
    );
    assert_eq!(pat.to_string(), "Constr5(f)");
}

#[test]
fn test_constr_structural_eq_known_shape_matches() {
    let a = PseudoExpr::some(PseudoExpr::int(1));
    let b = PseudoExpr::some(PseudoExpr::int(1));
    assert!(a.structural_eq(&b));
}

#[test]
fn test_constr_structural_eq_matches_identical_unknown_shapes() {
    // Structural equality anchors on the shape, not on per-node metadata
    // such as `type_hint`.
    let a = PseudoExpr::constr(
        ConstructorShape::unknown_data(2, 1),
        vec![PseudoExpr::int(0)],
    );
    let b = PseudoExpr::constr_with_hint(
        ConstructorShape::unknown_data(2, 1),
        vec![PseudoExpr::int(0)],
        Some(TypeHintId::new("SomeHint")),
    );
    assert!(a.structural_eq(&b));
}

#[test]
fn test_constr_structural_eq_different_tags_not_equal() {
    let a = PseudoExpr::constr(ConstructorShape::unknown_data(0, 0), vec![]);
    let b = PseudoExpr::constr(ConstructorShape::unknown_data(1, 0), vec![]);
    assert!(!a.structural_eq(&b));
}

#[test]
fn test_when_pattern_structural_eq_matches_identical_unknown_shapes() {
    // Pattern structural equality anchors on shape + binder names,
    // so a `TypeHintId` does not affect convergence detection.
    let hinted = WhenPattern::constructor_with_hint(
        ConstructorShape::unknown_data(0, 2),
        vec![Binder::from("h".to_string()), Binder::from("t".to_string())],
        Some(TypeHintId::new("MyList")),
    );
    let anon = WhenPattern::constructor(
        ConstructorShape::unknown_data(0, 2),
        vec![Binder::from("h".to_string()), Binder::from("t".to_string())],
    );
    assert!(when_pattern_structural_eq(&hinted, &anon));
}

#[test]
fn test_when_pattern_structural_eq_different_shapes_not_equal() {
    let a = WhenPattern::constructor(
        ConstructorShape::unknown_data(0, 1),
        vec![Binder::from("x".to_string())],
    );
    let b = WhenPattern::constructor(
        ConstructorShape::unknown_data(1, 1),
        vec![Binder::from("x".to_string())],
    );
    assert!(!when_pattern_structural_eq(&a, &b));
}

#[test]
fn constr_known_pins_shape() {
    let e = PseudoExpr::constr_known(KnownConstructor::Some, vec![PseudoExpr::int(1)]);
    let PseudoExpr::Constr { tag, shape, .. } = &e else {
        panic!("expected Constr");
    };
    // Option: Some is tag 0.
    assert_eq!(*tag, 0);
    assert_eq!(shape.as_known(), Some(KnownConstructor::Some));
}

#[test]
fn option_tag_convention_is_standard_some_zero_none_one() {
    // `KnownConstructor` encodes `Option<a>` as `Some=0, None=1`. The reversed
    // Plinth/PlutusTx encoding (`None=0, Some=1`) would silently
    // misalign every synthetic `PseudoExpr::constr` site that
    // assumes this ordering.
    assert_eq!(KnownConstructor::Some.expected_tag(), 0);
    assert_eq!(KnownConstructor::Some.expected_arity(), 1);
    assert_eq!(KnownConstructor::None.expected_tag(), 1);
    assert_eq!(KnownConstructor::None.expected_arity(), 0);

    // The `PseudoExpr::some`/`none` factories agree with the enum.
    let some_expr = PseudoExpr::some(PseudoExpr::int(42));
    let PseudoExpr::Constr {
        tag: some_tag,
        shape: some_shape,
        ..
    } = &some_expr
    else {
        panic!("PseudoExpr::some should return Constr");
    };
    assert_eq!(*some_tag, 0);
    assert_eq!(some_shape.as_known(), Some(KnownConstructor::Some));

    let none_expr = PseudoExpr::none();
    let PseudoExpr::Constr {
        tag: none_tag,
        shape: none_shape,
        ..
    } = &none_expr
    else {
        panic!("PseudoExpr::none should return Constr");
    };
    assert_eq!(*none_tag, 1);
    assert_eq!(none_shape.as_known(), Some(KnownConstructor::None));
}

#[test]
fn constr_shape_known_derives_tag() {
    let shape = ConstructorShape::known(KnownConstructor::Some);
    let e = PseudoExpr::constr(shape, vec![PseudoExpr::int(1)]);
    let PseudoExpr::Constr {
        type_hint,
        tag,
        shape: out_shape,
        ..
    } = &e
    else {
        panic!("expected Constr");
    };
    assert!(type_hint.is_none());
    assert_eq!(*tag, KnownConstructor::Some.expected_tag());
    assert_eq!(*out_shape, shape);
}

#[test]
fn constr_shape_unknown_keeps_unknown_and_derives_tag() {
    let shape = ConstructorShape::unknown_data(7, 2);
    let fields = vec![PseudoExpr::int(0), PseudoExpr::int(1)];
    let e = PseudoExpr::constr(shape, fields);
    let PseudoExpr::Constr {
        tag,
        shape: out_shape,
        ..
    } = &e
    else {
        panic!("expected Constr");
    };
    assert_eq!(*tag, 7);
    assert_eq!(*out_shape, shape);
}

#[test]
fn constr_with_hint_carries_type_hint() {
    let shape = ConstructorShape::unknown_data(0, 1);
    let hint = TypeHintId::new("MyType");
    let e = PseudoExpr::constr_with_hint(shape, vec![PseudoExpr::int(1)], Some(hint.clone()));
    let PseudoExpr::Constr { type_hint, .. } = &e else {
        panic!("expected Constr");
    };
    assert_eq!(type_hint.as_ref(), Some(&hint));
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "does not match fields.len()")]
fn constr_panics_on_arity_mismatch_in_debug() {
    // Debug assertion guards against caller-built impossible nodes;
    // compiled out in release, hence the cfg gate.
    let shape = ConstructorShape::unknown_data(0, 2);
    let _ = PseudoExpr::constr(shape, vec![PseudoExpr::int(1)]);
}

#[test]
fn constructor_shape_known_pattern_derives_tag() {
    let shape = ConstructorShape::known(KnownConstructor::Cons);
    let binders = vec![
        Binder::new("h", VarId::from_raw(0)),
        Binder::new("t", VarId::from_raw(1)),
    ];
    let p = WhenPattern::constructor(shape, binders);
    let WhenPattern::Constructor {
        type_hint,
        tag,
        shape: out_shape,
        ..
    } = &p
    else {
        panic!("expected Constructor");
    };
    assert!(type_hint.is_none());
    assert_eq!(*tag, KnownConstructor::Cons.expected_tag());
    assert_eq!(*out_shape, shape);
}

#[test]
fn constructor_with_hint_carries_type_hint() {
    let shape = ConstructorShape::unknown_data(3, 0);
    let hint = TypeHintId::new("MyEnum");
    let p = WhenPattern::constructor_with_hint(shape, vec![], Some(hint.clone()));
    let WhenPattern::Constructor { type_hint, .. } = &p else {
        panic!("expected Constructor");
    };
    assert_eq!(type_hint.as_ref(), Some(&hint));
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "does not match fields.len()")]
fn constructor_panics_on_arity_mismatch_in_debug() {
    // debug_assert! is compiled out in release; gate the should_panic.
    let shape = ConstructorShape::unknown_data(0, 2);
    let _ = WhenPattern::constructor(shape, vec![]);
}

#[test]
fn constructor_known_pattern_pins_shape() {
    let binder = Binder::new("h", VarId::from_raw(0));
    let p = WhenPattern::constructor_known(KnownConstructor::Cons, vec![binder]);
    let WhenPattern::Constructor { tag, shape, .. } = &p else {
        panic!("expected Constructor");
    };
    assert_eq!(*tag, 1);
    assert_eq!(shape.as_known(), Some(KnownConstructor::Cons));
}

#[test]
fn constr_known_renders_canonical_name_for_each_variant() {
    // Round-trip through the shape's canonical name ensures rendering
    // anchors on `KnownConstructor`, not on an absent display_name.
    for kc in [
        KnownConstructor::Nil,
        KnownConstructor::Cons,
        KnownConstructor::Less,
        KnownConstructor::Equal,
        KnownConstructor::Greater,
    ] {
        let fields: Vec<PseudoExpr> = (0..kc.expected_arity())
            .map(|_| PseudoExpr::int(0))
            .collect();
        let e = PseudoExpr::constr_known(kc, fields);
        let PseudoExpr::Constr { shape, .. } = &e else {
            panic!("expected Constr");
        };
        assert_eq!(shape.pretty_name(), Some(kc.pretty_name()));
    }
}

#[test]
fn test_provenance_graph_stable_ids() {
    let expr = PseudoExpr::let_bind(
        "x",
        PseudoExpr::Delay(PBox::new(PseudoExpr::int(1))),
        PseudoExpr::Force(PBox::new(PseudoExpr::var("x"))),
    );

    let graph_a = expr.provenance_graph();
    let graph_b = expr.provenance_graph();

    assert_eq!(graph_a.root_id, graph_b.root_id);
    assert_eq!(graph_a.nodes.len(), graph_b.nodes.len());
    assert_eq!(graph_a.nodes, graph_b.nodes);
}

#[test]
fn test_provenance_graph_origin_links() {
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::var("k")));
    let graph = expr.provenance_graph();
    let root_id = graph.root_id;

    let mut origin_map = PseudoOriginMap::new();
    origin_map.insert(
        root_id,
        vec![PseudoOriginLink {
            uplc_uniq_id: 42,
            role: "term".to_string(),
            confidence: 1.0,
        }],
    );

    let with_origins = expr.provenance_graph_with_origins(&origin_map);
    let root = with_origins
        .nodes
        .iter()
        .find(|n| n.id == root_id)
        .expect("root node missing");

    assert_eq!(root.origins.len(), 1);
    assert_eq!(root.origins[0].uplc_uniq_id, 42);
}

#[test]
fn test_provenance_node_id_from_path_hash_matches_path_lookup() {
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("f")))),
        args: vec![PseudoExpr::Force(PBox::new(PseudoExpr::var("x")))].into(),
    };
    let root_hash = PseudoExpr::provenance_root_path_hash();
    let function_hash = PseudoExpr::provenance_child_path_hash(root_hash, 0);
    let delayed_body_hash = PseudoExpr::provenance_child_path_hash(function_hash, 0);
    let arg_hash = PseudoExpr::provenance_child_path_hash(root_hash, 1);
    let forced_arg_hash = PseudoExpr::provenance_child_path_hash(arg_hash, 0);

    assert_eq!(
        expr.provenance_node_id_from_path_hash(root_hash),
        expr.provenance_node_id_for_path(&[])
    );

    match &expr {
        PseudoExpr::Apply { function, args } => {
            assert_eq!(
                function.provenance_node_id_from_path_hash(function_hash),
                function.provenance_node_id_for_path(&[0])
            );
            match function.as_ref() {
                PseudoExpr::Delay(inner) => assert_eq!(
                    inner.provenance_node_id_from_path_hash(delayed_body_hash),
                    inner.provenance_node_id_for_path(&[0, 0])
                ),
                other => panic!("expected delay, got {other:?}"),
            }
            assert_eq!(
                args[0].provenance_node_id_from_path_hash(arg_hash),
                args[0].provenance_node_id_for_path(&[1])
            );
            match &args[0] {
                PseudoExpr::Force(inner) => assert_eq!(
                    inner.provenance_node_id_from_path_hash(forced_arg_hash),
                    inner.provenance_node_id_for_path(&[1, 0])
                ),
                other => panic!("expected force, got {other:?}"),
            }
        }
        other => panic!("expected apply, got {other:?}"),
    }
}
