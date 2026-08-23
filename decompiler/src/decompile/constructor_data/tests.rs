use super::*;

#[test]
fn normalize_constructor_data_expr_accepts_list_cons_chain() {
    let expr = normalize_constructor_data_expr(
        PseudoExpr::Int(0.into()),
        PseudoExpr::builtin(
            "List.cons",
            vec![
                PseudoExpr::var("a"),
                PseudoExpr::builtin(
                    "List.cons",
                    vec![
                        PseudoExpr::var("b"),
                        PseudoExpr::List {
                            elements: vec![].into(),
                            tail: None,
                        },
                    ],
                ),
            ],
        ),
    );

    match expr {
        PseudoExpr::Constr { tag, fields, .. } => {
            assert_eq!(tag, 0);
            assert_eq!(fields.len(), 2);
        }
        other => panic!("expected Constr, got: {:?}", other),
    }
}

#[test]
fn rewrite_constr_exposer_wrapper_uses_constructor_owner_builtins() {
    let index_expr =
        rewrite_constr_exposer_wrapper("__constr_index_exposer", vec![PseudoExpr::var("x")])
            .expect("index exposer should rewrite");
    let fields_expr =
        rewrite_constr_exposer_wrapper("__constr_fields_exposer", vec![PseudoExpr::var("x")])
            .expect("fields exposer should rewrite");

    assert!(
        matches!(index_expr, PseudoExpr::BuiltinCall { name, .. } if name == BuiltinId::DataConstrIndex)
    );
    assert!(
        matches!(fields_expr, PseudoExpr::BuiltinCall { name, .. } if name == BuiltinId::DataConstrFields)
    );
    assert!(
        rewrite_constr_exposer_wrapper("__not_a_constr_exposer", vec![PseudoExpr::var("x")])
            .is_none()
    );
}

#[test]
fn rewrite_constr_unpack_pair_projection_handles_direct_and_tracked_subjects() {
    let direct = rewrite_constr_unpack_pair_projection(
        &PseudoExpr::builtin_id(BuiltinId::ConstrUnpack, vec![PseudoExpr::var("payload")]),
        None,
        ConstrPairProjection::Tag,
    )
    .expect("direct constr.unpack should rewrite");

    let tracked = rewrite_constr_unpack_pair_projection(
        &PseudoExpr::var("u"),
        Some(PseudoExpr::var("payload")),
        ConstrPairProjection::Fields,
    )
    .expect("tracked constr.unpack subject should rewrite");

    assert!(
        matches!(direct, PseudoExpr::FieldAccess { selector, .. } if selector.as_pretty_name() == "tag")
    );
    assert!(
        matches!(tracked, PseudoExpr::FieldAccess { selector, .. } if selector.as_pretty_name() == "fields")
    );
}

#[test]
fn constr_unpack_detection_helpers_cover_subject_and_tag_forms() {
    let unpack = PseudoExpr::builtin_id(BuiltinId::ConstrUnpack, vec![PseudoExpr::var("payload")]);
    let unpack_tag = PseudoExpr::field_access(unpack.clone(), "fst".to_string());
    let unpack_fields = PseudoExpr::field_access(unpack.clone(), "snd".to_string());

    assert!(matches!(
        extract_constr_unpack_subject(&unpack),
        Some(PseudoExpr::Var { name, .. }) if name == "payload"
    ));
    assert!(matches!(
        extract_constr_unpack_fst_subject(&unpack_tag),
        Some(PseudoExpr::Var { name, .. }) if name == "payload"
    ));
    assert_eq!(
        extract_constr_unpack_subject_var_name(&unpack),
        Some("payload")
    );
    assert!(is_constr_unpack_of_var(&unpack, "payload"));
    assert!(is_constr_unpack_snd_of_var(&unpack_fields, "payload"));
}

#[test]
fn constructor_tag_detection_helpers_cover_bare_named_and_data_forms() {
    let bare_true = PseudoExpr::constr(ConstructorShape::unknown_data(1, 0), vec![]);
    let named_false = PseudoExpr::constr_known(KnownConstructor::False, vec![]);
    let some_like = PseudoExpr::constr(
        ConstructorShape::unknown_data(0, 1),
        vec![PseudoExpr::var("x")],
    );

    assert!(is_empty_constr_tag(&bare_true, 1));
    assert!(is_known_empty_constr_tag(
        &named_false,
        KnownConstructor::False
    ));
    assert!(!is_empty_constr_tag(&some_like, 0));
    assert!(!is_known_empty_constr_tag(
        &bare_true,
        KnownConstructor::True
    ));
}

#[test]
fn semantic_constructor_helpers_cover_bool_and_option_families() {
    let bare_true = PseudoExpr::constr(ConstructorShape::unknown_data(1, 0), vec![]);
    let named_false = PseudoExpr::constr_known(KnownConstructor::False, vec![]);
    let named_none = PseudoExpr::constr_known(KnownConstructor::None, vec![]);
    let named_some =
        PseudoExpr::constr_known(KnownConstructor::Some, vec![PseudoExpr::var("payload")]);

    assert!(is_bool_true_like(&bare_true));
    assert!(is_bool_false_like(&named_false));
    assert!(is_standard_option_none_candidate(&PseudoExpr::Bool(true)));
    assert!(is_standard_option_none_candidate(&named_none));
    assert!(is_standard_option_some_candidate(&named_some));
    assert!(!is_standard_option_some_candidate(&bare_true));
    assert_eq!(
        extract_standard_option_some_fields(&named_some),
        Some(vec![PseudoExpr::var("payload")])
    );
    assert!(matches!(
        make_standard_option_none(),
        PseudoExpr::Constr {
            tag: 1,
            ref fields,
            shape: ConstructorShape::Known(KnownConstructor::None),
            ..
        } if fields.is_empty()
    ));
    assert!(matches!(
        make_standard_option_some(vec![PseudoExpr::Int(1.into())]),
        PseudoExpr::Constr {
            tag: 0,
            ref fields,
            shape: ConstructorShape::Known(KnownConstructor::Some),
            ..
        } if fields.len() == 1
    ));

    let data_some = PseudoExpr::builtin_id(
        BuiltinId::DataConstr,
        vec![
            PseudoExpr::Int(0.into()),
            PseudoExpr::List {
                elements: vec![PseudoExpr::Int(2.into())].into(),
                tail: None,
            },
        ],
    );
    assert_eq!(
        extract_standard_option_some_fields(&data_some),
        Some(vec![PseudoExpr::Int(2.into())])
    );
}

#[test]
fn constr_unpack_tag_check_helpers_cover_plain_and_expect_forms() {
    let tag_check = PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(PseudoExpr::field_access(
            PseudoExpr::builtin_id(BuiltinId::ConstrUnpack, vec![PseudoExpr::var("payload")]),
            "fst".to_string(),
        )),
        right: PBox::new(PseudoExpr::Int(2.into())),
    };
    let expect_check = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![tag_check.clone(), PseudoExpr::var("body")].into(),
    };

    assert!(matches!(
        extract_constr_unpack_tag_eq(&tag_check),
        Some((PseudoExpr::Var { name, .. }, 2)) if name == "payload"
    ));
    assert_eq!(
        extract_constr_unpack_tag_eq_var_name(&tag_check),
        Some(("payload", 2))
    );
    assert!(is_constr_unpack_tag_eq_for_var(&tag_check, "payload"));
    assert!(matches!(
        extract_expect_constr_unpack_tag(&expect_check),
        Some((2, "payload", PseudoExpr::Var { name, .. })) if name == "body"
    ));
}

#[test]
fn constr_unpack_field_helpers_cover_index_collection_and_rewrite() {
    let body = PseudoExpr::Tuple(
        vec![
            PseudoExpr::field_access(
                PseudoExpr::field_access(
                    PseudoExpr::builtin_id(
                        BuiltinId::ConstrUnpack,
                        vec![PseudoExpr::var("payload")],
                    ),
                    "snd".to_string(),
                ),
                "head".to_string(),
            ),
            PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::builtin(
                    "List.tail",
                    vec![PseudoExpr::field_access(
                        PseudoExpr::builtin_id(
                            BuiltinId::ConstrUnpack,
                            vec![PseudoExpr::var("payload")],
                        ),
                        "snd".to_string(),
                    )],
                )),
                index: 1,
            },
        ]
        .into(),
    );
    let mut indices = BTreeSet::new();

    collect_constr_unpack_field_indices(&body, "payload", &mut indices);
    let field_binders = vec!["a", "b", "c"]
        .into_iter()
        .map(Binder::synthetic)
        .collect::<Vec<_>>();
    let rewritten = rewrite_constr_unpack_field_accesses(body, "payload", 2, Some(&field_binders));

    assert_eq!(indices.into_iter().collect::<Vec<_>>(), vec![0, 2]);
    assert!(matches!(
        rewritten,
        PseudoExpr::Tuple(elements)
            if matches!(&elements[0], PseudoExpr::Var { name, id, .. }
                if name == "a" && *id == Some(field_binders[0].id))
                && matches!(&elements[1], PseudoExpr::Var { name, id, .. }
                    if name == "c" && *id == Some(field_binders[2].id))
    ));
}
