use super::Simplifier;
use crate::builtins::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

#[test]
fn test_collect_index_access_counts_counts_exact_ref_under_same_name_foreign_binder() {
    let collection_id = VarId::new(904);
    let foreign_param_id = VarId::new(905);
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("fields", foreign_param_id)],
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::var_with_id("fields", collection_id)),
                    index: 1,
                },
                PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::compat_var("fields")),
                    index: 2,
                },
            ]
            .into(),
        )),
    };

    let counts = Simplifier::collect_index_access_counts(&expr, "fields", Some(collection_id));

    assert_eq!(counts.get(&1), Some(&1));
    assert!(
        !counts.contains_key(&2),
        "same-name foreign binder should block compat/name fallback refs, got: {counts:?}"
    );
}

#[test]
fn test_replace_index_access_replaces_exact_ref_under_same_name_foreign_binder() {
    let collection_id = VarId::new(906);
    let foreign_param_id = VarId::new(907);
    let replacement_id = VarId::new(908);
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("fields", foreign_param_id)],
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::var_with_id("fields", collection_id)),
                    index: 1,
                },
                PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::compat_var("fields")),
                    index: 1,
                },
            ]
            .into(),
        )),
    };

    let replaced = Simplifier::replace_index_access(
        expr,
        "fields",
        Some(collection_id),
        1,
        "field_1",
        replacement_id,
    );

    assert!(
        matches!(
            &replaced,
            PseudoExpr::Lambda { body, .. }
                if matches!(
                    body.as_ref(),
                    PseudoExpr::Tuple(items)
                        if matches!(&items[0], PseudoExpr::Var { name, id } if name == "field_1" && *id == Some(replacement_id))
                            && matches!(&items[1], PseudoExpr::IndexAccess { collection, index }
                                if *index == 1
                                    && matches!(collection.as_ref(), PseudoExpr::Var { name, id } if name == "fields" && id.get().is_none()))
                )
        ),
        "expected exact ref replacement while compat fallback stayed shadowed, got: {replaced:?}"
    );
}

#[test]
fn test_replace_index_access_honors_when_pattern_shadow_for_name_fallback() {
    let foreign_pattern_id = VarId::new(909);
    let replacement_id = VarId::new(910);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Unit),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Var(Binder::new("fields", foreign_pattern_id)),
            PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::compat_var("fields")),
                index: 0,
            },
        )],
    };

    let replaced =
        Simplifier::replace_index_access(expr, "fields", None, 0, "field_0", replacement_id);

    assert!(
        matches!(
            &replaced,
            PseudoExpr::When { clauses, .. }
                if matches!(
                    &clauses[0].body,
                    PseudoExpr::IndexAccess { collection, index }
                        if *index == 0
                            && matches!(
                                collection.as_ref(),
                                PseudoExpr::Var { name, id }
                                    if name == "fields" && id.get().is_none()
                            )
                )
        ),
        "when pattern binder should shadow name-fallback index replacement, got: {replaced:?}"
    );
}

#[test]
fn test_list_access_usage_by_id_ignores_same_name_foreign_head_tail() {
    let target_id = VarId::new(911);
    let foreign_id = VarId::new(912);
    let foreign_expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::var_with_id("xs", foreign_id)),
                index: 0,
            },
            PseudoExpr::builtin_id(
                BuiltinId::ListTail,
                vec![PseudoExpr::var_with_id("xs", foreign_id)],
            ),
        ]
        .into(),
    );
    let target_expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::field_access(PseudoExpr::var_with_id("xs", target_id), "head"),
            PseudoExpr::builtin_id(
                BuiltinId::ListTail,
                vec![PseudoExpr::var_with_id("xs", target_id)],
            ),
        ]
        .into(),
    );

    assert_eq!(
        Simplifier::list_access_usage_by_id(&foreign_expr, "xs", Some(target_id)),
        (false, false)
    );
    assert_eq!(
        Simplifier::list_access_usage_by_id(&target_expr, "xs", Some(target_id)),
        (true, true)
    );
    assert_eq!(
        Simplifier::list_access_usage(&target_expr, "xs"),
        (true, true)
    );
    assert!(Simplifier::contains_head_access(&target_expr, "xs"));
}

#[test]
fn test_replace_head_access_by_id_leaves_foreign_same_name_refs() {
    let target_id = VarId::new(913);
    let foreign_id = VarId::new(914);
    let replacement_id = VarId::new(915);
    let expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::var_with_id("xs", foreign_id)),
                index: 0,
            },
            PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::var_with_id("xs", target_id)),
                index: 0,
            },
            PseudoExpr::field_access(PseudoExpr::var_with_id("xs", foreign_id), "head"),
        ]
        .into(),
    );

    let replaced = Simplifier::replace_head_access_by_id(
        expr,
        "xs",
        Some(target_id),
        "head_alias",
        replacement_id,
    );

    assert!(
        matches!(
            &replaced,
            PseudoExpr::Tuple(items)
                if matches!(
                    &items[0],
                    PseudoExpr::IndexAccess { collection, index }
                        if *index == 0
                            && matches!(collection.as_ref(), PseudoExpr::Var { name, id } if name == "xs" && *id == Some(foreign_id))
                )
                && matches!(&items[1], PseudoExpr::Var { name, id } if name == "head_alias" && *id == Some(replacement_id))
                && matches!(
                    &items[2],
                    PseudoExpr::FieldAccess { record, selector }
                        if selector.is_list_head()
                            && matches!(record.as_ref(), PseudoExpr::Var { name, id } if name == "xs" && *id == Some(foreign_id))
                )
        ),
        "expected only the exact target head access to be replaced, got: {replaced:?}"
    );
}

#[test]
fn test_replace_tail_access_by_id_leaves_foreign_same_name_refs() {
    let target_id = VarId::new(916);
    let foreign_id = VarId::new(917);
    let replacement_id = VarId::new(918);
    let expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::builtin_id(
                BuiltinId::ListTail,
                vec![PseudoExpr::var_with_id("xs", foreign_id)],
            ),
            PseudoExpr::builtin_id(
                BuiltinId::ListTail,
                vec![PseudoExpr::var_with_id("xs", target_id)],
            ),
        ]
        .into(),
    );

    let replaced = Simplifier::replace_tail_access_by_id(
        expr,
        "xs",
        Some(target_id),
        "tail_alias",
        replacement_id,
    );

    assert!(
        matches!(
            &replaced,
            PseudoExpr::Tuple(items)
                if matches!(
                    &items[0],
                    PseudoExpr::BuiltinCall { name, args }
                        if *name == BuiltinId::ListTail
                            && matches!(&args[0], PseudoExpr::Var { name, id } if name == "xs" && *id == Some(foreign_id))
                )
                && matches!(&items[1], PseudoExpr::Var { name, id } if name == "tail_alias" && *id == Some(replacement_id))
        ),
        "expected only the exact target tail access to be replaced, got: {replaced:?}"
    );
}

#[test]
fn test_replace_head_access_preserves_replacement_id() {
    let replacement_id = VarId::new(900);
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::var("xs")),
        index: 0,
    };

    let replaced = Simplifier::replace_head_access(expr, "xs", "head_alias", replacement_id);

    assert!(
        matches!(
            replaced,
            PseudoExpr::Var { name, id, .. }
                if name == "head_alias" && id == Some(replacement_id)
        ),
        "expected replacement var to preserve the supplied VarId"
    );
}

#[test]
fn test_replace_tail_access_preserves_replacement_id() {
    let replacement_id = VarId::new(901);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("List.tail")),
        args: vec![PseudoExpr::var("xs")].into(),
    };

    let replaced = Simplifier::replace_tail_access(expr, "xs", "tail_alias", replacement_id);

    assert!(
        matches!(
            replaced,
            PseudoExpr::Var { name, id, .. }
                if name == "tail_alias" && id == Some(replacement_id)
        ),
        "expected replacement var to preserve the supplied VarId"
    );
}

#[test]
fn test_replace_index_access_preserves_replacement_id() {
    let replacement_id = VarId::new(902);
    let collection_id = VarId::new(903);
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::var_with_id("fields", collection_id)),
        index: 1,
    };

    let replaced = Simplifier::replace_index_access(
        expr,
        "fields",
        Some(collection_id),
        1,
        "field_1",
        replacement_id,
    );

    assert!(
        matches!(
            replaced,
            PseudoExpr::Var { name, id, .. } if name == "field_1" && id == Some(replacement_id)
        ),
        "expected index-access replacement var to preserve the supplied VarId"
    );
}
