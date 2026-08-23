use super::*;
use crate::decompile::ref_retarget::refs_need_retarget_by_scope;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;

/// After `introduce_field_index_aliases` mints a `field_N` binder
/// from a Var-rooted `.fields` access, `var_kinds.kind_annotations`
/// must hold `VarKind::FieldIndexAlias { parent, index }` for that
/// binder's VarId.
#[test]
fn mint_site_tags_field_index_alias_with_parent_id() {
    let mut simplifier = Simplifier::with_safe_mode(false);

    let parent_id = VarId::fresh_binding();
    let fields_id = VarId::fresh_binding();
    let name = "fields_2";
    let value = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::Var {
            name: "ctx".to_string(),
            id: Some(parent_id),
        }),
        selector: FieldSelector::NamedField("fields".to_string()),
    };

    // Body uses fields_2[0] once, meeting `threshold = 1` for a
    // `.fields` binding, so the pass creates `field_0 = fields_2[0]`.
    let body = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::Var {
            name: name.to_string(),
            id: Some(fields_id),
        }),
        index: 0,
    };

    // Register the `fields_2` name → id mapping so
    // `binding_id(name, None)` returns `fields_id`.
    simplifier
        .naming
        .name_to_id
        .insert(name.to_string(), fields_id);

    let _out = simplifier.introduce_field_index_aliases(name, &value, body);

    // kind_annotations should have ONE entry whose kind is
    // FieldIndexAlias with parent=parent_id, index=0.
    let annotations = &simplifier.var_kinds.kind_annotations;
    let matching: Vec<_> = annotations
        .iter()
        .filter(|(_, kind)| {
            matches!(kind, VarKind::FieldIndexAlias { parent, index }
                if *parent == parent_id && *index == 0)
        })
        .collect();
    assert_eq!(
        matching.len(),
        1,
        "expected exactly one FieldIndexAlias annotation, got {} total (all: {:?})",
        annotations.len(),
        annotations,
    );
    // Sanity: the keyed VarId must be a *fresh* id (not parent, not fields_id).
    let (minted_id, _) = matching[0];
    assert_ne!(*minted_id, parent_id);
    assert_ne!(*minted_id, fields_id);
}

/// Negative: when the `.fields` source is NOT a Var
/// (e.g. nested expression), the pass doesn't know the parent
/// VarId and must not insert a FieldIndexAlias annotation.
#[test]
fn mint_site_skips_annotation_when_source_not_a_var() {
    let mut simplifier = Simplifier::with_safe_mode(false);

    let fields_id = VarId::fresh_binding();
    let name = "fields_3";
    // A let-binding source, not a plain Var: parent_id is None.
    let value = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::Let {
            name: "tmp".to_string(),
            id: Some(VarId::fresh_binding()),
            value: PBox::new(PseudoExpr::Unit),
            body: PBox::new(PseudoExpr::Var {
                name: "tmp".to_string(),
                id: Some(VarId::fresh_binding()),
            }),
        }),
        selector: FieldSelector::NamedField("fields".to_string()),
    };
    let body = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::Var {
            name: name.to_string(),
            id: Some(fields_id),
        }),
        index: 0,
    };
    simplifier
        .naming
        .name_to_id
        .insert(name.to_string(), fields_id);

    let _out = simplifier.introduce_field_index_aliases(name, &value, body);

    // No mint-site annotation recorded.
    assert!(
        simplifier.var_kinds.kind_annotations.is_empty(),
        "expected empty kind_annotations, got {:?}",
        simplifier.var_kinds.kind_annotations,
    );
}

#[test]
fn field_binding_source_preserves_record_var_id_over_name_lookup() {
    let mut simplifier = Simplifier::with_safe_mode(false);

    let parent_id = VarId::fresh_binding();
    let stale_parent_id = VarId::fresh_binding();
    let fields_id = VarId::fresh_binding();
    let name = "fields_4";
    let value = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::Var {
            name: "ctx".to_string(),
            id: Some(parent_id),
        }),
        selector: FieldSelector::NamedField("fields".to_string()),
    };
    let body = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::Var {
            name: name.to_string(),
            id: Some(fields_id),
        }),
        index: 0,
    };

    simplifier
        .naming
        .name_to_id
        .insert("ctx".to_string(), stale_parent_id);
    simplifier
        .naming
        .name_to_id
        .insert(name.to_string(), fields_id);

    let _out = simplifier.introduce_field_index_aliases(name, &value, body);

    let tracked_source = simplifier
        .constructors
        .fields_bindings
        .get(fields_id)
        .expect("fields binding should be tracked by the fields let id");
    assert!(
        matches!(
            tracked_source,
            PseudoExpr::Var { name, id } if name == "ctx" && *id == Some(parent_id)
        ),
        "fields binding source must keep the record VarId from the value, got: {tracked_source:?}"
    );
}

#[test]
fn field_index_alias_freshens_display_name_against_existing_field_let() {
    let mut simplifier = Simplifier::with_safe_mode(false);

    let parent_id = VarId::fresh_binding();
    let fields_id = VarId::fresh_binding();
    let existing_field_id = VarId::fresh_binding();
    let name = "fields_4";
    let value = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::Var {
            name: "ctx".to_string(),
            id: Some(parent_id),
        }),
        selector: FieldSelector::NamedField("fields".to_string()),
    };
    let body = PseudoExpr::Let {
        name: "field_0".to_string(),
        id: Some(existing_field_id),
        value: PBox::new(PseudoExpr::Int(1.into())),
        body: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::var_with_id(name, fields_id)),
            index: 0,
        }),
    };

    simplifier
        .naming
        .name_to_id
        .insert(name.to_string(), fields_id);

    let out = simplifier.introduce_field_index_aliases(name, &value, body);

    let PseudoExpr::Let {
        name: alias_name,
        id: Some(alias_id),
        body,
        ..
    } = &out
    else {
        panic!("expected generated field alias let, got: {out:?}");
    };
    assert_eq!(alias_name, "field_0_1");

    let PseudoExpr::Let {
        name: inner_name,
        id: Some(inner_id),
        body: inner_body,
        ..
    } = body.as_ref()
    else {
        panic!("expected existing field_0 let to remain inside alias, got: {body:?}");
    };
    assert_eq!(inner_name, "field_0");
    assert_eq!(*inner_id, existing_field_id);
    assert!(
        matches!(
            inner_body.as_ref(),
            PseudoExpr::Var { name, id } if name == "field_0_1" && *id == Some(*alias_id)
        ),
        "expected rewritten index access to point at freshened alias, got: {inner_body:?}"
    );

    assert_unique_let_names(&out);
    assert!(
        !refs_need_retarget_by_scope(&out),
        "fresh alias name should not strand refs by scope: {out:?}"
    );
}

struct LetNameCollector {
    names: Vec<String>,
}

impl ExprVisitor for LetNameCollector {
    fn visit_let_pre(&mut self, name: &str) {
        self.names.push(name.to_string());
    }
}

fn assert_unique_let_names(expr: &PseudoExpr) {
    let mut collector = LetNameCollector { names: Vec::new() };
    collector.walk(expr);
    let mut seen = std::collections::HashSet::new();
    for name in collector.names {
        assert!(seen.insert(name.clone()), "duplicate let name: {name}");
    }
}
