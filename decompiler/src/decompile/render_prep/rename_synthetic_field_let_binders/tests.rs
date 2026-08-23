use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

#[test]
fn renames_field_1_48_to_redeemer_when_bound_to_script_context_redeemer() {
    // `let field_1_48 = script_context.redeemer in body[field_1_48]`
    // → `let redeemer = script_context.redeemer in body[redeemer]`.
    let sc_id = VarId::new(6000);
    let f_id = VarId::new(6001);
    let body_ref = PseudoExpr::var_with_id("field_1_48", f_id);
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", sc_id)],
        body: PBox::new(PseudoExpr::Let {
            name: "field_1_48".to_string(),
            id: Some(f_id),
            value: PBox::new(PseudoExpr::FieldAccess {
                record: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
                selector: FieldSelector::NamedField("redeemer".to_string()),
            }),
            body: PBox::new(body_ref),
        }),
    };

    let renamed = rename_synthetic_field_let_binders(expr);
    let PseudoExpr::Lambda { body, .. } = renamed else {
        panic!("expected outer Lambda");
    };
    let body = body.into_inner();
    let PseudoExpr::Let {
        name, body: inner, ..
    } = body
    else {
        panic!("expected Let, got {:?}", body);
    };
    assert_eq!(name, "redeemer", "let binder must be renamed to `redeemer`");
    // Var reference in body must use the new name.
    let inner = inner.into_inner();
    let PseudoExpr::Var {
        name: ref_name,
        id: ref_id,
    } = inner
    else {
        panic!("expected Var, got {:?}", inner);
    };
    assert_eq!(ref_name, "redeemer", "Var reference must use the new name");
    assert_eq!(ref_id, Some(f_id), "VarId preserved");
}

#[test]
fn renames_field_1_to_tx_info() {
    let sc_id = VarId::new(6010);
    let f_id = VarId::new(6011);
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", sc_id)],
        body: PBox::new(PseudoExpr::Let {
            name: "field_1".to_string(),
            id: Some(f_id),
            value: PBox::new(PseudoExpr::FieldAccess {
                record: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
                selector: FieldSelector::NamedField("tx_info".to_string()),
            }),
            body: PBox::new(PseudoExpr::var_with_id("field_1", f_id)),
        }),
    };

    let renamed = rename_synthetic_field_let_binders(expr);
    let PseudoExpr::Lambda { body, .. } = renamed else {
        panic!()
    };
    let PseudoExpr::Let { name, .. } = body.into_inner() else {
        panic!()
    };
    assert_eq!(name, "tx_info");
}

#[test]
fn renames_field_for_script_info() {
    let sc_id = VarId::new(6020);
    let f_id = VarId::new(6021);
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", sc_id)],
        body: PBox::new(PseudoExpr::Let {
            name: "field_2_99".to_string(),
            id: Some(f_id),
            value: PBox::new(PseudoExpr::FieldAccess {
                record: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
                selector: FieldSelector::NamedField("script_info".to_string()),
            }),
            body: PBox::new(PseudoExpr::var_with_id("field_2_99", f_id)),
        }),
    };

    let renamed = rename_synthetic_field_let_binders(expr);
    let PseudoExpr::Lambda { body, .. } = renamed else {
        panic!()
    };
    let PseudoExpr::Let { name, .. } = body.into_inner() else {
        panic!()
    };
    assert_eq!(name, "script_info");
}

#[test]
fn does_not_rename_non_synthetic_binder() {
    // `let my_redeemer = script_context.redeemer in body` — user-named
    // binder, leave alone.
    let sc_id = VarId::new(6030);
    let f_id = VarId::new(6031);
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", sc_id)],
        body: PBox::new(PseudoExpr::Let {
            name: "my_redeemer".to_string(),
            id: Some(f_id),
            value: PBox::new(PseudoExpr::FieldAccess {
                record: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
                selector: FieldSelector::NamedField("redeemer".to_string()),
            }),
            body: PBox::new(PseudoExpr::var_with_id("my_redeemer", f_id)),
        }),
    };

    let renamed = rename_synthetic_field_let_binders(expr);
    let PseudoExpr::Lambda { body, .. } = renamed else {
        panic!()
    };
    let PseudoExpr::Let { name, .. } = body.into_inner() else {
        panic!()
    };
    assert_eq!(name, "my_redeemer", "user binder name preserved");
}

#[test]
fn does_not_rename_for_unknown_field() {
    // Field name not in {tx_info, redeemer, script_info} — leave alone.
    let sc_id = VarId::new(6040);
    let f_id = VarId::new(6041);
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", sc_id)],
        body: PBox::new(PseudoExpr::Let {
            name: "field_5".to_string(),
            id: Some(f_id),
            value: PBox::new(PseudoExpr::FieldAccess {
                record: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
                selector: FieldSelector::NamedField("some_user_field".to_string()),
            }),
            body: PBox::new(PseudoExpr::var_with_id("field_5", f_id)),
        }),
    };

    let renamed = rename_synthetic_field_let_binders(expr);
    let PseudoExpr::Lambda { body, .. } = renamed else {
        panic!()
    };
    let PseudoExpr::Let { name, .. } = body.into_inner() else {
        panic!()
    };
    assert_eq!(
        name, "field_5",
        "unknown field name leaves synthetic alias alone"
    );
}

#[test]
fn does_not_rename_when_target_name_already_in_scope() {
    // `let redeemer = ...; let field_1 = script_context.redeemer in ...`
    // — `redeemer` already exists in scope, so renaming would shadow
    // and collide. Skip.
    let sc_id = VarId::new(6050);
    let outer_redeemer_id = VarId::new(6051);
    let synth_id = VarId::new(6052);

    let inner = PseudoExpr::Let {
        name: "field_1".to_string(),
        id: Some(synth_id),
        value: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
            selector: FieldSelector::NamedField("redeemer".to_string()),
        }),
        body: PBox::new(PseudoExpr::var_with_id("field_1", synth_id)),
    };
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", sc_id)],
        body: PBox::new(PseudoExpr::Let {
            name: "redeemer".to_string(),
            id: Some(outer_redeemer_id),
            value: PBox::new(PseudoExpr::int(0)),
            body: PBox::new(inner),
        }),
    };

    let renamed = rename_synthetic_field_let_binders(expr);
    let PseudoExpr::Lambda { body, .. } = renamed else {
        panic!()
    };
    let PseudoExpr::Let {
        name: outer,
        body: inner,
        ..
    } = body.into_inner()
    else {
        panic!()
    };
    assert_eq!(outer, "redeemer");
    let PseudoExpr::Let {
        name: inner_name, ..
    } = inner.into_inner()
    else {
        panic!()
    };
    assert_eq!(inner_name, "field_1", "collision must prevent rename");
}
