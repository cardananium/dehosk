use super::*;
use crate::pseudo::ast::PseudoType;

/// Compilable-data-access ON. The pass early-returns unchanged under
/// [`RenderCtx::default`], which is the OFF default.
fn on() -> RenderCtx {
    RenderCtx::default().with_compilable_data_access(true)
}

fn tag_access(record: PseudoExpr) -> PseudoExpr {
    PseudoExpr::field_access(record, "tag".to_string())
}

fn fields_access(record: PseudoExpr) -> PseudoExpr {
    PseudoExpr::field_access(record, "fields".to_string())
}

fn is_un_constr_pair(expr: &PseudoExpr, expect_fst: bool) -> bool {
    if let PseudoExpr::FieldAccess { record, selector } = expr {
        let selector_ok = if expect_fst {
            matches!(selector, FieldSelector::PairFst)
        } else {
            matches!(selector, FieldSelector::PairSnd)
        };
        let record_ok = matches!(
            record.as_ref(),
            PseudoExpr::BuiltinCall {
                name: BuiltinId::DataUnConstr,
                ..
            }
        );
        selector_ok && record_ok
    } else {
        false
    }
}

#[test]
fn rewrites_tag_on_untyped_record() {
    // Untyped `Var` → type_resolution() is Unknown → FIRE.
    let input = tag_access(PseudoExpr::var("redeemer"));
    let out = lower_constr_field_sugar(input, &on());
    assert!(
        is_un_constr_pair(&out, /* expect_fst */ true),
        "tag should lower to builtin.un_constr_data(...).1st, got: {out:?}"
    );
}

#[test]
fn rewrites_fields_on_untyped_record() {
    let input = fields_access(PseudoExpr::var("redeemer"));
    let out = lower_constr_field_sugar(input, &on());
    assert!(
        is_un_constr_pair(&out, /* expect_fst */ false),
        "fields should lower to builtin.un_constr_data(...).2nd, got: {out:?}"
    );
}

#[test]
fn rewrites_fields_on_data_typed_record() {
    // `Data(_)` literal → type_resolution() is `Data` → FIRE.
    let data_lit = PseudoExpr::Data(Box::new(crate::pseudo::ast::PseudoData::Integer(
        num_bigint::BigInt::from(0),
    )));
    let input = fields_access(data_lit);
    let out = lower_constr_field_sugar(input, &on());
    assert!(
        is_un_constr_pair(&out, false),
        "fields on a Data-typed record should lower, got: {out:?}"
    );
}

#[test]
fn gate_b_skips_concrete_named_record() {
    // GATE B: a real (non-stub) blueprint `Named` record carrying a
    // genuine field titled `tag` must NOT be rewritten.
    let named = PseudoType::Named("Redeemer".to_string());
    assert!(
        !gate_b_allows_named(&named),
        "a concrete blueprint Named type must be SKIPPED"
    );
}

#[test]
fn gate_b_fires_on_stub_named_record() {
    // A synthetic stub `Named` is not a real record — FIRE.
    let stub = PseudoType::Named("Unknown_S_10_0".to_string());
    assert!(
        gate_b_allows_named(&stub),
        "a synthetic stub Named type must FIRE"
    );
    let stub_e = PseudoType::Named("Unknown_E_0_5".to_string());
    assert!(gate_b_allows_named(&stub_e), "Unknown_E_* stub must FIRE");
}

#[test]
fn gate_b_fires_on_data_and_unknown() {
    assert!(gate_b_allows_type(Some(&PseudoType::Data)));
    assert!(gate_b_allows_type(None));
}

/// Runs GATE B against an explicit `PseudoType::Named`, duplicating the
/// `Named` arm of `gate_b_allows`.
fn gate_b_allows_named(named: &PseudoType) -> bool {
    gate_b_allows_type(Some(named))
}

/// Runs GATE B against an explicit resolved type.
fn gate_b_allows_type(ty: Option<&PseudoType>) -> bool {
    match ty {
        Some(PseudoType::Named(n)) => is_stub_type_name(n),
        _ => true,
    }
}

#[test]
fn leaves_other_named_fields_untouched() {
    // A non-tag/fields named selector is never rewritten.
    let input = PseudoExpr::field_access(PseudoExpr::var("x"), "policy_id".to_string());
    let out = lower_constr_field_sugar(input.clone(), &on());
    assert_eq!(out, input, "non-tag/fields selector must be untouched");
}

#[test]
fn default_off_is_a_noop() {
    // The default ctx has the toggle OFF, so the pass is a no-op.
    let input = tag_access(PseudoExpr::var("redeemer"));
    let out = lower_constr_field_sugar(input.clone(), &RenderCtx::default());
    assert_eq!(
        out, input,
        "with the compilable-data-access toggle OFF, `.tag` must stay the \
         readable pseudo NamedField (no un_constr_data lowering), got: {out:?}"
    );
}

#[test]
fn rewrites_nested_tag_bottom_up() {
    // `record.fields.tag` → both levels lowered.
    let input = tag_access(fields_access(PseudoExpr::var("r")));
    let out = lower_constr_field_sugar(input, &on());
    // Outer is `.1st` over un_constr_data(<lowered fields>).
    assert!(
        is_un_constr_pair(&out, true),
        "outer tag must lower: {out:?}"
    );
    if let PseudoExpr::FieldAccess { record, .. } = &out
        && let PseudoExpr::BuiltinCall { args, .. } = record.as_ref()
    {
        assert!(
            is_un_constr_pair(&args[0], false),
            "inner fields must lower too: {:?}",
            args[0]
        );
    } else {
        panic!("unexpected outer shape: {out:?}");
    }
}
