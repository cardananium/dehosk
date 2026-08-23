use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

#[test]
fn renames_param_never_referenced_in_body() {
    // fn(__2) { 42 } — `__2` never referenced → fn(_) { 42 }
    let p_id = VarId::fresh_binding();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("__2", p_id)],
        body: PBox::new(PseudoExpr::int(42)),
    };
    let renamed = rename_unused_lambda_params(expr);
    let PseudoExpr::Lambda { params, .. } = renamed else {
        panic!("expected Lambda");
    };
    assert_eq!(params[0].as_str(), "_");
    // Semantic name preserved so tracing can still recover the
    // original identity.
    assert_eq!(params[0].semantic_name(), "__2");
    // VarId unchanged (scope integrity).
    assert_eq!(params[0].id, p_id);
}

#[test]
fn keeps_param_that_is_referenced() {
    // fn(x) { x } — `x` IS referenced → fn(x) { x }
    let p_id = VarId::fresh_binding();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("x", p_id)],
        body: PBox::new(PseudoExpr::var_with_id("x", p_id)),
    };
    let renamed = rename_unused_lambda_params(expr);
    let PseudoExpr::Lambda { params, .. } = renamed else {
        panic!("expected Lambda");
    };
    assert_eq!(params[0].as_str(), "x");
}

#[test]
fn mixed_used_and_unused_placeholder_params() {
    // fn(used, __2) { used } — only the unused placeholder is renamed
    let used_id = VarId::fresh_binding();
    let dead_id = VarId::fresh_binding();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("used", used_id), Binder::new("__2", dead_id)],
        body: PBox::new(PseudoExpr::var_with_id("used", used_id)),
    };
    let renamed = rename_unused_lambda_params(expr);
    let PseudoExpr::Lambda { params, .. } = renamed else {
        panic!("expected Lambda");
    };
    assert_eq!(params[0].as_str(), "used");
    assert_eq!(params[1].as_str(), "_");
}

#[test]
fn preserves_semantic_names_even_when_unused() {
    // fn(redeemer, script_context) { foo(redeemer) } — script_context
    // is unused but has a semantic name; leave it alone. The user
    // (or the validator-shape wrap) chose that name deliberately.
    let r_id = VarId::fresh_binding();
    let sc_id = VarId::fresh_binding();
    let expr = PseudoExpr::Lambda {
        params: vec![
            Binder::new("redeemer", r_id),
            Binder::new("script_context", sc_id),
        ],
        body: PBox::new(PseudoExpr::var_with_id("redeemer", r_id)),
    };
    let renamed = rename_unused_lambda_params(expr);
    let PseudoExpr::Lambda { params, .. } = renamed else {
        panic!("expected Lambda");
    };
    assert_eq!(params[0].as_str(), "redeemer");
    assert_eq!(params[1].as_str(), "script_context");
}

#[test]
fn keeps_placeholder_param_when_only_name_only_ref_exists() {
    // fn(__7) { Var { name: "__7", id: None } } — body has a
    // name-only ref to the param. Use-count via VarId says 0, but
    // the name-only counter sees 1. The binder must NOT be
    // renamed to `_` (that would strand the name-only ref).
    let p_id = VarId::fresh_binding();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("__7", p_id)],
        body: PBox::new(PseudoExpr::Var {
            name: "__7".to_string(),
            id: None,
        }),
    };
    let renamed = rename_unused_lambda_params(expr);
    let PseudoExpr::Lambda { params, .. } = renamed else {
        panic!("expected Lambda")
    };
    assert_eq!(
        params[0].as_str(),
        "__7",
        "name-only ref must keep the binder; if renamed to `_` the body's `Var{{name:\"__7\"}}` would strand."
    );
}

#[test]
fn renames_unused_pair_binder_in_when_clause() {
    // when X is { Pair(__7, used) -> used } — only __7 (placeholder
    // and unused) collapses to `_`.
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    let dead_id = VarId::fresh_binding();
    let used_id = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Pair(Binder::new("__7", dead_id), Binder::new("used", used_id)),
            PseudoExpr::var_with_id("used", used_id),
        )],
    };
    let renamed = rename_unused_lambda_params(expr);
    let PseudoExpr::When { clauses, .. } = renamed else {
        panic!("expected When")
    };
    let WhenPattern::Pair(a, b) = &clauses[0].pattern else {
        panic!("expected Pair pattern")
    };
    assert_eq!(a.as_str(), "_");
    assert_eq!(b.as_str(), "used");
}

#[test]
fn renames_unused_constructor_field_in_when_clause() {
    // when X is { Constr<0>(__1, used) -> used } — only __1 collapses.
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;
    let dead_id = VarId::fresh_binding();
    let used_id = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![Binder::new("__1", dead_id), Binder::new("used", used_id)],
                shape: ConstructorShape::unknown_data(0, 2),
            },
            PseudoExpr::var_with_id("used", used_id),
        )],
    };
    let renamed = rename_unused_lambda_params(expr);
    let PseudoExpr::When { clauses, .. } = renamed else {
        panic!("expected When")
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected Constructor pattern")
    };
    assert_eq!(fields[0].as_str(), "_");
    assert_eq!(fields[1].as_str(), "used");
}

/// Under a `type_hint`, common-word `payload` / `variant`
/// survive; `field_N` / `arg_N` and the naming-pass shapes
/// (`__N`, `x_N`) still collapse.
#[test]
fn keeps_payload_variant_under_type_hint() {
    use crate::decompile::TypeHintId;
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;
    let payload_id = VarId::fresh_binding();
    let variant_id = VarId::fresh_binding();
    let field_id = VarId::fresh_binding();
    let arg_id = VarId::fresh_binding();
    let underscore_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let used_id = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Constructor {
                type_hint: Some(TypeHintId::new("MyAdt")),
                tag: 0,
                fields: vec![
                    Binder::new("payload", payload_id), // common-word; KEEP under type_hint
                    Binder::new("variant", variant_id), // common-word; KEEP under type_hint
                    Binder::new("field_0", field_id),   // synthetic; still collapses
                    Binder::new("arg_2", arg_id),       // synthetic; still collapses
                    Binder::new("__7", underscore_id),  // naming-pass; still collapses
                    Binder::new("x_3", x_id),           // naming-pass; still collapses
                    Binder::new("used", used_id),
                ],
                shape: ConstructorShape::unknown_data(0, 7),
            },
            PseudoExpr::var_with_id("used", used_id),
        )],
    };
    let renamed = rename_unused_lambda_params(expr);
    let PseudoExpr::When { clauses, .. } = renamed else {
        panic!("When")
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("Constructor")
    };
    assert_eq!(fields[0].as_str(), "payload");
    assert_eq!(fields[1].as_str(), "variant");
    assert_eq!(
        fields[2].as_str(),
        "_",
        "field_N collapses (cardano-ctx synthetic)"
    );
    assert_eq!(
        fields[3].as_str(),
        "_",
        "arg_N collapses (cardano-ctx synthetic)"
    );
    assert_eq!(fields[4].as_str(), "_", "__N collapses (naming-pass)");
    assert_eq!(fields[5].as_str(), "_", "x_N collapses (naming-pass)");
    assert_eq!(fields[6].as_str(), "used");
}

/// Without a type_hint, common-word placeholders DO collapse.
#[test]
fn collapses_payload_when_no_type_hint() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;
    let payload_id = VarId::fresh_binding();
    let used_id = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Constructor {
                type_hint: None, // ← no blueprint metadata
                tag: 0,
                fields: vec![Binder::new("payload", payload_id)],
                shape: ConstructorShape::unknown_data(0, 1),
            },
            PseudoExpr::var_with_id("used", used_id),
        )],
    };
    let renamed = rename_unused_lambda_params(expr);
    let PseudoExpr::When { clauses, .. } = renamed else {
        panic!("When")
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("Constructor")
    };
    assert_eq!(fields[0].as_str(), "_");
}

#[test]
fn prefix_marks_unused_nonplaceholder_constructor_field() {
    // when X is { Spending(output_reference, datum) -> datum } —
    // `output_reference` (non-placeholder, unused) → `_output_reference`;
    // `datum` is used → kept.
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;
    let or_id = VarId::fresh_binding();
    let datum_id = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![
                    Binder::new("output_reference", or_id),
                    Binder::new("datum", datum_id),
                ],
                shape: ConstructorShape::unknown_data(0, 2),
            },
            PseudoExpr::var_with_id("datum", datum_id),
        )],
    };
    let out = underscore_unused_pattern_binders(expr);
    let PseudoExpr::When { clauses, .. } = out else {
        panic!("When")
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("Constructor")
    };
    assert_eq!(fields[0].as_str(), "_output_reference");
    assert_eq!(
        fields[0].semantic_name(),
        "output_reference",
        "name preserved"
    );
    assert_eq!(fields[1].as_str(), "datum");
}

#[test]
fn prefix_leaves_lambda_params_and_placeholders_alone() {
    // Lambda param (non-placeholder, unused) → untouched (not the prefix
    // pass's job); a placeholder field stays for the blank pass.
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;
    let lam_id = VarId::fresh_binding();
    let field_id = VarId::fresh_binding();
    let used_id = VarId::fresh_binding();
    // fn(output_reference) { when y is { Ctor(field_0, used) -> used } }
    let inner_when = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("y")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![
                    Binder::new("field_0", field_id),
                    Binder::new("used", used_id),
                ],
                shape: ConstructorShape::unknown_data(0, 2),
            },
            PseudoExpr::var_with_id("used", used_id),
        )],
    };
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("output_reference", lam_id)],
        body: PBox::new(inner_when),
    };
    let out = underscore_unused_pattern_binders(expr);
    let PseudoExpr::Lambda { params, body } = out else {
        panic!("Lambda")
    };
    assert_eq!(
        params[0].as_str(),
        "output_reference",
        "lambda param untouched"
    );
    let PseudoExpr::When { clauses, .. } = body.into_inner() else {
        panic!("When")
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("Constructor")
    };
    // `field_0` is placeholder-shaped → left for the blank pass (NOT prefixed).
    assert_eq!(fields[0].as_str(), "field_0");
    assert_eq!(fields[1].as_str(), "used");
}

#[test]
fn prefix_is_idempotent() {
    // Running twice must not double-prefix `_output_reference` → `__…`.
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;
    let or_id = VarId::fresh_binding();
    let used_id = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![Binder::new("output_reference", or_id)],
                shape: ConstructorShape::unknown_data(0, 1),
            },
            PseudoExpr::var_with_id("used", used_id),
        )],
    };
    let once = underscore_unused_pattern_binders(expr);
    let twice = underscore_unused_pattern_binders(once);
    let PseudoExpr::When { clauses, .. } = twice else {
        panic!("When")
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("Constructor")
    };
    assert_eq!(fields[0].as_str(), "_output_reference");
}

#[test]
fn nested_lambda_with_outer_param_used_in_inner_body() {
    // fn(outer) { fn(__7) { outer } } — outer is used inside the
    // inner body, inner placeholder (__7) is unused.
    let outer_id = VarId::fresh_binding();
    let inner_id = VarId::fresh_binding();
    let inner = PseudoExpr::Lambda {
        params: vec![Binder::new("__7", inner_id)],
        body: PBox::new(PseudoExpr::var_with_id("outer", outer_id)),
    };
    let outer = PseudoExpr::Lambda {
        params: vec![Binder::new("outer", outer_id)],
        body: PBox::new(inner),
    };
    let renamed = rename_unused_lambda_params(outer);
    let PseudoExpr::Lambda { params, body } = renamed else {
        panic!("expected outer Lambda");
    };
    assert_eq!(params[0].as_str(), "outer");
    let PseudoExpr::Lambda { params: ip, .. } = body.into_inner() else {
        panic!("expected inner Lambda");
    };
    assert_eq!(ip[0].as_str(), "_");
}
