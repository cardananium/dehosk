use super::*;
use crate::decompile::ScriptVersion;
use crate::decompile::render_prep::RenderCtx;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{WhenClause, WhenPattern};

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}
fn field(record: PseudoExpr, sel: &str) -> PseudoExpr {
    PseudoExpr::FieldAccess {
        record: PBox::new(record),
        selector: FieldSelector::NamedField(sel.to_string()),
    }
}
/// `let <name>@<id> = <value> in <body>`
fn let_in(name: &str, id: u32, value: PseudoExpr, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: name.to_string(),
        id: Some(VarId::new(id)),
        value: PBox::new(value),
        body: PBox::new(body),
    }
}
fn run_v3(expr: PseudoExpr) -> PseudoExpr {
    rename_let_to_cardano_field(expr, &RenderCtx::at(Some(ScriptVersion::PlutusV3)))
}
fn let_name_and_body_subject(out: &PseudoExpr) -> (String, Option<String>) {
    let PseudoExpr::Let { name, body, .. } = out else {
        panic!("expected Let")
    };
    let subj = match body.as_ref() {
        PseudoExpr::When { subject, .. } => match subject.as_ref() {
            PseudoExpr::Var { name, .. } => Some(name.clone()),
            _ => None,
        },
        _ => None,
    };
    (name.clone(), subj)
}

/// `let w = <X>.governance_action in when w is { … }` → the binder AND the
/// `when` subject reference both become `governance_action`.
#[test]
fn renames_synthetic_let_to_governance_action() {
    let value = field(var("x", 1), "governance_action");
    let expr = let_in(
        "w",
        10,
        value,
        PseudoExpr::When {
            subject: PBox::new(var("w", 10)),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Error { message: None },
            }],
        },
    );
    let out = run_v3(expr);
    let (binder, subject) = let_name_and_body_subject(&out);
    assert_eq!(binder, "governance_action", "binder renamed");
    assert_eq!(
        subject.as_deref(),
        Some("governance_action"),
        "ref rewired by VarId"
    );
}

/// Drop-on-ambiguity: two synthetic binders both projecting `.bound_type` in
/// disjoint scopes → both left untouched.
#[test]
fn drops_ambiguous_same_field_targets() {
    // let q7 = a.bound_type in (let j9 = b.bound_type in q7)
    let inner = let_in("j9", 12, field(var("b", 2), "bound_type"), var("q7", 11));
    let expr = let_in("q7", 11, field(var("a", 1), "bound_type"), inner);
    let out = run_v3(expr);
    let PseudoExpr::Let { name, body, .. } = &out else {
        panic!()
    };
    assert_eq!(name, "q7", "ambiguous target dropped — q7 kept");
    let PseudoExpr::Let {
        name: inner_name, ..
    } = body.as_ref()
    else {
        panic!()
    };
    assert_eq!(inner_name, "j9", "ambiguous target dropped — j9 kept");
}

/// Structural `.fields` / `.tag` projections and already-meaningful binders are
/// never renamed.
#[test]
fn ignores_structural_and_meaningful() {
    // `.fields` (structural) → not a Cardano field.
    let e1 = let_in("w", 10, field(var("x", 1), "fields"), var("w", 10));
    let PseudoExpr::Let { name, .. } = run_v3(e1) else {
        panic!()
    };
    assert_eq!(name, "w", "structural .fields projection not renamed");

    // Already-meaningful binder name (a Cardano field) is not a placeholder.
    let e2 = let_in(
        "inputs",
        10,
        field(var("x", 1), "governance_action"),
        var("inputs", 10),
    );
    let PseudoExpr::Let { name, .. } = run_v3(e2) else {
        panic!()
    };
    assert_eq!(name, "inputs", "meaningful binder not treated as synthetic");
}

/// Versionless render (None) → no-op.
#[test]
fn inert_at_version_none() {
    let expr = let_in(
        "w",
        10,
        field(var("x", 1), "governance_action"),
        var("w", 10),
    );
    let out = rename_let_to_cardano_field(expr, &RenderCtx::at(None));
    let PseudoExpr::Let { name, .. } = out else {
        panic!()
    };
    assert_eq!(name, "w", "version=None ⇒ inert");
}
