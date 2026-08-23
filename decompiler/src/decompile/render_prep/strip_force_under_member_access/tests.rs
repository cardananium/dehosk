use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::field_selector::FieldSelector;

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `Some(payload) -> payload().snd` → `payload.snd`.
#[test]
fn strips_force_under_pair_snd_on_pattern_binder() {
    let payload = Binder::new("payload".to_string(), VarId::new(200));
    let payload_call = PseudoExpr::Apply {
        function: PBox::new(varref("payload", 200)),
        args: vec![].into(),
    };
    let clause_body = PseudoExpr::FieldAccess {
        record: PBox::new(payload_call),
        selector: FieldSelector::PairSnd,
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(varref("subject", 100)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 1,
                fields: vec![payload],
                shape: ConstructorShape::Known(KnownConstructor::Some),
            },
            guard: None,
            body: clause_body,
        }],
    };

    let out = strip_force_under_member_access(expr);
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    let body = &clauses[0].body;
    let PseudoExpr::FieldAccess { record, .. } = body else {
        panic!("expected FieldAccess, got {body:?}")
    };
    assert!(
        matches!(record.as_ref(), PseudoExpr::Var { id: Some(_), .. }),
        "record should collapse to bare Var, got {:?}",
        record
    );
}

/// `fn(x) { x().snd }` → `fn(x) { x.snd }` (Lambda param case).
#[test]
fn strips_force_under_member_access_on_lambda_param() {
    let p = Binder::new("x".to_string(), VarId::new(200));
    let body = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::Force(PBox::new(varref("x", 200)))),
        selector: FieldSelector::PairSnd,
    };
    let expr = PseudoExpr::Lambda {
        params: vec![p],
        body: PBox::new(body),
    };

    let out = strip_force_under_member_access(expr);
    let PseudoExpr::Lambda { body, .. } = out else {
        panic!()
    };
    let PseudoExpr::FieldAccess { record, .. } = body.as_ref() else {
        panic!()
    };
    assert!(
        matches!(record.as_ref(), PseudoExpr::Var { id: Some(_), .. }),
        "Lambda param force should be stripped under FieldAccess"
    );
}

/// Top-level `Var(p)()` (Force outside a FieldAccess) is NOT stripped.
#[test]
fn does_not_strip_force_outside_member_access() {
    let p = Binder::new("x".to_string(), VarId::new(200));
    let body = PseudoExpr::Force(PBox::new(varref("x", 200)));
    let expr = PseudoExpr::Lambda {
        params: vec![p],
        body: PBox::new(body),
    };
    let out = strip_force_under_member_access(expr);
    let PseudoExpr::Lambda { body, .. } = out else {
        panic!()
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Force(_)),
        "Force outside FieldAccess context must remain"
    );
}
