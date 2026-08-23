use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::var_id::VarId;

fn selector_lambda(body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![
            Binder::new("a", VarId::new(9401)),
            Binder::new("b", VarId::new(9402)),
        ],
        body: PBox::new(body),
    }
}

#[test]
fn test_scott_constructor_value_rejects_same_name_foreign_body_var() {
    let expr = selector_lambda(PseudoExpr::var_with_id("a", VarId::new(9403)));

    assert!(Simplifier::try_rewrite_scott_constructor_value(&expr).is_none());
}

#[test]
fn test_scott_constructor_value_rejects_same_name_foreign_apply_callee() {
    let expr = selector_lambda(PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("a", VarId::new(9404))),
        args: vec![PseudoExpr::int(1)].into(),
    });

    assert!(Simplifier::try_rewrite_scott_constructor_value(&expr).is_none());
}

#[test]
fn test_scott_constructor_value_allows_same_name_foreign_field_arg() {
    let field_id = VarId::new(9405);
    let expr = selector_lambda(PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("a", VarId::new(9401))),
        args: vec![PseudoExpr::var_with_id("a", field_id)].into(),
    });

    let (rewritten, arity, has_fields) = Simplifier::try_rewrite_scott_constructor_value(&expr)
        .expect("expected selector param call to rewrite");

    assert_eq!(arity, 2);
    assert!(has_fields);
    assert!(
        matches!(
            rewritten,
            PseudoExpr::Constr { tag: 0, fields, .. }
                if matches!(&fields[0], PseudoExpr::Var { name, id } if name == "a" && *id == Some(field_id))
        ),
        "same-name foreign field argument should be preserved"
    );
}

fn eta_subject(function: PseudoExpr, first_arg: PseudoExpr, second_arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![
            Binder::new("sel", VarId::new(9410)),
            Binder::new("rest", VarId::new(9411)),
        ],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(function),
            args: vec![first_arg, second_arg].into(),
        }),
    }
}

#[test]
fn test_eta_pair_selector_subject_rejects_same_name_foreign_selector_callee() {
    let subject = eta_subject(
        PseudoExpr::var_with_id("sel", VarId::new(9412)),
        PseudoExpr::var_with_id("payload", VarId::new(9413)),
        PseudoExpr::var_with_id("rest", VarId::new(9411)),
    );

    assert!(Simplifier::extract_eta_pair_selector_subject(&subject).is_none());
}

#[test]
fn test_eta_pair_selector_subject_rejects_same_name_foreign_second_arg() {
    let subject = eta_subject(
        PseudoExpr::var_with_id("sel", VarId::new(9410)),
        PseudoExpr::var_with_id("payload", VarId::new(9414)),
        PseudoExpr::var_with_id("rest", VarId::new(9415)),
    );

    assert!(Simplifier::extract_eta_pair_selector_subject(&subject).is_none());
}

#[test]
fn test_eta_pair_selector_subject_allows_same_name_foreign_payload() {
    let payload_id = VarId::new(9416);
    let subject = eta_subject(
        PseudoExpr::var_with_id("sel", VarId::new(9410)),
        PseudoExpr::var_with_id("rest", payload_id),
        PseudoExpr::var_with_id("rest", VarId::new(9411)),
    );

    let extracted = Simplifier::extract_eta_pair_selector_subject(&subject)
        .expect("same-name foreign payload should not count as the second param");

    assert!(
        matches!(
            extracted,
            PseudoExpr::Var { name, id } if name == "rest" && id == Some(payload_id)
        ),
        "payload identity should be preserved"
    );
}
