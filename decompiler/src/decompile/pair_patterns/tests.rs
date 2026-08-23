use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn pair_pattern_helpers_cover_sugar_and_constructor_forms() {
    let sugar = WhenPattern::Pair("left".into(), "right".into());
    let constr =
        WhenPattern::constructor_known(KnownConstructor::Pair, vec!["left".into(), "right".into()]);

    assert!(is_pair_pattern(&sugar));
    assert!(is_pair_pattern(&constr));
    assert_eq!(
        pair_pattern_binders(&sugar),
        Some(("left".to_string(), "right".to_string()))
    );
    assert_eq!(
        pair_pattern_binders(&constr),
        Some(("left".to_string(), "right".to_string()))
    );
}

#[test]
fn pair_field_helpers_cover_direct_payload_and_body_scan() {
    let fst_access = PseudoExpr::field_access(PseudoExpr::var("entry"), "fst".to_string());
    let snd_payload = PseudoExpr::constr(
        ConstructorShape::unknown_data(0, 1),
        vec![PseudoExpr::field_access(
            PseudoExpr::var("entry"),
            "snd".to_string(),
        )],
    );
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("transform")),
        args: vec![snd_payload.clone()].into(),
    };

    assert!(is_pair_field_access_of_var(&fst_access, "entry", "fst"));
    assert!(is_pair_field_payload_of_var(&snd_payload, "entry", "snd"));
    assert!(body_contains_pair_field_access(&body));
}
