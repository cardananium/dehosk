use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_when_body_accepts_un_bytearray_extractor() {
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 1),
                    vec!["field_0".into()],
                ),
                guard: None,
                body: PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.un_bytearray"),
                    args: vec![PseudoExpr::var("field_0")].into(),
                },
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::error(),
            },
        ],
    };

    assert_eq!(
        analyze_when_body(&body, 1),
        Some("extract_policy_id".to_string())
    );
}

#[test]
fn test_analyze_when_body_accepts_un_int_extractor() {
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 1),
                    vec!["field_0".into()],
                ),
                guard: None,
                body: PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.un_int"),
                    args: vec![PseudoExpr::var("field_0")].into(),
                },
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::error(),
            },
        ],
    };

    assert_eq!(analyze_when_body(&body, 1), Some("extract_int".to_string()));
}

/// `extract_*` is a claim about a single extraction. A `when` with TWO
/// live arms is a sum decoder — naming it `extract_policy_id` asserts a
/// policy id the script never mentions. The wildcard-fail arm alone does
/// not make a `when` an `expect`.
#[test]
fn multi_arm_decoder_is_not_named_extract_policy_id() {
    let arm = |tag: usize| WhenClause {
        pattern: WhenPattern::constructor(
            ConstructorShape::unknown_data(tag, 1),
            vec!["field_0".into()],
        ),
        guard: None,
        body: PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
            args: vec![PseudoExpr::var("field_0")].into(),
        },
    };
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            arm(0),
            arm(1),
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::error(),
            },
        ],
    };
    assert_ne!(
        analyze_when_body(&body, 1),
        Some("extract_policy_id".to_string()),
        "a two-variant decoder must not take the extraction name"
    );
}

/// The extractor has to be what the branch RETURNS. An `un_int` buried
/// in a nested lambda otherwise names a pair-building function
/// `extract_int`.
#[test]
fn extractor_inside_a_nested_lambda_does_not_name_the_function() {
    let nested = PseudoExpr::Lambda {
        params: vec!["y".into()],
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_int"),
            args: vec![PseudoExpr::var("y")].into(),
        }),
    };
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 1),
                    vec!["field_0".into()],
                ),
                guard: None,
                body: PseudoExpr::Tuple((vec![PseudoExpr::var("field_0"), nested]).into()),
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::error(),
            },
        ],
    };
    assert_ne!(
        analyze_when_body(&body, 1),
        Some("extract_int".to_string()),
        "the name describes the return value, not every call inside"
    );
}

/// `decode_output_datum` is `NoDatum | DatumHash(h) | InlineDatum(d)` —
/// tags 0/1/2 at arities 0/1/1. A `Credential`-shaped decoder gets the
/// shape-honest name instead.
#[test]
fn narrow_decoder_without_the_output_datum_shape_is_not_named_for_it() {
    let arm = |tag: usize| WhenClause {
        pattern: WhenPattern::constructor(
            ConstructorShape::unknown_data(tag, 1),
            vec!["field_0".into()],
        ),
        guard: None,
        body: PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
            args: vec![PseudoExpr::var("field_0")].into(),
        },
    };
    // Three payload-carrying arms: not the `OutputDatum` layout (whose
    // tag 0 is nullary), and not the two-arm pair-walk shape either.
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![arm(0), arm(1), arm(2)],
    };
    assert_eq!(
        analyze_when_body(&body, 1),
        Some("decode_constr_narrow".to_string()),
    );
}

/// The real `OutputDatum` layout still gets its name.
#[test]
fn output_datum_shape_keeps_its_name() {
    let nullary = WhenClause {
        pattern: WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
        guard: None,
        body: PseudoExpr::Bool(true),
    };
    let payload = |tag: usize| WhenClause {
        pattern: WhenPattern::constructor(
            ConstructorShape::unknown_data(tag, 1),
            vec!["field_0".into()],
        ),
        guard: None,
        body: PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
            args: vec![PseudoExpr::var("field_0")].into(),
        },
    };
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![nullary, payload(1), payload(2)],
    };
    assert_eq!(
        analyze_when_body(&body, 1),
        Some("decode_output_datum".to_string()),
    );
}

/// A live wildcard arm next to the three `OutputDatum` tags means the
/// subject is something wider — the layout match does not settle it.
#[test]
fn output_datum_shape_rejects_a_live_wildcard_arm() {
    let nullary = WhenClause {
        pattern: WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
        guard: None,
        body: PseudoExpr::Bool(true),
    };
    let payload = |tag: usize| WhenClause {
        pattern: WhenPattern::constructor(
            ConstructorShape::unknown_data(tag, 1),
            vec!["field_0".into()],
        ),
        guard: None,
        body: PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
            args: vec![PseudoExpr::var("field_0")].into(),
        },
    };
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            nullary,
            payload(1),
            payload(2),
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Bool(false),
            },
        ],
    };
    assert_ne!(
        analyze_when_body(&body, 1),
        Some("decode_output_datum".to_string()),
        "a fourth live case is not the OutputDatum layout"
    );
}

/// A conditional whose arms all return the extraction still returns it.
#[test]
fn extractor_behind_a_conditional_still_names_the_function() {
    let extract = || PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.un_bytearray"),
        args: vec![PseudoExpr::var("field_0")].into(),
    };
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 1),
                    vec!["field_0".into()],
                ),
                guard: None,
                body: PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::Bool(true)),
                    then_branch: PBox::new(extract()),
                    else_branch: PBox::new(extract()),
                },
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::error(),
            },
        ],
    };
    assert_eq!(
        analyze_when_body(&body, 1),
        Some("extract_policy_id".to_string())
    );
}
