use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_collect_all_names_visitor_covers_binders_and_vars() {
    let expr = PseudoExpr::Let {
        name: "outer".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".into()],
            body: PBox::new(PseudoExpr::RecFn {
                name: "loop".into(),
                params: vec!["acc".into()],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("outer")),
                    args: vec![PseudoExpr::var("x"), PseudoExpr::var("acc")].into(),
                }),
            }),
        }),
        body: PBox::new(PseudoExpr::var("outer")),
    };

    assert_eq!(
        collect_all_names_sorted(&expr),
        vec![
            "acc".to_string(),
            "loop".to_string(),
            "outer".to_string(),
            "x".to_string(),
        ]
    );
}

#[test]
fn test_boolean_negation_detection() {
    // when x: Bool is { True -> False, False -> True }
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor_known(KnownConstructor::True, vec![]),
                guard: None,
                body: PseudoExpr::Bool(false),
            },
            WhenClause {
                pattern: WhenPattern::constructor_known(KnownConstructor::False, vec![]),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
        ],
    };
    assert!(is_boolean_negation(&body));
}

#[test]
fn test_is_generic_name() {
    assert!(is_generic_name("fn"));
    assert!(is_generic_name("rec_fn"));
    assert!(is_generic_name("f_3"));
    assert!(is_generic_name("f_14"));
    assert!(is_generic_name("fn_7"));
    assert!(is_generic_name("fn_22"));
    assert!(is_generic_name("rec_fn_7"));
    assert!(is_generic_name("fn_result"));
    assert!(is_generic_name("fn_result_2"));
    assert!(is_generic_name("rec_fn_result"));
    assert!(is_generic_name("rec_fn_result_2"));
    assert!(is_generic_name("fold_result_0"));
    assert!(is_generic_name("fold_result_6"));
    // `helper` / `helper_<N>` count as generic so downstream
    // readability passes can still upgrade them; an `fn`-shaped hint
    // would collide with the `fn` keyword.
    assert!(is_generic_name("helper"));
    assert!(is_generic_name("helper_2"));
    assert!(is_generic_name("helper_17"));
    assert!(!is_generic_name("x_5"));
    assert!(!is_generic_name("condition_ok"));
    assert!(!is_generic_name("head"));
    assert!(!is_generic_name("self_fn"));
    // `helper_X` where X isn't all-digits stays out of generic.
    assert!(!is_generic_name("helper_lookup"));
}

#[test]
fn test_is_temporary_helper_name() {
    assert!(is_temporary_helper_name("g"));
    assert!(is_temporary_helper_name("h2"));
    assert!(is_temporary_helper_name("z_2"));
    assert!(is_temporary_helper_name("check_2"));
    assert!(is_temporary_helper_name("to_data_partial"));
    assert!(!is_temporary_helper_name("lookup"));
    assert!(!is_temporary_helper_name("filter_matches"));
}
