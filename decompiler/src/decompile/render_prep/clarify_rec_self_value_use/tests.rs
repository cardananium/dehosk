use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::constructor::ConstructorShape;

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn ctor_pattern(tag: usize) -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag,
        fields: vec![],
        shape: ConstructorShape::unknown_data(tag, 0),
    }
}

/// `rec fn self(p) { when self is { 0 -> A; 1 -> B; 2 -> C } }`
///  → `rec fn self(p) { self(A, B, C) }`.
#[test]
fn reverts_complete_3_arm_self_case() {
    let input = PseudoExpr::RecFn {
        name: Binder::new("self".to_string(), VarId::new(100)),
        params: vec![Binder::new("p".to_string(), VarId::new(1))],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("self", 100)),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: ctor_pattern(0),
                    guard: None,
                    body: var("a", 10),
                },
                WhenClause {
                    pattern: ctor_pattern(1),
                    guard: None,
                    body: var("b", 11),
                },
                WhenClause {
                    pattern: ctor_pattern(2),
                    guard: None,
                    body: var("c", 12),
                },
            ],
        }),
    };
    let out = clarify_rec_self_value_use(input);
    let PseudoExpr::RecFn { body, .. } = out else {
        panic!("RecFn")
    };
    match body.into_inner() {
        PseudoExpr::Apply { function, args } => {
            assert!(
                matches!(*function, PseudoExpr::Var { id: Some(v), .. } if v == VarId::new(100))
            );
            assert_eq!(args.len(), 3);
            let names: Vec<String> = args
                .iter()
                .map(|a| match a {
                    PseudoExpr::Var { name, .. } => name.clone(),
                    _ => "<other>".to_string(),
                })
                .collect();
            assert_eq!(names, vec!["a", "b", "c"]);
        }
        other => panic!("expected Apply, got {:?}", other),
    }
}

/// Missing tag (sequence is 0, 2) — skip.
#[test]
fn skips_non_consecutive_tags() {
    let input = PseudoExpr::RecFn {
        name: Binder::new("self".to_string(), VarId::new(100)),
        params: vec![Binder::new("p".to_string(), VarId::new(1))],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("self", 100)),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: ctor_pattern(0),
                    guard: None,
                    body: var("a", 10),
                },
                WhenClause {
                    pattern: ctor_pattern(2),
                    guard: None,
                    body: var("c", 12),
                },
            ],
        }),
    };
    let out = clarify_rec_self_value_use(input.clone());
    assert_eq!(out, input);
}

/// Constructor pattern with binders — skip (body might use them).
#[test]
fn skips_constructor_with_binders() {
    let input = PseudoExpr::RecFn {
        name: Binder::new("self".to_string(), VarId::new(100)),
        params: vec![Binder::new("p".to_string(), VarId::new(1))],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("self", 100)),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: WhenPattern::Constructor {
                        type_hint: None,
                        tag: 0,
                        fields: vec![Binder::new("inner".to_string(), VarId::new(99))],
                        shape: ConstructorShape::unknown_data(0, 1),
                    },
                    guard: None,
                    body: var("inner", 99),
                },
                WhenClause {
                    pattern: ctor_pattern(1),
                    guard: None,
                    body: var("b", 11),
                },
                WhenClause {
                    pattern: ctor_pattern(2),
                    guard: None,
                    body: var("c", 12),
                },
            ],
        }),
    };
    let out = clarify_rec_self_value_use(input.clone());
    assert_eq!(out, input);
}

/// When-subject is NOT self — leave alone.
#[test]
fn skips_non_self_subject() {
    let input = PseudoExpr::RecFn {
        name: Binder::new("self".to_string(), VarId::new(100)),
        params: vec![Binder::new("p".to_string(), VarId::new(1))],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("other", 200)),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: ctor_pattern(0),
                    guard: None,
                    body: var("a", 10),
                },
                WhenClause {
                    pattern: ctor_pattern(1),
                    guard: None,
                    body: var("b", 11),
                },
            ],
        }),
    };
    let out = clarify_rec_self_value_use(input.clone());
    assert_eq!(out, input);
}
