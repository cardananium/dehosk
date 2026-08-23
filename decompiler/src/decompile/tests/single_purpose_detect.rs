//! Unit tests for `detect_single_purpose_v3` auto-detection.
//!
//! The detector proves a V3 single purpose from a `script_info`
//! assertion reached by the STRICT-dominance spine walk of the prepared
//! entry body. These tests build that prepared form directly: purpose
//! arms are `ConstructorShape::Unknown{tag}` with the `script_info`
//! type_hint (`Known` purpose ctors are the V1/V2 arity-1 forms), and
//! the subject selector is `NamedField("script_info")`.

use crate::decompile::{TypeHintId, ValidatorPurpose, detect_single_purpose_v3};
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

/// `Constructor` purpose pattern in the V3 prepared form:
/// `Unknown{tag}` + `type_hint = script_info`.
fn purpose_pattern(tag: usize, arity: usize) -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: Some(TypeHintId::new("script_info")),
        tag,
        fields: (0..arity).map(|i| binder("_", 700 + i as u32)).collect(),
        shape: ConstructorShape::unknown_data(tag, arity),
    }
}

fn fail_arm() -> WhenClause {
    WhenClause {
        pattern: WhenPattern::Wildcard,
        guard: None,
        body: PseudoExpr::Error { message: None },
    }
}

fn script_info_access() -> PseudoExpr {
    PseudoExpr::field_access(varref("script_context", 2), "script_info")
}

/// Wrap `body` in the prepared entry shape
/// `let decompiled = fn(script_context) { body }`.
fn entry(body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "decompiled".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("script_context", 2)],
            body: PBox::new(body),
        }),
        body: PBox::new(varref("decompiled", 1)),
    }
}

/// `expect Spending(..) = script_context.script_info`
/// as a spine-tail single-arm When (continuation inside the arm).
#[test]
fn detects_spine_tail_expect_destructure() {
    let when = PseudoExpr::When {
        subject: PBox::new(script_info_access()),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: purpose_pattern(1, 2),
            guard: None,
            body: PseudoExpr::Bool(true),
        }],
    };
    let input = entry(PseudoExpr::Let {
        name: "tx_info".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(PseudoExpr::field_access(
            varref("script_context", 2),
            "tx_info",
        )),
        body: PBox::new(when),
    });
    assert_eq!(
        detect_single_purpose_v3(&input),
        Some(ValidatorPurpose::Spend)
    );
}

/// `let script_info = script_context.script_info` then a When on the
/// alias Var — resolved by ONE VarId-keyed let-value hop.
#[test]
fn detects_var_alias_subject() {
    let when = PseudoExpr::When {
        subject: PBox::new(varref("script_info", 20)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: purpose_pattern(1, 2),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
            fail_arm(),
        ],
    };
    let input = entry(PseudoExpr::Let {
        name: "script_info".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(script_info_access()),
        body: PBox::new(when),
    });
    assert_eq!(
        detect_single_purpose_v3(&input),
        Some(ValidatorPurpose::Spend)
    );
}

/// The When sits in a Let VALUE behind a FieldAccess (`let g =
/// when ctx.script_info { Proposing(..) -> pp; _ -> fail
/// }.governance_action`); tag 5 maps to Propose.
#[test]
fn detects_when_in_let_value_behind_field_access() {
    let when = PseudoExpr::When {
        subject: PBox::new(script_info_access()),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: purpose_pattern(5, 2),
                guard: None,
                body: varref("proposal_procedure", 30),
            },
            fail_arm(),
        ],
    };
    let input = entry(PseudoExpr::Let {
        name: "governance_action".to_string(),
        id: Some(VarId::new(31)),
        value: PBox::new(PseudoExpr::field_access(when, "governance_action")),
        body: PBox::new(PseudoExpr::Bool(true)),
    });
    assert_eq!(
        detect_single_purpose_v3(&input),
        Some(ValidatorPurpose::Propose)
    );
}

/// A purpose assertion inside a WHEN-ARM body — a sibling-bypassable
/// region the spine walk never enters — must NOT promote.
#[test]
fn rejects_purpose_when_inside_when_arm() {
    let inner = PseudoExpr::When {
        subject: PBox::new(script_info_access()),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: purpose_pattern(0, 1),
            guard: None,
            body: PseudoExpr::Bool(true),
        }],
    };
    let outer = PseudoExpr::When {
        subject: PBox::new(varref("redeemer", 40)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body: inner,
        }],
    };
    assert_eq!(detect_single_purpose_v3(&entry(outer)), None);
}

/// A purpose match inside a LAMBDA body (un-applied helper) must not
/// promote.
#[test]
fn rejects_purpose_when_inside_lambda_body() {
    let inner = PseudoExpr::When {
        subject: PBox::new(script_info_access()),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: purpose_pattern(1, 2),
            guard: None,
            body: PseudoExpr::Bool(true),
        }],
    };
    let input = entry(PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(50)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("x", 51)],
            body: PBox::new(inner),
        }),
        body: PBox::new(PseudoExpr::Bool(true)),
    });
    assert_eq!(detect_single_purpose_v3(&input), None);
}

/// Two LIVE purpose arms = a multi-purpose dispatch, not single.
#[test]
fn rejects_two_live_purpose_arms() {
    let when = PseudoExpr::When {
        subject: PBox::new(script_info_access()),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: purpose_pattern(0, 1),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
            WhenClause {
                pattern: purpose_pattern(1, 2),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
        ],
    };
    assert_eq!(detect_single_purpose_v3(&entry(when)), None);
}

/// A non-purpose arm with a NON-failing body breaks the
/// exhaustive-or-fail proof.
#[test]
fn rejects_non_failing_wildcard_arm() {
    let when = PseudoExpr::When {
        subject: PBox::new(script_info_access()),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: purpose_pattern(1, 2),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Bool(false),
            },
        ],
    };
    assert_eq!(detect_single_purpose_v3(&entry(when)), None);
}

/// A when over something other than the script_info oracle never
/// qualifies, even with purpose-shaped arms.
#[test]
fn rejects_non_script_info_subject() {
    let when = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::field_access(
            varref("script_context", 2),
            "redeemer",
        )),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: purpose_pattern(1, 2),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
            fail_arm(),
        ],
    };
    assert_eq!(detect_single_purpose_v3(&entry(when)), None);
}

/// A purpose assertion inside an IF BRANCH (only the condition is
/// dominating) must not promote.
#[test]
fn rejects_purpose_when_inside_if_branch() {
    let inner = PseudoExpr::When {
        subject: PBox::new(script_info_access()),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: purpose_pattern(1, 2),
            guard: None,
            body: PseudoExpr::Bool(true),
        }],
    };
    let input = entry(PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Bool(true)),
        then_branch: PBox::new(inner),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    });
    assert_eq!(detect_single_purpose_v3(&input), None);
}

// `observe_script_info_purposes` — the wrap-neutral companion.
//
// Where `detect_single_purpose_v3` needs one dominating assertion, this
// only reads which `ScriptInfo` tags the body matches at all. PlutusTx
// splits that decision by field count first and tag second, across
// separate `when`s, so the stronger detector abstains and the diagnostic
// would otherwise claim the purpose is unrecoverable.

use crate::decompile::observe_script_info_purposes;

/// A `when <script_info> is { Constr<tag>(..) -> body }` arm.
fn tag_when(subject: PseudoExpr, tag: usize, arity: usize, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: purpose_pattern(tag, arity),
                guard: None,
                body,
            },
            fail_arm(),
        ],
    }
}

/// Two tags matched in SEPARATE `when`s on the peeled `script_info`
/// binder — the PlutusTx shape.
#[test]
fn observes_both_purposes_from_separate_tag_matches() {
    let spend = tag_when(varref("script_info", 5), 1, 2, PseudoExpr::Bool(true));
    let mint = tag_when(varref("script_info", 5), 0, 1, spend);
    assert_eq!(
        observe_script_info_purposes(&entry(mint)),
        vec![ValidatorPurpose::Mint, ValidatorPurpose::Spend],
    );
}

/// The `ctx.script_info` field-access subject works the same way.
#[test]
fn observes_a_purpose_from_the_field_access_subject() {
    let expr = tag_when(script_info_access(), 4, 1, PseudoExpr::Bool(true));
    assert_eq!(
        observe_script_info_purposes(&entry(expr)),
        vec![ValidatorPurpose::Vote],
    );
}

/// A `when` on anything else contributes nothing — the tags only mean a
/// purpose because the subject is the `script_info`.
#[test]
fn ignores_tags_matched_on_another_subject() {
    let expr = tag_when(varref("redeemer", 6), 1, 2, PseudoExpr::Bool(true));
    assert!(observe_script_info_purposes(&entry(expr)).is_empty());
}

/// Repeats collapse; order follows first appearance.
#[test]
fn deduplicates_repeated_tags() {
    let inner = tag_when(varref("script_info", 5), 1, 2, PseudoExpr::Bool(true));
    let outer = tag_when(varref("script_info", 5), 1, 2, inner);
    assert_eq!(
        observe_script_info_purposes(&entry(outer)),
        vec![ValidatorPurpose::Spend],
    );
}

// ---------------------------------------------------------------
// Scattered-dispatch split: `scattered_purposes` +
// `specialize_to_purpose`.
//
// The PlutusTx shape has no single dispatch `when` — it tests the
// ScriptInfo FIELD COUNT first and the tag second, so each purpose
// gets its own `when script_info is { P(..) -> …; _ -> … }` in a
// different branch.
// ---------------------------------------------------------------

use crate::decompile::{scattered_purposes, specialize_to_purpose};

/// `when script_info is { <tag>(..) -> body; _ -> fallback }`.
fn purpose_when(tag: usize, arity: usize, body: PseudoExpr, fallback: PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(varref("script_info", 9)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: purpose_pattern(tag, arity),
                guard: None,
                body,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: fallback,
            },
        ],
    }
}

/// The two purpose `when`s sit in different branches of an outer
/// non-purpose `when`, the way the field-count dispatch leaves them.
fn scattered_body() -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(varref("rest", 10)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: purpose_when(0, 1, PseudoExpr::Int(1.into()), PseudoExpr::Int(9.into())),
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: purpose_when(
                    1,
                    2,
                    PseudoExpr::Int(2.into()),
                    PseudoExpr::Error { message: None },
                ),
            },
        ],
    }
}

#[test]
fn scattered_purposes_collects_across_separate_whens() {
    let found = scattered_purposes(&scattered_body());
    assert_eq!(found, vec![ValidatorPurpose::Mint, ValidatorPurpose::Spend]);
}

#[test]
fn scattered_purposes_ignores_a_when_with_no_cardano_anchor() {
    // Same two-variant shape, but the arms carry no purpose type_hint,
    // so they are an ordinary user ADT and must not read as a dispatch.
    let plain = PseudoExpr::When {
        subject: PBox::new(varref("x", 11)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint: Some(TypeHintId::new("Unknown_S_3")),
                    tag: 0,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(0, 0),
                },
                guard: None,
                body: PseudoExpr::Int(1.into()),
            },
            WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint: Some(TypeHintId::new("Unknown_S_3")),
                    tag: 1,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(1, 0),
                },
                guard: None,
                body: PseudoExpr::Int(2.into()),
            },
        ],
    };
    assert!(scattered_purposes(&plain).is_empty());
}

#[test]
fn specialize_keeps_only_the_handlers_own_purpose() {
    let mint = specialize_to_purpose(scattered_body(), ValidatorPurpose::Mint);
    let PseudoExpr::When { clauses, .. } = &mint else {
        panic!("outer when survives");
    };
    // Mint's own `when` keeps both its arm and the wildcard.
    let PseudoExpr::When {
        clauses: mint_arms, ..
    } = &clauses[0].body
    else {
        panic!("mint when survives, got {:?}", clauses[0].body);
    };
    assert_eq!(mint_arms.len(), 2);
    // The spend `when` loses its only purpose arm and collapses to the
    // fallback — under `mint` that tag can never arrive.
    assert!(
        matches!(clauses[1].body, PseudoExpr::Error { .. }),
        "spend arm should collapse to its fallback, got {:?}",
        clauses[1].body
    );
}

#[test]
fn specialize_leaves_a_when_without_purpose_arms_alone() {
    let before = PseudoExpr::When {
        subject: PBox::new(varref("xs", 12)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body: PseudoExpr::Int(7.into()),
        }],
    };
    let after = specialize_to_purpose(before.clone(), ValidatorPurpose::Mint);
    assert_eq!(after, before);
}

#[test]
fn specialize_leaves_a_when_whose_subject_computes() {
    // `decode(ctx).script_info` carries the own-purpose NAME but hangs
    // off a call, not the context binder — nothing about it proves it
    // IS the script's purpose, so every arm stays.
    let subject = PseudoExpr::field_access(
        PseudoExpr::Apply {
            function: PBox::new(varref("decode", 13)),
            args: vec![varref("ctx", 14)].into(),
        },
        "script_info",
    );
    let before = PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: purpose_pattern(1, 2),
                guard: None,
                body: PseudoExpr::Int(2.into()),
            },
            fail_arm(),
        ],
    };
    let after = specialize_to_purpose(before.clone(), ValidatorPurpose::Mint);
    assert_eq!(after, before);
}

#[test]
fn specialize_collapses_over_a_plain_field_chain() {
    // Same shape, but the subject only READS — the `when` goes and the
    // wildcard body takes its place.
    let before = PseudoExpr::When {
        subject: PBox::new(script_info_access()),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: purpose_pattern(1, 2),
                guard: None,
                body: PseudoExpr::Int(2.into()),
            },
            fail_arm(),
        ],
    };
    let after = specialize_to_purpose(before, ValidatorPurpose::Mint);
    assert!(
        matches!(after, PseudoExpr::Error { .. }),
        "expected the wildcard body, got {after:?}"
    );
}

#[test]
fn scattered_purposes_ignores_a_purpose_from_the_transaction() {
    // `tx_info.redeemers` is a map KEYED by `ScriptPurpose`, so a
    // validator that walks it matches other scripts' purposes. Those
    // arms resolve exactly like a real dispatch, but specializing them
    // would delete live logic — under `mint` a `Spending` arm of a
    // redeemer scan is perfectly reachable.
    let scan = PseudoExpr::When {
        subject: PBox::new(varref("entry_key", 20)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: purpose_pattern(0, 1),
                guard: None,
                body: PseudoExpr::Int(1.into()),
            },
            WhenClause {
                pattern: purpose_pattern(1, 2),
                guard: None,
                body: PseudoExpr::Int(2.into()),
            },
        ],
    };
    assert!(scattered_purposes(&scan).is_empty());
    assert_eq!(
        specialize_to_purpose(scan.clone(), ValidatorPurpose::Mint),
        scan,
        "a purpose value from the transaction keeps all its arms"
    );
}

#[test]
fn specialize_fails_a_when_left_with_no_arm() {
    // The expect-destructure form: one purpose arm, no wildcard. Under
    // `mint` that tag never arrives, so the assertion always fails.
    // Leaving an EMPTY clause list would be worse than wrong —
    // `collapse_empty_when` rewrites `when X is {}` to `X`, turning the
    // assertion into the value it was asserting about.
    let before = PseudoExpr::When {
        subject: PBox::new(script_info_access()),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: purpose_pattern(1, 2),
            guard: None,
            body: PseudoExpr::Int(2.into()),
        }],
    };
    let after = specialize_to_purpose(before, ValidatorPurpose::Mint);
    assert!(
        matches!(after, PseudoExpr::Error { .. }),
        "expected a fail, got {after:?}"
    );
}

#[test]
fn specialize_keeps_a_when_that_binds_its_subject() {
    // `when script_info as si is { Spending(..) -> …; _ -> use(si) }`:
    // the wildcard body reads the subject binder, so the `when` has to
    // stay for `si` to exist.
    let before = PseudoExpr::When {
        subject: PBox::new(script_info_access()),
        subject_name: Some(binder("si", 30)),
        clauses: vec![
            WhenClause {
                pattern: purpose_pattern(1, 2),
                guard: None,
                body: PseudoExpr::Int(2.into()),
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: varref("si", 30),
            },
        ],
    };
    let after = specialize_to_purpose(before, ValidatorPurpose::Mint);
    let PseudoExpr::When {
        subject_name,
        clauses,
        ..
    } = &after
    else {
        panic!("when must survive a bound subject, got {after:?}");
    };
    assert!(subject_name.is_some());
    assert_eq!(clauses.len(), 1);
}

#[test]
fn scattered_purposes_ignores_a_same_named_field_off_a_user_record() {
    // `redeemer.script_info` carries the schema NAME but not the schema
    // POSITION — it is a user record's own field, and its arms stay.
    let subject = PseudoExpr::field_access(varref("redeemer", 31), "script_info");
    let scan = PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: purpose_pattern(0, 1),
                guard: None,
                body: PseudoExpr::Int(1.into()),
            },
            WhenClause {
                pattern: purpose_pattern(1, 2),
                guard: None,
                body: PseudoExpr::Int(2.into()),
            },
        ],
    };
    assert!(scattered_purposes(&scan).is_empty());
    assert_eq!(
        specialize_to_purpose(scan.clone(), ValidatorPurpose::Mint),
        scan
    );
}
