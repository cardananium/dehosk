use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};

fn nullary(tag: usize) -> PseudoExpr {
    PseudoExpr::constr(
        crate::pseudo::constructor::ConstructorShape::scott_positional(tag, 0),
        vec![],
    )
}

/// `if c { Constr<0> } else { Constr<1> }` over a comparison cond.
fn inverse_cip_producer() -> PseudoExpr {
    PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Bool(true)),
        then_branch: PBox::new(nullary(0)),
        else_branch: PBox::new(nullary(1)),
    }
}

/// `when X is { Constr<0> -> ok; _ -> fail }`.
fn tag0_success_oracle(subject: PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(
                    crate::pseudo::constructor::ConstructorShape::scott_positional(0, 0),
                    vec![],
                ),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Error { message: None },
            },
        ],
    }
}

fn seq(value: PseudoExpr, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "_".into(),
        id: None,
        value: PBox::new(value),
        body: PBox::new(body),
    }
}

/// `when X is { Constr<1> -> ok; _ -> fail }` — the CIP success signature.
fn tag1_success_oracle(subject: PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(
                    crate::pseudo::constructor::ConstructorShape::scott_positional(1, 0),
                    vec![],
                ),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Error { message: None },
            },
        ],
    }
}

#[test]
fn both_signals_present_is_inverse_cip() {
    let seed = seq(
        inverse_cip_producer(),
        tag0_success_oracle(PseudoExpr::Unit),
    );
    assert_eq!(
        detect_church_polarity(&seed).verdict(),
        ChurchPolarity::InverseCip
    );
}

#[test]
fn consistency_gate_tag1_oracle_present_stays_cip() {
    // Producer + tag-0 oracle BUT also a tag-1 (CIP) success oracle →
    // ambiguous convention → fail-safe to CIP.
    let seed = seq(
        inverse_cip_producer(),
        seq(
            tag0_success_oracle(PseudoExpr::Unit),
            tag1_success_oracle(PseudoExpr::Unit),
        ),
    );
    assert_eq!(detect_church_polarity(&seed).verdict(), ChurchPolarity::Cip);
}

#[test]
fn producer_only_stays_cip() {
    // No success oracle → fail-safe to CIP.
    let seed = seq(inverse_cip_producer(), PseudoExpr::Bool(true));
    assert_eq!(detect_church_polarity(&seed).verdict(), ChurchPolarity::Cip);
}

#[test]
fn oracle_only_stays_cip() {
    // No inverse-CIP producer → fail-safe to CIP.
    let seed = tag0_success_oracle(PseudoExpr::Unit);
    assert_eq!(detect_church_polarity(&seed).verdict(), ChurchPolarity::Cip);
}

#[test]
fn cip_negation_producer_then_constr1_stays_cip() {
    // A CIP `if c { True=Constr<1> } else { False=Constr<0> }` does NOT
    // match the inverse-CIP producer (then-branch is tag 1).
    let cip_producer = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Bool(true)),
        then_branch: PBox::new(nullary(1)),
        else_branch: PBox::new(nullary(0)),
    };
    let seed = seq(cip_producer, tag0_success_oracle(PseudoExpr::Unit));
    assert_eq!(detect_church_polarity(&seed).verdict(), ChurchPolarity::Cip);
}

#[test]
fn default_polarity_is_cip() {
    // The value every non-pipeline caller gets, and the tag table it
    // implies: CIP `True = Constr<1>`, `False = Constr<0>`.
    let cip = ChurchPolarity::default();
    assert_eq!(cip, ChurchPolarity::Cip);
    assert_eq!(cip.data_tag_for_true(), 1);
    assert_eq!(cip.data_tag_for_false(), 0);
}

#[test]
fn inverse_cip_flips_the_data_tags() {
    let inverse = ChurchPolarity::InverseCip;
    assert_eq!(inverse.data_tag_for_true(), 0);
    assert_eq!(inverse.data_tag_for_false(), 1);
}

#[test]
fn report_captures_inverse_cip_signals() {
    // Detection returns the signal breakdown; the report reflects it.
    let seed = seq(
        inverse_cip_producer(),
        tag0_success_oracle(PseudoExpr::Unit),
    );
    let signals = detect_church_polarity(&seed);
    assert_eq!(signals.verdict(), ChurchPolarity::InverseCip);
    assert!(signals.inverse_cip_producer);
    assert!(signals.success_oracle_tag0);
    assert!(!signals.success_oracle_tag1);
    let report = render_polarity_report_heuristic(&signals);
    assert!(report.contains("InverseCip (detected"));
    assert!(report.contains("(1) inverse-CIP producer"));
    assert!(report.contains("HEURISTIC"));
}

#[test]
fn report_marks_fail_safe_default_for_cip() {
    // Producer only → fail-safe Cip; the report must say so.
    let seed = seq(inverse_cip_producer(), PseudoExpr::Bool(true));
    let signals = detect_church_polarity(&seed);
    assert_eq!(signals.verdict(), ChurchPolarity::Cip);
    let report = render_polarity_report_heuristic(&signals);
    assert!(report.contains("verdict: Cip (default)"));
    assert!(report.contains("fail-safe default"));
}
