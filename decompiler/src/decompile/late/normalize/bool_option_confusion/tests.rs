use super::fix_bool_option_confusion;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

fn binder(name: &str) -> Binder {
    Binder::new(name, VarId::fresh_binding())
}

fn subject() -> PseudoExpr {
    PseudoExpr::Var {
        name: "subj".to_string(),
        id: Some(VarId::fresh_binding()),
    }
}

/// A `Constr<tag>` with `arity` wildcard-typed fields (bare, Unknown shape).
fn bare_constr(tag: usize, arity: usize) -> PseudoExpr {
    let fields = (0..arity).map(|_| PseudoExpr::Int(0.into())).collect();
    PseudoExpr::constr(ConstructorShape::unknown_data(tag, arity), fields)
}

/// `Some(x)` — standard Option, tag 0 / arity 1.
fn some_candidate() -> PseudoExpr {
    // A bare tag-0 arity-1 Constr is a Some-candidate per
    // `is_option_some_arity1`.
    bare_constr(0, 1)
}

/// `None` — standard Option, tag 1 / nullary.
fn none_candidate() -> PseudoExpr {
    bare_constr(1, 0)
}

fn clause(tag: usize, arity: usize, body: PseudoExpr) -> WhenClause {
    let fields = (0..arity).map(|i| binder(&format!("f{i}"))).collect();
    WhenClause {
        pattern: WhenPattern::constructor(ConstructorShape::unknown_data(tag, arity), fields),
        guard: None,
        body,
    }
}

fn build_when(clauses: Vec<WhenClause>) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(subject()),
        subject_name: None,
        clauses,
    }
}

fn arm_bodies(expr: &PseudoExpr) -> Vec<&PseudoExpr> {
    match expr {
        PseudoExpr::When { clauses, .. } => clauses.iter().map(|c| &c.body).collect(),
        _ => panic!("expected When, got {expr:?}"),
    }
}

fn is_known_some(expr: &PseudoExpr) -> bool {
    matches!(
        expr,
        PseudoExpr::Constr {
            shape: ConstructorShape::Known(KnownConstructor::Some),
            ..
        }
    )
}

fn is_known_none(expr: &PseudoExpr) -> bool {
    matches!(
        expr,
        PseudoExpr::Constr {
            shape: ConstructorShape::Known(KnownConstructor::None),
            ..
        }
    )
}

fn any_known_option(bodies: &[&PseudoExpr]) -> bool {
    bodies.iter().any(|b| is_known_some(b) || is_known_none(b))
}

/// (a) A 3-ctor `when {None-cand, Some-cand, bare Constr<2>}` is NOT
/// relabeled: the tag-2 arm is a disproof witness, so the veto fires and
/// all arms stay raw.
#[test]
fn veto_fires_on_third_bare_ctor() {
    let when = build_when(vec![
        clause(0, 1, some_candidate()),
        clause(1, 0, none_candidate()),
        clause(2, 2, bare_constr(2, 2)),
    ]);
    let fixed = fix_bool_option_confusion(when);
    let bodies = arm_bodies(&fixed);
    assert!(
        !any_known_option(&bodies),
        "veto should suppress Some/None relabel when a tag>=2 witness is present: {bodies:?}"
    );
}

/// (b) A genuine 2-ctor Option `when {None-cand, Some-cand}` IS still
/// relabeled: no witness present.
#[test]
fn two_ctor_option_still_relabeled() {
    let when = build_when(vec![
        clause(0, 1, some_candidate()),
        clause(1, 0, none_candidate()),
    ]);
    let fixed = fix_bool_option_confusion(when);
    let bodies = arm_bodies(&fixed);
    assert!(
        bodies.iter().any(|b| is_known_some(b)),
        "Some arm should be relabeled: {bodies:?}"
    );
    assert!(
        bodies.iter().any(|b| is_known_none(b)),
        "None arm should be relabeled: {bodies:?}"
    );
}

/// (c) An Option `when` whose third arm is `fail` (Error) or `Error(x)` IS
/// still relabeled — Error/fail are not disproof witnesses.
#[test]
fn error_arm_is_not_a_witness() {
    // Third arm: Error(x) — a Result::Err, tolerated tail, not a witness.
    let when = build_when(vec![
        clause(0, 1, some_candidate()),
        clause(1, 0, none_candidate()),
        clause(2, 1, PseudoExpr::err(PseudoExpr::Int(0.into()))),
    ]);
    let fixed = fix_bool_option_confusion(when);
    let bodies = arm_bodies(&fixed);
    assert!(
        any_known_option(&bodies),
        "Error arm must not veto Some/None relabel: {bodies:?}"
    );

    // Third arm: fail (PseudoExpr::Error) — also not a witness.
    let when_fail = build_when(vec![
        clause(0, 1, some_candidate()),
        clause(1, 0, none_candidate()),
        clause(
            2,
            0,
            PseudoExpr::Error {
                message: Some("PT1".to_string()),
            },
        ),
    ]);
    let fixed_fail = fix_bool_option_confusion(when_fail);
    let bodies_fail = arm_bodies(&fixed_fail);
    assert!(
        any_known_option(&bodies_fail),
        "fail arm must not veto Some/None relabel: {bodies_fail:?}"
    );
}

/// (d) A `when` with a nested-Option / Apply arm still relabels — an Apply
/// tail (e.g. a recursive call) is not a witness and the disproof descent
/// does not enter Apply args.
#[test]
fn apply_arm_still_relabels() {
    let apply_arm = PseudoExpr::Apply {
        function: PBox::new(subject()),
        // A bare tag-2 ctor buried in an Apply ARG must NOT be seen as a
        // witness (descent does not enter Apply args).
        args: vec![bare_constr(2, 2)].into(),
    };
    let when = build_when(vec![
        clause(0, 1, some_candidate()),
        clause(1, 0, none_candidate()),
        clause(2, 1, apply_arm),
    ]);
    let fixed = fix_bool_option_confusion(when);
    let bodies = arm_bodies(&fixed);
    assert!(
        any_known_option(&bodies),
        "Apply arm (with buried ctor in args) must not veto relabel: {bodies:?}"
    );
}
