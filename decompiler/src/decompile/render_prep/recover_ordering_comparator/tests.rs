use super::*;
use crate::pseudo::ast::{BinaryOp, Binder, WhenClause, WhenPattern};

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn unknown_constr(tag: usize) -> PseudoExpr {
    PseudoExpr::constr(ConstructorShape::unknown_data(tag, 0), vec![])
}

fn cmp(left: u32, right: u32, op: BinaryOp) -> PseudoExpr {
    PseudoExpr::BinOp {
        op,
        left: PBox::new(var("a", left)),
        right: PBox::new(var("b", right)),
    }
}

/// `fn cmp(a,b){ if a<b {Constr<0>} else if a==b {Constr<1>} else {Constr<2>} }`
/// with the three branch tags supplied as `t0`/`t1`/`t2`.
fn comparator_lambda(t0: usize, t1: usize, t2: usize) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![binder("a", 1), binder("b", 2)],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(cmp(1, 2, BinaryOp::Lt)),
            then_branch: PBox::new(unknown_constr(t0)),
            else_branch: PBox::new(PseudoExpr::If {
                condition: PBox::new(cmp(1, 2, BinaryOp::Eq)),
                then_branch: PBox::new(unknown_constr(t1)),
                else_branch: PBox::new(unknown_constr(t2)),
            }),
        }),
    }
}

/// A consumer arm that ALREADY reads the value as a native `Ordering`:
/// `Known(Less/Equal/Greater)` whose tag matches (Less=0, Equal=1,
/// Greater=2) — the shape `is_clean_ordering_when` requires.
fn ordering_when_pattern(tag: usize) -> WhenPattern {
    let kc = match tag {
        0 => KnownConstructor::Less,
        1 => KnownConstructor::Equal,
        2 => KnownConstructor::Greater,
        _ => unreachable!("ordering_when_pattern tag {tag} > 2"),
    };
    WhenPattern::Constructor {
        type_hint: None,
        tag,
        fields: Vec::new(),
        shape: ConstructorShape::Known(kc),
    }
}

/// `when cmp(x, y) is { Less -> A; Equal -> B; Greater -> C }`.
fn ordering_consumer(fid: u32) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("cmp", fid)),
            args: vec![var("x", 100), var("y", 101)].into(),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause::new(ordering_when_pattern(0), var("A", 200)),
            WhenClause::new(ordering_when_pattern(1), var("B", 201)),
            WhenClause::new(ordering_when_pattern(2), var("C", 202)),
        ],
    }
}

fn assert_branch_is(e: &PseudoExpr, kc: KnownConstructor) {
    match e {
        PseudoExpr::Constr {
            shape: ConstructorShape::Known(got),
            fields,
            ..
        } if fields.is_empty() => {
            assert_eq!(*got, kc, "expected {kc:?}, got {got:?}");
        }
        other => panic!("expected Known({kc:?}) Constr, got {other:?}"),
    }
}

/// Comparator whose arms are `Less=0`, `Equal=1`, `Greater=2`, plus a clean
/// 3-arm Ordering consumer → producer branches recovered to
/// Less/Equal/Greater BY TAG.
#[test]
fn recovers_abi_comparator_with_ordering_consumer() {
    let expr = PseudoExpr::Let {
        name: "cmp".to_string(),
        id: Some(VarId::new(7)),
        value: PBox::new(comparator_lambda(0, 1, 2)),
        body: PBox::new(ordering_consumer(7)),
    };
    let out = recover_ordering_comparator(expr);
    let PseudoExpr::Let { value, .. } = &out else {
        panic!("expected Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.as_ref() else {
        panic!("expected Lambda")
    };
    let PseudoExpr::If {
        then_branch,
        else_branch,
        ..
    } = body.as_ref()
    else {
        panic!("expected If");
    };
    // a<b → tag0 → Less
    assert_branch_is(then_branch, KnownConstructor::Less);
    let PseudoExpr::If {
        then_branch: t1,
        else_branch: t2,
        ..
    } = else_branch.as_ref()
    else {
        panic!("expected nested If");
    };
    // a==b → tag1 → Equal ; else → tag2 → Greater
    assert_branch_is(t1, KnownConstructor::Equal);
    assert_branch_is(t2, KnownConstructor::Greater);
}

/// Scrambled tags: `<` produces tag 2, `==` produces tag 0, `>` produces
/// tag 1 — not `Less=0` / `Equal=1` / `Greater=2`. Even with a clean
/// Ordering consumer the producer is LEFT HONEST: a tag-only relabel would
/// be value-faithful, but the prelude names would disagree with the
/// comparison's MEANING ("Less" firing on equal inputs).
#[test]
fn leaves_scrambled_comparator_honest() {
    // branch order: then=tag2, mid=tag0, else=tag1
    let expr = PseudoExpr::Let {
        name: "cmp".to_string(),
        id: Some(VarId::new(7)),
        value: PBox::new(comparator_lambda(2, 0, 1)),
        body: PBox::new(ordering_consumer(7)),
    };
    let out = recover_ordering_comparator(expr.clone());
    assert_eq!(out, expr, "scrambled tags must fail the semantic gate");
}

/// Operand-swapped canonical comparator: `b > a` ≡ `a < b` — the
/// orientation-aware relation classification accepts it.
#[test]
fn recovers_operand_swapped_canonical_comparator() {
    let lambda = PseudoExpr::Lambda {
        params: vec![binder("a", 1), binder("b", 2)],
        body: PBox::new(PseudoExpr::If {
            // b > a  ≡  a < b → Less (tag 0)
            condition: PBox::new(cmp(2, 1, BinaryOp::Gt)),
            then_branch: PBox::new(unknown_constr(0)),
            else_branch: PBox::new(PseudoExpr::If {
                condition: PBox::new(cmp(1, 2, BinaryOp::Eq)),
                then_branch: PBox::new(unknown_constr(1)),
                else_branch: PBox::new(unknown_constr(2)),
            }),
        }),
    };
    let expr = PseudoExpr::Let {
        name: "cmp".to_string(),
        id: Some(VarId::new(7)),
        value: PBox::new(lambda),
        body: PBox::new(ordering_consumer(7)),
    };
    let out = recover_ordering_comparator(expr);
    let PseudoExpr::Let { value, .. } = &out else {
        panic!("expected Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.as_ref() else {
        panic!("expected Lambda")
    };
    let PseudoExpr::If { then_branch, .. } = body.as_ref() else {
        panic!("expected If");
    };
    assert_branch_is(then_branch, KnownConstructor::Less);
}

/// A comparator whose conditions are NOT direct param comparisons
/// (a cross-multiplied rational compare) fails the semantic gate
/// even when the Constr tags happen to be 0/1/2.
#[test]
fn leaves_non_param_condition_comparator_honest() {
    let lambda = PseudoExpr::Lambda {
        params: vec![binder("a", 1), binder("b", 2)],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Lt,
                left: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Mul,
                    left: PBox::new(var("a", 1)),
                    right: PBox::new(var("b", 2)),
                }),
                right: PBox::new(var("b", 2)),
            }),
            then_branch: PBox::new(unknown_constr(0)),
            else_branch: PBox::new(PseudoExpr::If {
                condition: PBox::new(cmp(1, 2, BinaryOp::Eq)),
                then_branch: PBox::new(unknown_constr(1)),
                else_branch: PBox::new(unknown_constr(2)),
            }),
        }),
    };
    let expr = PseudoExpr::Let {
        name: "cmp".to_string(),
        id: Some(VarId::new(7)),
        value: PBox::new(lambda),
        body: PBox::new(ordering_consumer(7)),
    };
    let out = recover_ordering_comparator(expr.clone());
    assert_eq!(out, expr);
}

/// A comparator consumed by a BOOLEAN equality (`cmp(..) == Constr<0>`),
/// NOT a clean Ordering `when` → left honest (no relabel).
#[test]
fn leaves_comparator_honest_without_ordering_consumer() {
    let consumer = PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("cmp", 7)),
            args: vec![var("x", 100), var("y", 101)].into(),
        }),
        right: PBox::new(unknown_constr(0)),
    };
    let expr = PseudoExpr::Let {
        name: "cmp".to_string(),
        id: Some(VarId::new(7)),
        value: PBox::new(comparator_lambda(0, 1, 2)),
        body: PBox::new(consumer),
    };
    let out = recover_ordering_comparator(expr.clone());
    assert_eq!(
        out, expr,
        "no Ordering consumer ⇒ comparator must stay honest"
    );
}

/// A comparator consumed by a `when` that has a WILDCARD arm → left
/// honest: the wildcard means it is NOT a clean 3-tag Ordering dispatch.
#[test]
fn leaves_comparator_honest_with_wildcard_consumer() {
    let consumer = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("cmp", 7)),
            args: vec![var("x", 100), var("y", 101)].into(),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause::new(ordering_when_pattern(0), var("A", 200)),
            WhenClause::new(ordering_when_pattern(1), var("B", 201)),
            WhenClause::new(WhenPattern::Wildcard, var("C", 202)),
        ],
    };
    let expr = PseudoExpr::Let {
        name: "cmp".to_string(),
        id: Some(VarId::new(7)),
        value: PBox::new(comparator_lambda(0, 1, 2)),
        body: PBox::new(consumer),
    };
    let out = recover_ordering_comparator(expr.clone());
    assert_eq!(out, expr, "wildcard consumer ⇒ comparator must stay honest");
}

/// A consumer whose 3 arms include a church-bool `Known(True)`/
/// `Known(False)` pattern (even if tags cover {0,1,2}) is a church-bool
/// reader, NOT a clean Ordering dispatch → producer left honest.
#[test]
fn leaves_comparator_honest_with_church_bool_consumer() {
    let church_bool_pattern = |kc: KnownConstructor| WhenPattern::Constructor {
        type_hint: None,
        tag: kc.expected_tag(),
        fields: Vec::new(),
        shape: ConstructorShape::Known(kc),
    };
    let consumer = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("cmp", 7)),
            args: vec![var("x", 100), var("y", 101)].into(),
        }),
        subject_name: None,
        clauses: vec![
            // False(tag0), True(tag1), Greater(tag2) — tags cover {0,1,2}
            // but the church-bool arms disqualify it.
            WhenClause::new(church_bool_pattern(KnownConstructor::False), var("A", 200)),
            WhenClause::new(church_bool_pattern(KnownConstructor::True), var("B", 201)),
            WhenClause::new(ordering_when_pattern(2), var("C", 202)),
        ],
    };
    let expr = PseudoExpr::Let {
        name: "cmp".to_string(),
        id: Some(VarId::new(7)),
        value: PBox::new(comparator_lambda(0, 1, 2)),
        body: PBox::new(consumer),
    };
    let out = recover_ordering_comparator(expr.clone());
    assert_eq!(
        out, expr,
        "church-bool consumer arms ⇒ comparator must stay honest"
    );
}

/// Tags do NOT cover {0,1,2} (e.g. {0,1,1}) → no relabel even with a
/// clean-looking consumer (defensive; such a body isn't a real 3-way
/// Ordering).
#[test]
fn leaves_non_three_distinct_tags_honest() {
    let expr = PseudoExpr::Let {
        name: "cmp".to_string(),
        id: Some(VarId::new(7)),
        value: PBox::new(comparator_lambda(0, 1, 1)),
        body: PBox::new(ordering_consumer(7)),
    };
    let out = recover_ordering_comparator(expr.clone());
    // consumer is collected, but body tags {0,1,1} ≠ {0,1,2} ⇒ body unchanged
    let PseudoExpr::Let { value, .. } = &out else {
        panic!("expected Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.as_ref() else {
        panic!("expected Lambda")
    };
    let PseudoExpr::If { then_branch, .. } = body.as_ref() else {
        panic!("expected If")
    };
    assert!(
        matches!(
            then_branch.as_ref(),
            PseudoExpr::Constr {
                shape: ConstructorShape::Unknown { .. },
                ..
            }
        ),
        "tags not covering {{0,1,2}} must stay Unknown stub Constrs"
    );
}

/// A consumer whose 3 arms are un-named `Unknown { tag }` stubs (NOT
/// `Known(Less/Equal/Greater)`) is NOT an established Ordering dispatch.
/// Relabeling the producer while the consumer still renders
/// `Unknown_E_0_<tag>` would be a NAME disagreement → the comparator must
/// stay honest.
#[test]
fn leaves_comparator_honest_with_unknown_stub_consumer() {
    let unknown_arm = |tag: usize| {
        WhenClause::new(
            WhenPattern::Constructor {
                type_hint: None,
                tag,
                fields: Vec::new(),
                shape: ConstructorShape::unknown_data(tag, 0),
            },
            var("A", 200 + tag as u32),
        )
    };
    let consumer = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("cmp", 7)),
            args: vec![var("x", 100), var("y", 101)].into(),
        }),
        subject_name: None,
        clauses: vec![unknown_arm(0), unknown_arm(1), unknown_arm(2)],
    };
    let expr = PseudoExpr::Let {
        name: "cmp".to_string(),
        id: Some(VarId::new(7)),
        value: PBox::new(comparator_lambda(0, 1, 2)),
        body: PBox::new(consumer),
    };
    let out = recover_ordering_comparator(expr.clone());
    assert_eq!(
        out, expr,
        "un-named Unknown stub consumer ⇒ comparator must stay honest"
    );
}

/// A helper consumed by BOTH a clean Ordering `when` AND another `when` that
/// reads the result as a church-bool `True`/`False` is matched under two
/// conflicting arm-name maps. Relabeling its producer to Ordering would
/// disagree with the church-bool consumer → the helper is disqualified and
/// the comparator stays honest.
#[test]
fn disqualifies_helper_with_mixed_ordering_and_bool_when() {
    let church_bool_pattern = |kc: KnownConstructor| WhenPattern::Constructor {
        type_hint: None,
        tag: kc.expected_tag(),
        fields: Vec::new(),
        shape: ConstructorShape::Known(kc),
    };
    let bool_when = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("cmp", 7)),
            args: vec![var("x", 110), var("y", 111)].into(),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause::new(church_bool_pattern(KnownConstructor::False), var("A", 200)),
            WhenClause::new(church_bool_pattern(KnownConstructor::True), var("B", 201)),
            WhenClause::new(ordering_when_pattern(2), var("C", 202)),
        ],
    };
    // Both consumers of the SAME fid 7 live in one tree.
    let body = PseudoExpr::Let {
        name: "_a".to_string(),
        id: None,
        value: PBox::new(ordering_consumer(7)),
        body: PBox::new(bool_when),
    };
    let expr = PseudoExpr::Let {
        name: "cmp".to_string(),
        id: Some(VarId::new(7)),
        value: PBox::new(comparator_lambda(0, 1, 2)),
        body: PBox::new(body),
    };
    let out = recover_ordering_comparator(expr.clone());
    assert_eq!(
        out, expr,
        "a helper matched as BOTH Ordering and church-bool must stay honest"
    );
}
