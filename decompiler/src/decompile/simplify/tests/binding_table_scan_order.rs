//! The binding table is SCANNED, not just looked up — so its order is part of
//! the decompiler's contract.
//!
//! `destructure_when_fields` searches `constructors.fields_bindings` for a
//! binding that aliases the subject's `.fields`. Scripts alias the same
//! `x.fields` many times, so the scan has several right answers and must
//! commit to one. Hashed order would let the process's hash seed choose,
//! drifting the whole decompilation: the same script produces two different
//! texts across runs. Binding-id order picks the earliest-allocated alias.

use super::*;
use crate::pseudo::ast::PBox;

/// Build one alias-heavy scenario and return how many pattern fields the
/// destructure bound. That count identifies WHICH alias the scan picked:
/// only the lowest-id alias is indexed at `[0]` (1 field), only the
/// highest-id alias is indexed at `[1]` (2 fields), and picking any of the
/// 14 aliases in between leaves the clause untouched (0 fields).
fn fields_bound_by_alias_scan(round: u32) -> usize {
    const ALIASES: u32 = 16;
    let base = 8_000 + round * 100;
    let subject_id = VarId::new(7_000 + round);
    let subject = PseudoExpr::var_with_id("x", subject_id);
    let subject_name: Option<Binder> = None;

    let mut simplifier = Simplifier::with_safe_mode(false);
    // Insert high id first: if insertion order were what made the scan
    // deterministic, this test would pass for the wrong reason.
    for k in (0..ALIASES).rev() {
        simplifier.constructors.fields_bindings.insert(
            VarId::new(base + k),
            PseudoExpr::var_with_id("x", subject_id),
        );
    }

    let body = PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::var_with_id("fv_lowest", VarId::new(base))),
            index: 0,
        }),
        right: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::var_with_id(
                "fv_highest",
                VarId::new(base + ALIASES - 1),
            )),
            index: 1,
        }),
    };

    let clauses = simplifier.destructure_when_fields(
        &subject,
        &subject_name,
        vec![WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
            body,
        )],
    );

    match &clauses[0].pattern {
        WhenPattern::Constructor { fields, .. } => fields.len(),
        other => panic!("expected a constructor pattern, got {other:?}"),
    }
}

#[test]
fn fields_alias_scan_resolves_to_the_earliest_alias_every_round() {
    // 16 independent scenarios. One round could agree with the ordered answer
    // by luck; sixteen in a row cannot.
    for round in 0..16 {
        assert_eq!(
            fields_bound_by_alias_scan(round),
            1,
            "round {round}: the alias scan must resolve to the lowest-id \
             `x.fields` alias, which is the one indexed at [0]"
        );
    }
}
