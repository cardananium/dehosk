use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

fn make_pattern_with_n_binders(n: usize) -> (WhenPattern, Vec<VarId>) {
    let ids: Vec<VarId> = (0..n).map(|_| VarId::fresh_binding()).collect();
    let fields: Vec<Binder> = ids
        .iter()
        .enumerate()
        .map(|(i, id)| Binder::new(format!("field_{}", i), *id))
        .collect();
    let pat = WhenPattern::Constructor {
        type_hint: None,
        tag: 0,
        fields,
        shape: ConstructorShape::unknown_data(0, n),
    };
    (pat, ids)
}

#[test]
fn renames_v1_tx_info_arity_10_pattern_and_body_uses() {
    let tx_info_id = VarId::new(50000);
    let (pat, ids) = make_pattern_with_n_binders(10);
    // Body references the first binder (the "inputs" slot).
    let body = PseudoExpr::var_with_id("field_0", ids[0]);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("tx_info", tx_info_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: pat,
            guard: None,
            body,
        }],
    };

    let rewritten = rename_tx_info_binders(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!()
    };
    assert_eq!(fields.len(), 10);
    assert_eq!(fields[0].to_string(), "inputs");
    assert_eq!(fields[1].to_string(), "outputs");
    assert_eq!(fields[2].to_string(), "fee");
    // Slot 9 is the ledger's `id` (`uplc`'s `TxInfo::V1` serialises it
    // last), rendered as `transaction_id`.
    assert_eq!(fields[9].to_string(), "transaction_id");
    // The body's Var ref to the first binder should be renamed.
    let PseudoExpr::Var { name, id: Some(id) } = &clauses[0].body else {
        panic!()
    };
    assert_eq!(name, "inputs");
    assert_eq!(*id, ids[0]);
}

#[test]
fn does_not_rename_when_subject_is_not_tx_info() {
    let subject_id = VarId::new(51000);
    let (pat, _ids) = make_pattern_with_n_binders(10);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("some_other", subject_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: pat,
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };
    let rewritten = rename_tx_info_binders(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!()
    };
    assert_eq!(
        fields[0].to_string(),
        "field_0",
        "non-tx_info subject must not trigger rename"
    );
}

#[test]
fn does_not_rename_wrong_arity_pattern() {
    // tx_info subject but arity-5 pattern — doesn't match any canonical
    // schema, must stay as-is.
    let tx_info_id = VarId::new(52000);
    let (pat, _ids) = make_pattern_with_n_binders(5);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("tx_info", tx_info_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: pat,
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };
    let rewritten = rename_tx_info_binders(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!()
    };
    assert_eq!(fields[0].to_string(), "field_0", "arity-5 must not rename");
}

#[test]
fn renames_v2_tx_info_arity_12() {
    let tx_info_id = VarId::new(53000);
    let (pat, _ids) = make_pattern_with_n_binders(12);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("tx_info", tx_info_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: pat,
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };
    let rewritten = rename_tx_info_binders(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!()
    };
    assert_eq!(
        fields[1].to_string(),
        "reference_inputs",
        "V2 has reference_inputs at index 1"
    );
    assert_eq!(
        fields[9].to_string(),
        "redeemers",
        "V2 has redeemers at index 9"
    );
}
