use super::*;
use crate::pseudo::mid::expr::{MidExpr, MidLiteral};
use crate::pseudo::var_id::VarId;

fn lit(id: MidExprId, value: i64) -> MidExpr {
    MidExpr::Lit {
        id,
        value: MidLiteral::Integer(value.into()),
    }
}

#[test]
fn test_validate_mid_invariants_accepts_well_formed_tree() {
    let mut provenance = ProvenanceBuilder::new();
    let let_id = provenance.fresh_id();
    let value_id = provenance.fresh_id();
    let body_id = provenance.fresh_id();
    provenance.link(let_id, 10);
    provenance.link(value_id, 11);
    provenance.link(body_id, 12);

    let expr = MidExpr::Let {
        id: let_id,
        var: VarId::new(0),
        value: Box::new(lit(value_id, 42)),
        body: Box::new(MidExpr::Var {
            id: body_id,
            var: VarId::new(0),
        }),
        use_count: 1,
    };

    assert!(validate_mid_invariants(&expr, &provenance).is_ok());
}

#[test]
fn test_validate_mid_invariants_rejects_duplicate_ids() {
    let mut provenance = ProvenanceBuilder::new();
    let let_id = provenance.fresh_id();
    let shared_id = provenance.fresh_id();
    provenance.link(let_id, 10);
    provenance.link(shared_id, 11);

    let expr = MidExpr::Let {
        id: let_id,
        var: VarId::new(0),
        value: Box::new(lit(shared_id, 42)),
        body: Box::new(MidExpr::Var {
            id: shared_id,
            var: VarId::new(0),
        }),
        use_count: 1,
    };

    let errors = validate_mid_invariants(&expr, &provenance).unwrap_err();
    assert!(
        errors.iter().any(
            |error| matches!(error, MidInvariantError::DuplicateId { id } if id == &shared_id)
        )
    );
}

#[test]
fn test_validate_mid_invariants_rejects_missing_provenance() {
    let expr = MidExpr::Lit {
        id: MidExprId::new(999),
        value: MidLiteral::Integer(1.into()),
    };

    let errors = validate_mid_invariants(&expr, &ProvenanceBuilder::new()).unwrap_err();
    assert_eq!(
        errors,
        vec![MidInvariantError::MissingProvenance {
            id: MidExprId::new(999),
        }]
    );
}

#[test]
fn test_enforce_mid_invariants_returns_internal_error() {
    let expr = MidExpr::Lit {
        id: MidExprId::new(999),
        value: MidLiteral::Integer(1.into()),
    };

    let err = enforce_mid_invariants("test_stage", &expr, &ProvenanceBuilder::new())
        .expect_err("expected missing provenance to return an internal error");

    assert!(
        matches!(err, DecompileError::Internal(message) if message.contains("test_stage") && message.contains("missing provenance"))
    );
}
