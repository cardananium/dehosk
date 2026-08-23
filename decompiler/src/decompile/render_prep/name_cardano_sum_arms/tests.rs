use super::*;
use crate::builtins::BuiltinId;
use crate::decompile::render_prep::RenderCtx;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

fn ctor_clause(tag: usize, field_binders: &[(&str, VarId)], body: PseudoExpr) -> WhenClause {
    let fields: Vec<Binder> = field_binders
        .iter()
        .map(|(n, id)| Binder::new(*n, *id))
        .collect();
    WhenClause {
        pattern: WhenPattern::Constructor {
            type_hint: None,
            tag,
            shape: ConstructorShape::from_name_and_tag(None, tag, fields.len()),
            fields,
        },
        guard: None,
        body,
    }
}

fn when_on(subject: &str, sid: VarId, clauses: Vec<WhenClause>) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id(subject, sid)),
        subject_name: None,
        clauses,
    }
}

/// `when <record>.<field> is { … }` — a Cardano-sum FIELD ACCESS subject
/// (`script_context.script_info`); `field` becomes a `NamedField`.
fn when_on_field(record: &str, rid: VarId, field: &str, clauses: Vec<WhenClause>) -> PseudoExpr {
    let subject = PseudoExpr::field_access(PseudoExpr::var_with_id(record, rid), field);
    PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses,
    }
}

fn clause_type_hint(c: &WhenClause) -> Option<&TypeHintId> {
    match &c.pattern {
        WhenPattern::Constructor { type_hint, .. } => type_hint.as_ref(),
        _ => None,
    }
}

fn clause_field_names(c: &WhenClause) -> Vec<String> {
    match &c.pattern {
        WhenPattern::Constructor { fields, .. } => {
            fields.iter().map(|b| b.as_str().to_string()).collect()
        }
        _ => vec![],
    }
}

#[test]
fn names_interval_bound_type_arms_and_renames_finite_payload() {
    // when bound_type is {
    //   Constr<0> -> a            (NegativeInfinity, nullary)
    //   Constr<1>(field_0) -> field_0   (Finite, payload)
    //   Constr<2> -> b            (PositiveInfinity, nullary)
    // }
    let sid = VarId::new(8000);
    let fid = VarId::new(8001);
    let expr = when_on(
        "bound_type",
        sid,
        vec![
            ctor_clause(0, &[], PseudoExpr::var_with_id("a", VarId::new(8010))),
            ctor_clause(
                1,
                &[("field_0", fid)],
                PseudoExpr::var_with_id("field_0", fid),
            ),
            ctor_clause(2, &[], PseudoExpr::var_with_id("b", VarId::new(8011))),
        ],
    );

    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &RenderCtx::at(None));
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };

    let ibt = TypeHintId::new("interval_bound_type");
    assert_eq!(
        clause_type_hint(&clauses[0]),
        Some(&ibt),
        "NegInf arm hinted"
    );
    assert_eq!(
        clause_type_hint(&clauses[1]),
        Some(&ibt),
        "Finite arm hinted"
    );
    assert_eq!(
        clause_type_hint(&clauses[2]),
        Some(&ibt),
        "PosInf arm hinted"
    );

    // Finite payload binder renamed `field_0` -> `value`, body ref rewired.
    assert_eq!(clause_field_names(&clauses[1]), vec!["value".to_string()]);
    let PseudoExpr::Var { name, id } = &clauses[1].body else {
        panic!("expected the Finite body Var");
    };
    assert_eq!(name, "value");
    assert_eq!(*id, Some(fid), "VarId preserved on rewire");
}

#[test]
fn renames_purpose_payload_keeping_existing_hint() {
    // when purpose is { Constr<0>(field_0) -> field_0 }  (Minting payload)
    let sid = VarId::new(8100);
    let fid = VarId::new(8101);
    // Pre-existing hint as the early pass would leave it.
    let existing = TypeHintId::new("purpose");
    let mut clause = ctor_clause(
        0,
        &[("field_0", fid)],
        PseudoExpr::var_with_id("field_0", fid),
    );
    if let WhenPattern::Constructor { type_hint, .. } = &mut clause.pattern {
        *type_hint = Some(existing.clone());
    }
    let expr = when_on("purpose", sid, vec![clause]);

    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &RenderCtx::at(None));
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    assert_eq!(
        clause_type_hint(&clauses[0]),
        Some(&existing),
        "existing hint kept"
    );
    assert_eq!(
        clause_field_names(&clauses[0]),
        vec!["policy_id".to_string()],
        "Minting payload renamed to policy_id"
    );
}

#[test]
fn skips_arm_with_arity_mismatch() {
    // when bound_type is { Constr<0>(x, y) -> ... } — NegativeInfinity is
    // nullary (arity 0), so a 2-arg arm cannot be it: leave untouched.
    let sid = VarId::new(8200);
    let expr = when_on(
        "bound_type",
        sid,
        vec![ctor_clause(
            0,
            &[("x", VarId::new(8201)), ("y", VarId::new(8202))],
            PseudoExpr::Unit,
        )],
    );
    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &RenderCtx::at(None));
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    assert_eq!(
        clause_type_hint(&clauses[0]),
        None,
        "arity mismatch ⇒ no hint"
    );
    assert_eq!(
        clause_field_names(&clauses[0]),
        vec!["x".to_string(), "y".to_string()]
    );
}

#[test]
fn all_or_nothing_leaves_when_untouched_if_any_arm_mismatches() {
    // when bound_type is {
    //   Constr<1>(field_0) -> ...   (Finite, arity ok)
    //   Constr<2>(a, b) -> ...      (PositiveInfinity is nullary — arity 2 wrong)
    // }
    // One bad arm ⇒ the whole `when` is left untouched (no mixed types).
    let sid = VarId::new(8600);
    let expr = when_on(
        "bound_type",
        sid,
        vec![
            ctor_clause(1, &[("field_0", VarId::new(8601))], PseudoExpr::Unit),
            ctor_clause(
                2,
                &[("a", VarId::new(8602)), ("b", VarId::new(8603))],
                PseudoExpr::Unit,
            ),
        ],
    );
    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &RenderCtx::at(None));
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    assert_eq!(
        clause_type_hint(&clauses[0]),
        None,
        "good arm left untouched"
    );
    assert_eq!(clause_field_names(&clauses[0]), vec!["field_0".to_string()]);
    assert_eq!(
        clause_type_hint(&clauses[1]),
        None,
        "bad arm left untouched"
    );
}

#[test]
fn names_v1_v2_certificate_arms_and_renames_payloads() {
    // when certificate is {
    //   Constr<2>(field_0, field_1) -> field_0   (CredentialDelegation)
    //   Constr<5> -> ...                         (Governance, nullary)
    // }
    // Certificate requires an EXPLICIT V1/V2 render version (it is not
    // activated by the None→V2 default — see `known_ctor_arity`).
    use crate::decompile::ScriptVersion;
    let ctx = RenderCtx::at(Some(ScriptVersion::PlutusV2));

    let sid = VarId::new(8700);
    let a = VarId::new(8701);
    let b = VarId::new(8702);
    let expr = when_on(
        "certificate",
        sid,
        vec![
            ctor_clause(
                2,
                &[("field_0", a), ("field_1", b)],
                PseudoExpr::var_with_id("field_0", a),
            ),
            ctor_clause(5, &[], PseudoExpr::Unit),
        ],
    );

    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &ctx);
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    let cert = TypeHintId::new("certificate");
    assert_eq!(
        clause_type_hint(&clauses[0]),
        Some(&cert),
        "CredentialDelegation arm hinted"
    );
    assert_eq!(
        clause_type_hint(&clauses[1]),
        Some(&cert),
        "Governance (nullary) arm hinted"
    );
    assert_eq!(
        clause_field_names(&clauses[0]),
        vec!["delegator".to_string(), "delegatee".to_string()],
        "CredentialDelegation payloads named"
    );
    // body ref to field_0 rewired to delegator
    let PseudoExpr::Var { name, .. } = &clauses[0].body else {
        panic!()
    };
    assert_eq!(name, "delegator");
    assert!(
        clause_field_names(&clauses[1]).is_empty(),
        "nullary Governance has no fields"
    );
}

#[test]
fn skips_non_cardano_subject() {
    // A user binder that is not a Cardano sum subject — untouched.
    let sid = VarId::new(8300);
    let expr = when_on(
        "my_thing",
        sid,
        vec![ctor_clause(
            0,
            &[("field_0", VarId::new(8301))],
            PseudoExpr::Unit,
        )],
    );
    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &RenderCtx::at(None));
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    assert_eq!(clause_type_hint(&clauses[0]), None);
    assert_eq!(clause_field_names(&clauses[0]), vec!["field_0".to_string()]);
}

#[test]
fn leaves_when_alone_when_an_arm_has_a_user_blueprint_hint() {
    // An arm carrying a real (non-stub) hint that names a DIFFERENT type
    // means the subject was typed as a user ADT: Cardano names would build
    // a hybrid arm, so the whole `when` is skipped.
    let sid = VarId::new(8500);
    let fid = VarId::new(8501);
    let user_hint = TypeHintId::new("MyUserType");
    let mut clause = ctor_clause(1, &[("field_0", fid)], PseudoExpr::Unit);
    if let WhenPattern::Constructor { type_hint, .. } = &mut clause.pattern {
        *type_hint = Some(user_hint.clone());
    }
    let expr = when_on("bound_type", sid, vec![clause]);

    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &RenderCtx::at(None));
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    assert_eq!(
        clause_type_hint(&clauses[0]),
        Some(&user_hint),
        "user hint preserved"
    );
    assert_eq!(
        clause_field_names(&clauses[0]),
        vec!["field_0".to_string()],
        "payload not renamed when respecting a user hint"
    );
}

#[test]
fn does_not_clobber_meaningful_payload_binder() {
    // If the payload binder already has a non-synthetic name, keep it.
    let sid = VarId::new(8400);
    let fid = VarId::new(8401);
    let expr = when_on(
        "bound_type",
        sid,
        vec![ctor_clause(1, &[("my_value", fid)], PseudoExpr::Unit)],
    );
    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &RenderCtx::at(None));
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    // Still hinted (Finite), but the user name is preserved.
    assert_eq!(
        clause_type_hint(&clauses[0]),
        Some(&TypeHintId::new("interval_bound_type"))
    );
    assert_eq!(
        clause_field_names(&clauses[0]),
        vec!["my_value".to_string()]
    );
}

// ==================================================================
// V3 Cardano-sum naming over a FIELD-ACCESS subject + the
// version-gated GovernanceAction activation.
// ==================================================================

#[test]
fn names_script_info_proposing_arm_over_field_access_subject_v3() {
    // when script_context.script_info is {
    //   Constr<5>(field_0, field_1) -> field_1   (Proposing: index, proposal_procedure)
    // }
    // The subject is a FIELD ACCESS (`<ctx>.script_info`), not a bare
    // binder — the V3 idiomatic dispatch. `script_info` resolves to
    // SumTypeId::ScriptInfo, whose table is only populated under V3.
    use crate::decompile::ScriptVersion;
    let ctx = RenderCtx::at(Some(ScriptVersion::PlutusV3));

    let rid = VarId::new(8800);
    let idx = VarId::new(8801);
    let proposal = VarId::new(8802);
    let expr = when_on_field(
        "script_context",
        rid,
        "script_info",
        vec![ctor_clause(
            5,
            &[("field_0", idx), ("field_1", proposal)],
            PseudoExpr::var_with_id("field_1", proposal),
        )],
    );

    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &ctx);
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    let si = TypeHintId::new("script_info");
    assert_eq!(
        clause_type_hint(&clauses[0]),
        Some(&si),
        "Proposing arm hinted ScriptInfo over a field-access subject"
    );
    assert_eq!(
        clause_field_names(&clauses[0]),
        vec!["index".to_string(), "proposal_procedure".to_string()],
        "Proposing payloads named index, proposal_procedure"
    );
    // body ref to field_1 rewired to proposal_procedure
    let PseudoExpr::Var { name, id } = &clauses[0].body else {
        panic!()
    };
    assert_eq!(name, "proposal_procedure");
    assert_eq!(*id, Some(proposal), "VarId preserved on rewire");
}

#[test]
fn field_access_subject_not_named_under_non_v3() {
    // The SAME field-access ScriptInfo `when` under the (V1/V2) default
    // must NOT be named: the ScriptInfo field table only returns Some
    // under V3, so every arm's arity is unknown -> honest stub.
    let ctx = RenderCtx::at(None);

    let rid = VarId::new(8810);
    let expr = when_on_field(
        "script_context",
        rid,
        "script_info",
        vec![ctor_clause(
            5,
            &[("field_0", VarId::new(8811)), ("field_1", VarId::new(8812))],
            PseudoExpr::Unit,
        )],
    );

    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &ctx);
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    assert_eq!(
        clause_type_hint(&clauses[0]),
        None,
        "ScriptInfo arm not named under the non-V3 default"
    );
    assert_eq!(
        clause_field_names(&clauses[0]),
        vec!["field_0".to_string(), "field_1".to_string()]
    );
}

#[test]
fn names_governance_action_protocol_parameters_arm_v3() {
    // when governance_action is {
    //   Constr<0>(field_0, field_1, field_2) -> field_1
    // }  (ProtocolParameters: ancestor, new_parameters, guardrails)
    // GovernanceAction requires an EXPLICIT V3 render version (it is NOT
    // activated by the None->V2 default — see `known_ctor_arity`).
    use crate::decompile::ScriptVersion;
    let ctx = RenderCtx::at(Some(ScriptVersion::PlutusV3));

    let sid = VarId::new(8900);
    let a = VarId::new(8901);
    let b = VarId::new(8902);
    let c = VarId::new(8903);
    let expr = when_on(
        "governance_action",
        sid,
        vec![ctor_clause(
            0,
            &[("field_0", a), ("field_1", b), ("field_2", c)],
            PseudoExpr::var_with_id("field_1", b),
        )],
    );

    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &ctx);
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    let ga = TypeHintId::new("governance_action");
    assert_eq!(
        clause_type_hint(&clauses[0]),
        Some(&ga),
        "ProtocolParameters arm hinted GovernanceAction"
    );
    assert_eq!(
        clause_field_names(&clauses[0]),
        vec![
            "ancestor".to_string(),
            "new_parameters".to_string(),
            "guardrails".to_string()
        ],
        "ProtocolParameters payloads named"
    );
    let PseudoExpr::Var { name, .. } = &clauses[0].body else {
        panic!()
    };
    assert_eq!(name, "new_parameters", "body ref rewired");
}

#[test]
fn skips_governance_action_arm_with_arity_mismatch_v3() {
    // ProtocolParameters (tag 0) is arity 3; a 2-arg arm cannot be it —
    // even under V3, leave the whole `when` untouched (all-or-nothing).
    use crate::decompile::ScriptVersion;
    let ctx = RenderCtx::at(Some(ScriptVersion::PlutusV3));

    let sid = VarId::new(8910);
    let expr = when_on(
        "governance_action",
        sid,
        vec![ctor_clause(
            0,
            &[("a", VarId::new(8911)), ("b", VarId::new(8912))],
            PseudoExpr::Unit,
        )],
    );

    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &ctx);
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    assert_eq!(
        clause_type_hint(&clauses[0]),
        None,
        "arity mismatch ⇒ GovernanceAction arm not named"
    );
    assert_eq!(
        clause_field_names(&clauses[0]),
        vec!["a".to_string(), "b".to_string()]
    );
}

#[test]
fn governance_action_not_named_under_non_v3_default() {
    // GovernanceAction must NEVER be activated by the None->V2 default:
    // the field table returns None outside V3, AND the explicit V3 gate in
    // `known_ctor_arity` blocks it.
    let ctx = RenderCtx::at(None);

    let sid = VarId::new(8920);
    let expr = when_on(
        "governance_action",
        sid,
        vec![ctor_clause(
            0,
            &[
                ("field_0", VarId::new(8921)),
                ("field_1", VarId::new(8922)),
                ("field_2", VarId::new(8923)),
            ],
            PseudoExpr::Unit,
        )],
    );

    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &ctx);
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    assert_eq!(
        clause_type_hint(&clauses[0]),
        None,
        "GovernanceAction not named under the non-V3 default"
    );
    assert_eq!(
        clause_field_names(&clauses[0]),
        vec![
            "field_0".to_string(),
            "field_1".to_string(),
            "field_2".to_string()
        ]
    );
}

// ==================================================================
// Credential conflation handler (the ScalarKind GATE).
//
// `Credential` (`VerificationKey(ByteArray)` / `Script(ByteArray)`) is the
// merged 2-variant stub `Unknown_S_*`. A subject typing to
// `SumTypeId::Credential` is NECESSARY but NOT SUFFICIENT: the arms are named
// only when EVERY arm's field-0 PROVABLY decodes as `ByteArray`. The Int /
// conflated site must stay the honest `Unknown_S_*`.
// ==================================================================

const CREDENTIAL_STUB: &str = "Unknown_S_1";

/// `un_b_data(Var{vid})` — a `ByteArray` decode of the arm field.
fn un_b_of(vid: VarId) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnByteArray,
        args: vec![PseudoExpr::var_with_id("field_0", vid)].into(),
    }
}

/// `un_i_data(Var{vid})` — an `Int` decode of the arm field.
fn un_i_of(vid: VarId) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnInt,
        args: vec![PseudoExpr::var_with_id("field_0", vid)].into(),
    }
}

/// A stub-hinted (`Unknown_S_1`) 2-variant `when <subject> is { … }`: tag 0 +
/// tag 1, each binding `field_0` to the given decode body. This is the shape
/// the Credential gate keys its ScalarKind lookup on.
fn credential_when(subject: &str, sid: VarId, body0: PseudoExpr, body1: PseudoExpr) -> PseudoExpr {
    let hint = TypeHintId::new(CREDENTIAL_STUB);
    let mk = |tag: usize, fid: VarId, body: PseudoExpr| WhenClause {
        pattern: WhenPattern::Constructor {
            type_hint: Some(hint.clone()),
            tag,
            shape: ConstructorShape::unknown_data(tag, 1),
            fields: vec![Binder::new("field_0", fid)],
        },
        guard: None,
        body,
    };
    PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id(subject, sid)),
        subject_name: None,
        clauses: vec![
            mk(0, VarId::new(9001), body0),
            mk(1, VarId::new(9002), body1),
        ],
    }
}

/// GATE FIRES: a `credential` subject whose BOTH arms decode field-0 as
/// `ByteArray` → named `Credential` (hint stamped, payload renamed `hash`).
#[test]
fn names_credential_arms_when_both_fields_bytearray() {
    let expr = credential_when(
        "credential",
        VarId::new(9000),
        un_b_of(VarId::new(9001)),
        un_b_of(VarId::new(9002)),
    );
    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &RenderCtx::at(None));
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    let cred = TypeHintId::new("credential");
    assert_eq!(
        clause_type_hint(&clauses[0]),
        Some(&cred),
        "VerificationKey arm hinted Credential"
    );
    assert_eq!(
        clause_type_hint(&clauses[1]),
        Some(&cred),
        "Script arm hinted Credential"
    );
    assert_eq!(
        clause_field_names(&clauses[0]),
        vec!["hash".to_string()],
        "Credential tag-0 payload renamed to hash"
    );
    assert_eq!(
        clause_field_names(&clauses[1]),
        vec!["hash".to_string()],
        "Credential tag-1 payload renamed to hash"
    );
}

/// A `credential` subject where one arm decodes field-0 as `ByteArray` and
/// the other as `Int`: the gate requires `ByteArray` on BOTH arms, so the
/// whole `when` stays the honest `Unknown_S_1`.
#[test]
fn leaves_credential_stub_when_one_arm_is_int() {
    let expr = credential_when(
        "credential",
        VarId::new(9100),
        un_b_of(VarId::new(9001)),
        un_i_of(VarId::new(9002)), // tag 1 field decoded as Int
    );
    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &RenderCtx::at(None));
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    assert_eq!(
        clause_type_hint(&clauses[0]),
        Some(&TypeHintId::new(CREDENTIAL_STUB)),
        "Int conflation ⇒ tag-0 arm left as the honest stub"
    );
    assert_eq!(
        clause_type_hint(&clauses[1]),
        Some(&TypeHintId::new(CREDENTIAL_STUB)),
        "Int conflation ⇒ tag-1 arm left as the honest stub"
    );
    assert_eq!(clause_field_names(&clauses[0]), vec!["field_0".to_string()]);
    assert_eq!(clause_field_names(&clauses[1]), vec!["field_0".to_string()]);
}

/// The same merged-stub key decoded as `un_b_data` at one site and
/// `un_i_data` at another (what `merge_isomorphic_stub_adts` produces) ⇒
/// `Conflict` for that key ⇒ the Credential gate fail-closes on EVERY site
/// of the stub, including the genuinely-ByteArray one.
#[test]
fn leaves_credential_stub_when_key_conflicts_across_sites() {
    let hint = TypeHintId::new(CREDENTIAL_STUB);
    // The credential `when` (both arms ByteArray, would-pass in isolation).
    let cred = credential_when(
        "credential",
        VarId::new(9200),
        un_b_of(VarId::new(9001)),
        un_b_of(VarId::new(9002)),
    );
    // A SECOND, separate `when` over the same merged stub whose tag-0 field is
    // decoded as Int — conflicting the shared `(Unknown_S_1, 0, 0)` key.
    let conflicting = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("other", VarId::new(9201))),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: Some(hint.clone()),
                tag: 0,
                shape: ConstructorShape::unknown_data(0, 1),
                fields: vec![Binder::new("field_0", VarId::new(9202))],
            },
            guard: None,
            body: un_i_of(VarId::new(9202)),
        }],
    };
    let expr = PseudoExpr::Tuple((vec![cred, conflicting]).into());
    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &RenderCtx::at(None));
    let PseudoExpr::Tuple(items) = out else {
        panic!()
    };
    let PseudoExpr::When { clauses, .. } = &items[0] else {
        panic!()
    };
    assert_eq!(
        clause_type_hint(&clauses[0]),
        Some(&hint),
        "cross-site Conflict ⇒ even the ByteArray credential `when` stays the honest stub"
    );
}

/// GATE GUARDS THE SUBJECT: even with both arms ByteArray, a NON-credential
/// (plain user) subject does not type to `SumTypeId::Credential` → untouched.
#[test]
fn leaves_credential_arms_when_subject_not_credential() {
    let expr = credential_when(
        "my_thing",
        VarId::new(9300),
        un_b_of(VarId::new(9001)),
        un_b_of(VarId::new(9002)),
    );
    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &RenderCtx::at(None));
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    assert_eq!(
        clause_type_hint(&clauses[0]),
        Some(&TypeHintId::new(CREDENTIAL_STUB)),
        "non-credential subject ⇒ stub kept"
    );
    assert_eq!(clause_field_names(&clauses[0]), vec!["field_0".to_string()]);
}

/// SUBJECT PROVENANCE: a `payment_credential`-named binder also types to
/// `SumTypeId::Credential` (via its static field type), so a both-ByteArray
/// `when payment_credential is { … }` is named too.
#[test]
fn names_credential_arms_over_payment_credential_subject() {
    let expr = credential_when(
        "payment_credential",
        VarId::new(9400),
        un_b_of(VarId::new(9001)),
        un_b_of(VarId::new(9002)),
    );
    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &RenderCtx::at(None));
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    assert_eq!(
        clause_type_hint(&clauses[0]),
        Some(&TypeHintId::new("credential")),
        "payment_credential subject types to Credential ⇒ named"
    );
    assert_eq!(clause_field_names(&clauses[0]), vec!["hash".to_string()]);
}

/// End-to-end: `when output.datum is { NoDatum; DatumHash(h); InlineDatum(d) }`
/// names the OutputDatum arms under V2/V3 (the `datum` field-access selector
/// types the subject to `Sum(OutputDatum)`).
#[test]
fn names_output_datum_arms_v2_v3() {
    use crate::decompile::ScriptVersion;
    for v in [ScriptVersion::PlutusV2, ScriptVersion::PlutusV3] {
        let ctx = RenderCtx::at(Some(v));
        let h = VarId::new(9501);
        let d = VarId::new(9502);
        let expr = when_on_field(
            "output",
            VarId::new(9500),
            "datum",
            vec![
                ctor_clause(0, &[], PseudoExpr::var_with_id("x", VarId::new(9510))),
                ctor_clause(1, &[("field_0", h)], PseudoExpr::var_with_id("field_0", h)),
                ctor_clause(2, &[("field_0", d)], PseudoExpr::var_with_id("field_0", d)),
            ],
        );
        let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &ctx);
        let PseudoExpr::When { clauses, .. } = out else {
            panic!()
        };
        let od = TypeHintId::new("output_datum");
        assert_eq!(
            clause_type_hint(&clauses[0]),
            Some(&od),
            "{v:?}: NoDatum hinted"
        );
        assert_eq!(
            clause_type_hint(&clauses[1]),
            Some(&od),
            "{v:?}: DatumHash hinted"
        );
        assert_eq!(
            clause_type_hint(&clauses[2]),
            Some(&od),
            "{v:?}: InlineDatum hinted"
        );
        assert_eq!(clause_field_names(&clauses[1]), vec!["hash".to_string()]);
    }
}

/// Version gate: OutputDatum is NOT named at V1 (V1 has no OutputDatum sum;
/// the datum field there is `datum_hash : Option<ByteArray>`).
#[test]
fn output_datum_not_named_at_v1() {
    use crate::decompile::ScriptVersion;
    let ctx = RenderCtx::at(Some(ScriptVersion::PlutusV1));
    let expr = when_on_field(
        "output",
        VarId::new(9600),
        "datum",
        vec![
            ctor_clause(0, &[], PseudoExpr::var_with_id("x", VarId::new(9610))),
            ctor_clause(
                1,
                &[("field_0", VarId::new(9611))],
                PseudoExpr::var_with_id("y", VarId::new(9612)),
            ),
        ],
    );
    let out = name_cardano_sum_arms(expr, &CardanoTypeEnv::default(), &ctx);
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    assert_eq!(
        clause_type_hint(&clauses[0]),
        None,
        "V1 ⇒ OutputDatum not named"
    );
}

/// End-to-end: a Voter-typed subject (via the env) names the V3 Voter
/// arms (ConstitutionalCommitteeMember / DelegateRepresentative / StakePool).
#[test]
fn names_voter_arms_v3_via_env() {
    use crate::decompile::ScriptVersion;
    use crate::decompile::simplify::postprocess::{CardanoTypeRef, SumTypeId as S};
    let ctx = RenderCtx::at(Some(ScriptVersion::PlutusV3));
    // A bare `voter` binder typed Sum(Voter) via the env (as the ScriptInfo
    // Voting payload would be).
    let vid = VarId::new(9700);
    let mut env = CardanoTypeEnv::default();
    env.debug_insert(vid, CardanoTypeRef::Sum(S::Voter));
    let expr = when_on(
        "voter",
        vid,
        vec![
            ctor_clause(
                0,
                &[("field_0", VarId::new(9701))],
                PseudoExpr::var_with_id("x", VarId::new(9710)),
            ),
            ctor_clause(
                1,
                &[("field_0", VarId::new(9702))],
                PseudoExpr::var_with_id("y", VarId::new(9711)),
            ),
            ctor_clause(
                2,
                &[("field_0", VarId::new(9703))],
                PseudoExpr::var_with_id("z", VarId::new(9712)),
            ),
        ],
    );
    let out = name_cardano_sum_arms(expr, &env, &ctx);
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    let voter = TypeHintId::new("voter");
    assert_eq!(
        clause_type_hint(&clauses[0]),
        Some(&voter),
        "CC member hinted"
    );
    assert_eq!(
        clause_type_hint(&clauses[2]),
        Some(&voter),
        "StakePool hinted"
    );
    assert_eq!(
        clause_field_names(&clauses[0]),
        vec!["credential".to_string()]
    );
    assert_eq!(clause_field_names(&clauses[2]), vec!["pool_id".to_string()]);
}
