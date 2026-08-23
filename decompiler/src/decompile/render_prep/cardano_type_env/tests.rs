use super::*;
use crate::decompile::render_prep::RenderCtx;
use crate::decompile::simplify::postprocess::SumTypeId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::WhenClause;
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}
fn field(record: PseudoExpr, name: &str) -> PseudoExpr {
    PseudoExpr::FieldAccess {
        record: PBox::new(record),
        selector: FieldSelector::NamedField(name.to_string()),
    }
}
fn index(coll: PseudoExpr, i: usize) -> PseudoExpr {
    PseudoExpr::IndexAccess {
        collection: PBox::new(coll),
        index: i,
    }
}
fn ctor_clause(tag: usize, fields: Vec<Binder>, body: PseudoExpr) -> WhenClause {
    let arity = fields.len();
    WhenClause {
        pattern: WhenPattern::Constructor {
            type_hint: None,
            tag,
            fields,
            shape: ConstructorShape::unknown_data(tag, arity),
        },
        guard: None,
        body,
    }
}
fn fail_clause() -> WhenClause {
    WhenClause {
        pattern: WhenPattern::Wildcard,
        guard: None,
        body: PseudoExpr::Error { message: None },
    }
}
fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name, VarId::new(id))
}

/// Run the env builder at an explicit render version.
fn build_at(version: ScriptVersion, expr: &PseudoExpr) -> CardanoTypeEnv {
    build_cardano_type_env(expr, &RenderCtx::at(Some(version)))
}

/// The validator entry's `script_context` param seeds `Record(ScriptContext)`.
#[test]
fn seeds_script_context_param() {
    let expr = PseudoExpr::Lambda {
        params: vec![binder("script_context", 1)],
        body: PBox::new(PseudoExpr::Error { message: None }),
    };
    let env = build_at(ScriptVersion::PlutusV3, &expr);
    assert_eq!(
        env.get(VarId::new(1)),
        Some(CardanoTypeRef::Record(ContextType::ScriptContext)),
    );
}

/// End-to-end: the env types
///   `let w = (when script_context.script_info is {
///       Proposing(_index, proposal_procedure) -> proposal_procedure;
///       _ -> fail }).fields[2]`
/// as `GovernanceAction` — via Sum-aware payload binding
/// (`proposal_procedure : ProposalProcedure`), the When-value join, and the
/// `.fields[2] → governance_action` projection.
#[test]
fn types_w_as_governance_action_through_proposal_procedure() {
    // when script_context.script_info is {
    //   Constr<5>(_index@10, proposal_procedure@11) -> proposal_procedure
    //   _ -> fail
    // }
    let outer_when = PseudoExpr::When {
        subject: PBox::new(field(var("script_context", 1), "script_info")),
        subject_name: None,
        clauses: vec![
            ctor_clause(
                5,
                vec![binder("_index", 10), binder("proposal_procedure", 11)],
                var("proposal_procedure", 11),
            ),
            fail_clause(),
        ],
    };
    // let w@20 = <outer_when>.fields[2] in w
    let body = PseudoExpr::Let {
        name: "w".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(index(field(outer_when, "fields"), 2)),
        body: PBox::new(var("w", 20)),
    };
    let expr = PseudoExpr::Lambda {
        params: vec![binder("script_context", 1)],
        body: PBox::new(body),
    };

    let env = build_at(ScriptVersion::PlutusV3, &expr);
    assert_eq!(
        env.get(VarId::new(11)),
        Some(CardanoTypeRef::Record(ContextType::ProposalProcedure)),
        "proposal_procedure payload binder types as ProposalProcedure",
    );
    assert_eq!(
        env.get(VarId::new(20)),
        Some(CardanoTypeRef::Sum(SumTypeId::GovernanceAction)),
        "w = proposal_procedure.fields[2] types as GovernanceAction",
    );
}

/// Fail-closed: under V2 the V3-only ScriptInfo/ProposalProcedure chain does
/// not resolve, so `w` stays untyped.
#[test]
fn inert_under_wrong_version() {
    let outer_when = PseudoExpr::When {
        subject: PBox::new(field(var("script_context", 1), "script_info")),
        subject_name: None,
        clauses: vec![
            ctor_clause(
                5,
                vec![binder("_index", 10), binder("proposal_procedure", 11)],
                var("proposal_procedure", 11),
            ),
            fail_clause(),
        ],
    };
    let body = PseudoExpr::Let {
        name: "w".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(index(field(outer_when, "fields"), 2)),
        body: PBox::new(var("w", 20)),
    };
    let expr = PseudoExpr::Lambda {
        params: vec![binder("script_context", 1)],
        body: PBox::new(body),
    };
    let env = build_at(ScriptVersion::PlutusV2, &expr);
    assert_eq!(
        env.get(VarId::new(20)),
        None,
        "V3-only chain inert under V2"
    );
}

/// Fail-closed: a `when`-value whose constructor arms produce DIFFERENT
/// Cardano types does not join — the binding stays untyped.
#[test]
fn when_value_disagreeing_arms_is_none() {
    // when script_context.script_info is {
    //   Spending(out_ref@10, datum@11) -> out_ref      // TxOutRef
    //   Certifying(index@12, certificate@13) -> index   // (untyped scalar)
    //   _ -> fail
    // }
    // The untyped `index` arm makes the join None — any None arm bails.
    let outer_when = PseudoExpr::When {
        subject: PBox::new(field(var("script_context", 1), "script_info")),
        subject_name: None,
        clauses: vec![
            ctor_clause(
                1,
                vec![binder("out_ref", 10), binder("datum", 11)],
                var("out_ref", 10),
            ),
            ctor_clause(
                3,
                vec![binder("index", 12), binder("certificate", 13)],
                var("index", 12),
            ),
            fail_clause(),
        ],
    };
    let body = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(outer_when),
        body: PBox::new(var("x", 20)),
    };
    let expr = PseudoExpr::Lambda {
        params: vec![binder("script_context", 1)],
        body: PBox::new(body),
    };
    let env = build_at(ScriptVersion::PlutusV3, &expr);
    assert_eq!(
        env.get(VarId::new(20)),
        None,
        "disagreeing when-value arms must not join",
    );
}

/// `resolve_cardano_field_indices`: a positional `.fields[N]` on an env-typed
/// record is rewritten to the schema-named field. Here
/// `script_context.tx_info.valid_range.fields[0]` (Interval.fields[0]) becomes
/// `.lower_bound`; without a render version the resolver is inert.
#[test]
fn resolve_field_indices_names_interval_and_governance_action() {
    fn lb_value(out: &PseudoExpr) -> Option<String> {
        // find `let lb = <X>` and return X's FieldAccess selector name.
        if let PseudoExpr::Lambda { body, .. } = out
            && let PseudoExpr::Let { value, .. } = body.as_ref()
            && let PseudoExpr::FieldAccess { selector, .. } = value.as_ref()
        {
            return Some(selector.as_pretty_name().to_string());
        }
        None
    }

    // fn(script_context) { let lb = script_context.tx_info.valid_range.fields[0] in lb }
    let vr = field(field(var("script_context", 1), "tx_info"), "valid_range");
    let expr = PseudoExpr::Lambda {
        params: vec![binder("script_context", 1)],
        body: PBox::new(PseudoExpr::Let {
            name: "lb".to_string(),
            id: Some(VarId::new(50)),
            value: PBox::new(index(field(vr, "fields"), 0)),
            body: PBox::new(var("lb", 50)),
        }),
    };
    let out =
        resolve_cardano_field_indices(expr.clone(), &RenderCtx::at(Some(ScriptVersion::PlutusV3)));
    assert_eq!(
        lb_value(&out).as_deref(),
        Some("lower_bound"),
        "Interval.fields[0] resolves to .lower_bound",
    );

    // Versionless (None) → no-op (the gate), so `.fields[0]` is preserved.
    let out_none = resolve_cardano_field_indices(expr, &RenderCtx::at(None));
    assert!(
        lb_value(&out_none).as_deref().is_none(),
        "at version=None the resolver is inert (lb stays an IndexAccess, not a FieldAccess)",
    );
}

/// Interproc soundness: the cons witness says the rec-fn param is a list, so
/// a `Record(ScriptContext)` call-site arg contradicts it and is rejected
/// (`element_type().is_some()` gate) — otherwise a wrong type would leak
/// into env-aware payload binding.
#[test]
fn interproc_rejects_non_list_call_arg() {
    use crate::pseudo::ast::WhenPattern;
    // let f@2 = rec fn g@3(xs@4) {
    //   when xs is { [] -> fail; [_h@5, ..tail@6] -> g(tail) }
    // } in f(script_context)
    let cons_clause = WhenClause {
        pattern: WhenPattern::List {
            elements: vec![binder("_h", 5)],
            tail: Some(binder("tail", 6)),
        },
        guard: None,
        body: PseudoExpr::Apply {
            function: PBox::new(var("g", 3)),
            args: vec![var("tail", 6)].into(),
        },
    };
    let recfn = PseudoExpr::RecFn {
        name: binder("g", 3),
        params: vec![binder("xs", 4)],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("xs", 4)),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    guard: None,
                    body: PseudoExpr::Error { message: None },
                },
                cons_clause,
            ],
        }),
    };
    let expr = PseudoExpr::Lambda {
        params: vec![binder("script_context", 1)],
        body: PBox::new(PseudoExpr::Let {
            name: "f".to_string(),
            id: Some(VarId::new(2)),
            value: PBox::new(recfn),
            // external call feeds the NON-list `script_context`.
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("f", 2)),
                args: vec![var("script_context", 1)].into(),
            }),
        }),
    };
    let env = build_at(ScriptVersion::PlutusV3, &expr);
    assert_eq!(
        env.get(VarId::new(4)),
        None,
        "cons-matched param fed Record(ScriptContext) must NOT be typed",
    );
}

/// `script_context.tx_info.outputs[0].address.stake_credential` types as
/// `Option<StakeCredential>`; the `Some(inner)` arm types `inner :
/// StakeCredential`; the inner `Inline(cred)` arm types `cred : Credential`.
#[test]
fn option_strip_types_stake_credential_then_inner_credential() {
    // chain = sc.tx_info.outputs[0].address.stake_credential
    let chain = field(
        index(
            field(field(var("script_context", 1), "tx_info"), "outputs"),
            0,
        ),
        "address",
    );
    let chain = field(chain, "stake_credential");
    // inner when over the Some-bound `inner` (StakeCredential): Inline(cred) binds cred.
    let inner_when = PseudoExpr::When {
        subject: PBox::new(var("inner", 31)),
        subject_name: None,
        clauses: vec![
            ctor_clause(0, vec![binder("cred", 40)], var("cred", 40)), // Inline(cred)
            ctor_clause(
                1,
                vec![binder("s", 41), binder("t", 42), binder("u", 43)],
                var("s", 41),
            ),
            fail_clause(),
        ],
    };
    // when scred is { Some(inner) -> <inner_when>; None -> fail }
    let outer_when = PseudoExpr::When {
        subject: PBox::new(var("scred", 30)),
        subject_name: None,
        clauses: vec![
            ctor_clause(0, vec![binder("inner", 31)], inner_when), // Some(inner)
            ctor_clause(1, vec![], PseudoExpr::Error { message: None }), // None
        ],
    };
    let body = PseudoExpr::Let {
        name: "scred".to_string(),
        id: Some(VarId::new(30)),
        value: PBox::new(chain),
        body: PBox::new(outer_when),
    };
    let expr = PseudoExpr::Lambda {
        params: vec![binder("script_context", 1)],
        body: PBox::new(body),
    };
    let env = build_at(ScriptVersion::PlutusV3, &expr);
    assert_eq!(
        env.get(VarId::new(30)),
        Some(CardanoTypeRef::OptionOfSum(SumTypeId::StakeCredential)),
        "stake_credential chain types as Option<StakeCredential>",
    );
    assert_eq!(
        env.get(VarId::new(31)),
        Some(CardanoTypeRef::Sum(SumTypeId::StakeCredential)),
        "Some(inner) binds inner : StakeCredential",
    );
    assert_eq!(
        env.get(VarId::new(40)),
        Some(CardanoTypeRef::Sum(SumTypeId::Credential)),
        "Inline(cred) binds cred : Credential",
    );
}

/// Fail-closed (exact-arity gate): a constructor arm whose field
/// count DISAGREES with the ABI arity (a coincidental tag) must NOT bind any
/// payload type — otherwise an arity-wrong `Constr<5>(a, b, c)` would still
/// mis-type `b : ProposalProcedure` and leak a wrong `w : GovernanceAction`.
#[test]
fn arity_mismatch_binds_no_payload() {
    // Proposing is arity 2, but this arm has 3 fields → not really Proposing.
    let outer_when = PseudoExpr::When {
        subject: PBox::new(field(var("script_context", 1), "script_info")),
        subject_name: None,
        clauses: vec![
            ctor_clause(
                5,
                vec![binder("a", 10), binder("b", 11), binder("c", 12)],
                var("b", 11),
            ),
            fail_clause(),
        ],
    };
    let body = PseudoExpr::Let {
        name: "w".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(index(field(outer_when, "fields"), 2)),
        body: PBox::new(var("w", 20)),
    };
    let expr = PseudoExpr::Lambda {
        params: vec![binder("script_context", 1)],
        body: PBox::new(body),
    };
    let env = build_at(ScriptVersion::PlutusV3, &expr);
    assert_eq!(
        env.get(VarId::new(11)),
        None,
        "arity-3 arm must not type its 2nd binder as ProposalProcedure",
    );
    assert_eq!(env.get(VarId::new(20)), None, "w must stay untyped");
}

/// Fail-closed (entry-only seed): a `script_context` param on a nested
/// lambda must NOT be seeded, so `script_context.script_info` there
/// does not resolve.
#[test]
fn nested_lambda_script_context_param_not_seeded() {
    // fn(outer) { fn(script_context) { let x = script_context.script_info in x } }
    let inner = PseudoExpr::Lambda {
        params: vec![binder("script_context", 2)],
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(VarId::new(20)),
            value: PBox::new(field(var("script_context", 2), "script_info")),
            body: PBox::new(var("x", 20)),
        }),
    };
    let expr = PseudoExpr::Lambda {
        params: vec![binder("outer", 1)],
        body: PBox::new(inner),
    };
    let env = build_at(ScriptVersion::PlutusV3, &expr);
    assert_eq!(
        env.get(VarId::new(2)),
        None,
        "nested-lambda script_context param must NOT be seeded",
    );
    assert_eq!(env.get(VarId::new(20)), None, "so x stays untyped");
}

/// `script_context.script_info` types as the ScriptInfo sum (FieldAccess on a
/// Record parent, field membership verified).
#[test]
fn field_access_on_record_resolves_sum() {
    // let si@20 = script_context.script_info in si
    let expr = PseudoExpr::Lambda {
        params: vec![binder("script_context", 1)],
        body: PBox::new(PseudoExpr::Let {
            name: "si".to_string(),
            id: Some(VarId::new(20)),
            value: PBox::new(field(var("script_context", 1), "script_info")),
            body: PBox::new(var("si", 20)),
        }),
    };
    let env = build_at(ScriptVersion::PlutusV3, &expr);
    assert_eq!(
        env.get(VarId::new(20)),
        Some(CardanoTypeRef::Sum(SumTypeId::ScriptInfo)),
    );
}

/// Fail-closed: a coincidentally-named selector on the WRONG record does not
/// resolve — `tx_info.script_info` is rejected (script_info ∉ TxInfo).
#[test]
fn field_access_rejects_foreign_selector() {
    // let r@30 = script_context.tx_info in ...  (Record(TxInfo))
    // let bad@31 = r.script_info in bad         (script_info ∉ TxInfo)
    let inner = PseudoExpr::Let {
        name: "bad".to_string(),
        id: Some(VarId::new(31)),
        value: PBox::new(field(var("r", 30), "script_info")),
        body: PBox::new(var("bad", 31)),
    };
    let expr = PseudoExpr::Lambda {
        params: vec![binder("script_context", 1)],
        body: PBox::new(PseudoExpr::Let {
            name: "r".to_string(),
            id: Some(VarId::new(30)),
            value: PBox::new(field(var("script_context", 1), "tx_info")),
            body: PBox::new(inner),
        }),
    };
    let env = build_at(ScriptVersion::PlutusV3, &expr);
    assert_eq!(
        env.get(VarId::new(30)),
        Some(CardanoTypeRef::Record(ContextType::TxInfo)),
        "tx_info resolves to TxInfo",
    );
    assert_eq!(
        env.get(VarId::new(31)),
        None,
        "script_info is not a TxInfo field → rejected",
    );
}

/// An inlined `list.head` leaves `when xs is { [] -> None; [x, ..] -> Some(x) }`
/// behind, and its caller unwraps it with `expect Some(p) = …`. The element type
/// has to survive both hops: the cons arm types `x`, `Some(x)` lifts that to
/// `Option<TxOut>`, and the Option arm rule unwraps it back onto `p`.
#[test]
fn option_round_trip_carries_the_list_element_type() {
    let outputs = field(field(var("script_context", 1), "tx_info"), "outputs");
    // when xs@2 is { [] -> None; [output@3, ..tail@4] -> Some(output@3) }
    let head_opt = PseudoExpr::When {
        subject: PBox::new(var("xs", 2)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                guard: None,
                body: PseudoExpr::constr_known(KnownConstructor::None, vec![]),
            },
            WhenClause {
                pattern: WhenPattern::List {
                    elements: vec![binder("output", 3)],
                    tail: Some(binder("tail", 4)),
                },
                guard: None,
                body: PseudoExpr::constr_known(KnownConstructor::Some, vec![var("output", 3)]),
            },
        ],
    };
    // when opt@5 is { Some(payload@6) -> payload@6; _ -> fail }
    let unwrap = PseudoExpr::When {
        subject: PBox::new(var("opt", 5)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor_known(
                    KnownConstructor::Some,
                    vec![binder("payload", 6)],
                ),
                guard: None,
                body: var("payload", 6),
            },
            fail_clause(),
        ],
    };
    // let xs@2 = un_list_data(script_context.tx_info.outputs)
    // let opt@5 = <head_opt>
    // <unwrap>
    let expr = PseudoExpr::Lambda {
        params: vec![binder("script_context", 1)],
        body: PBox::new(PseudoExpr::Let {
            name: "xs".to_string(),
            id: Some(VarId::new(2)),
            value: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::DataUnList,
                args: vec![outputs].into(),
            }),
            body: PBox::new(PseudoExpr::Let {
                name: "opt".to_string(),
                id: Some(VarId::new(5)),
                value: PBox::new(head_opt),
                body: PBox::new(unwrap),
            }),
        }),
    };

    let env = build_at(ScriptVersion::PlutusV3, &expr);
    assert_eq!(
        env.get(VarId::new(3)),
        Some(CardanoTypeRef::Record(ContextType::TxOut)),
        "the cons-arm head binds to the list element type",
    );
    assert_eq!(
        env.get(VarId::new(5)),
        Some(CardanoTypeRef::OptionOfRecord(ContextType::TxOut)),
        "`Some(output)` lifts the element type to Option; the bare `None` arm \
         must not sink the join",
    );
    assert_eq!(
        env.get(VarId::new(6)),
        Some(CardanoTypeRef::Record(ContextType::TxOut)),
        "`expect Some(payload)` unwraps it back to the element type",
    );
}

/// Fail-closed: `Some(x)` over an untypeable `x` stays untyped rather than
/// inventing an Option, and the `None`-arm skip cannot conjure a type on its own.
#[test]
fn option_construction_over_unknown_inner_is_none() {
    let expr = PseudoExpr::Lambda {
        params: vec![binder("script_context", 1)],
        body: PBox::new(PseudoExpr::Let {
            name: "opt".to_string(),
            id: Some(VarId::new(5)),
            value: PBox::new(PseudoExpr::When {
                subject: PBox::new(var("unknown", 9)),
                subject_name: None,
                clauses: vec![
                    WhenClause {
                        pattern: WhenPattern::List {
                            elements: vec![],
                            tail: None,
                        },
                        guard: None,
                        body: PseudoExpr::constr_known(KnownConstructor::None, vec![]),
                    },
                    WhenClause {
                        pattern: WhenPattern::List {
                            elements: vec![binder("output", 3)],
                            tail: None,
                        },
                        guard: None,
                        body: PseudoExpr::constr_known(
                            KnownConstructor::Some,
                            vec![var("output", 3)],
                        ),
                    },
                ],
            }),
            body: PBox::new(var("opt", 5)),
        }),
    };
    let env = build_at(ScriptVersion::PlutusV3, &expr);
    assert_eq!(env.get(VarId::new(5)), None);
}

/// The rewrite pass must see the SAME env as every other consumer — including
/// the interproc param seed. `resolve_cardano_field_indices` used to build its
/// own env with a bare `walk`, so a `.fields[N]` inside a rec-fn helper stayed
/// positional even though `build_cardano_type_env` typed that very param. Both
/// go through `build_env_at` now; this pins that they cannot drift apart again.
#[test]
fn field_index_rewrite_sees_interproc_seeded_params() {
    use crate::pseudo::ast::WhenPattern;
    // let f@2 = rec fn g@3(xs@4) {
    //   when xs is { [] -> fail; [head@5, ..tail@6] -> head@5.fields[1] }
    // } in f(un_list_data(script_context.tx_info.inputs))
    let cons_clause = WhenClause {
        pattern: WhenPattern::List {
            elements: vec![binder("head", 5)],
            tail: Some(binder("tail", 6)),
        },
        guard: None,
        body: index(field(var("head", 5), "fields"), 1),
    };
    let recfn = PseudoExpr::RecFn {
        name: binder("g", 3),
        params: vec![binder("xs", 4)],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("xs", 4)),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    guard: None,
                    body: PseudoExpr::Error { message: None },
                },
                cons_clause,
            ],
        }),
    };
    let inputs = field(field(var("script_context", 1), "tx_info"), "inputs");
    let expr = PseudoExpr::Lambda {
        params: vec![binder("script_context", 1)],
        body: PBox::new(PseudoExpr::Let {
            name: "f".to_string(),
            id: Some(VarId::new(2)),
            value: PBox::new(recfn),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("f", 2)),
                args: vec![PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::DataUnList,
                    args: vec![inputs].into(),
                }]
                .into(),
            }),
        }),
    };

    // The param IS typed by the env builder …
    let env = build_at(ScriptVersion::PlutusV3, &expr);
    assert_eq!(
        env.get(VarId::new(4)),
        Some(CardanoTypeRef::ListOfRecords(ContextType::TxInInfo)),
        "the seed types the rec-fn param from its only call site",
    );
    assert_eq!(
        env.get(VarId::new(5)),
        Some(CardanoTypeRef::Record(ContextType::TxInInfo)),
        "the re-walk then types the cons-arm head",
    );

    // … and the rewrite must act on it: TxInInfo.fields[1] is `resolved`.
    let out = resolve_cardano_field_indices(expr, &RenderCtx::at(Some(ScriptVersion::PlutusV3)));
    let rendered = format!("{out:?}");
    assert!(
        rendered.contains("resolved"),
        "`head.fields[1]` inside the helper must be renamed to `head.resolved`; got {rendered}",
    );
}
