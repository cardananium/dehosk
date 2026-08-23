use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

#[test]
fn resolve_expect_constr_unpack_preserves_subject_and_field_ids() {
    let subject_id = VarId::fresh_binding();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::expect_helper()),
        args: vec![
            PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::builtin(
                        "Constr.unpack",
                        vec![PseudoExpr::var_with_id("x", subject_id)],
                    ),
                    "fst".to_string(),
                )),
                right: PBox::new(PseudoExpr::int(0)),
            },
            PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id("x", subject_id),
                    "fields".to_string(),
                )),
                index: 0,
            },
        ]
        .into(),
    };

    let resolved = resolve_expect_constr_unpack(expr, None);

    let PseudoExpr::When {
        subject,
        subject_name,
        clauses,
    } = resolved
    else {
        panic!("expected expect-constr rewrite to produce when");
    };
    assert!(
        matches!(subject.as_ref(), PseudoExpr::Var { name, id, .. } if name == "x" && *id == Some(subject_id))
    );
    let Some(subject_name) = subject_name else {
        panic!("expected subject_name binder");
    };
    assert_eq!(subject_name.as_str(), "x");
    assert_eq!(subject_name.id, subject_id);

    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor clause");
    };
    assert_eq!(fields.len(), 1);
    let field_id = fields[0].id;
    assert!(
        matches!(&clauses[0].body, PseudoExpr::Var { name, id, .. } if name == "field_0" && *id == Some(field_id))
    );
}

/// `resolve_expect_constr_unpack` names unpack fields from the Cardano
/// schema when the subject is a recognized `ContextType` and a
/// `ScriptVersion` is supplied — here the 3-field V3 ScriptContext.
#[test]
fn resolve_expect_constr_unpack_uses_cardano_field_names_for_script_context() {
    use crate::decompile::ScriptVersion;

    let subject_id = VarId::fresh_binding();
    // Build: expect!(Constr.unpack(script_context).fst == 0,
    //                script_context.fields[2])
    // The body field-access at index 2 forces a 3-field arity.
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::expect_helper()),
        args: vec![
            PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::builtin(
                        "Constr.unpack",
                        vec![PseudoExpr::var_with_id("script_context", subject_id)],
                    ),
                    "fst".to_string(),
                )),
                right: PBox::new(PseudoExpr::int(0)),
            },
            PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id("script_context", subject_id),
                    "fields".to_string(),
                )),
                index: 2,
            },
        ]
        .into(),
    };

    let resolved = resolve_expect_constr_unpack(expr, Some(ScriptVersion::PlutusV3));

    let PseudoExpr::When { clauses, .. } = resolved else {
        panic!("expected expect-constr rewrite to produce when");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor clause");
    };
    let names: Vec<&str> = fields.iter().map(|f| f.as_str()).collect();
    assert_eq!(
        names,
        vec!["tx_info", "redeemer", "script_info"],
        "V3 ScriptContext fields should be named via the schema"
    );
}

/// The fallback path (no script_version OR subject is
/// not a known ContextType) still yields `field_N` binders — no
/// regression on user-defined ADT destructures.
#[test]
fn resolve_expect_constr_unpack_falls_back_to_field_n_for_user_adt() {
    use crate::decompile::ScriptVersion;

    let subject_id = VarId::fresh_binding();
    // Subject `my_adt` is not a known ContextType — even with a
    // version, the binder must remain `field_N`.
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::expect_helper()),
        args: vec![
            PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::builtin(
                        "Constr.unpack",
                        vec![PseudoExpr::var_with_id("my_adt", subject_id)],
                    ),
                    "fst".to_string(),
                )),
                right: PBox::new(PseudoExpr::int(0)),
            },
            PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id("my_adt", subject_id),
                    "fields".to_string(),
                )),
                index: 1,
            },
        ]
        .into(),
    };

    let resolved = resolve_expect_constr_unpack(expr, Some(ScriptVersion::PlutusV3));

    let PseudoExpr::When { clauses, .. } = resolved else {
        panic!("expected expect-constr rewrite to produce when");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor clause");
    };
    let names: Vec<&str> = fields.iter().map(|f| f.as_str()).collect();
    assert_eq!(
        names,
        vec!["field_0", "field_1"],
        "unknown subject types must keep `field_N` naming"
    );
}

#[test]
fn resolve_immediate_applications_preserves_lambda_param_ids() {
    let x_id = VarId::fresh_binding();
    let y_id = VarId::fresh_binding();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id), Binder::new("y", y_id)],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::var_with_id("x", x_id)),
                right: PBox::new(PseudoExpr::var_with_id("y", y_id)),
            }),
        }),
        args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
    };

    let resolved = resolve_immediate_applications(expr);

    let PseudoExpr::Let { name, id, body, .. } = resolved else {
        panic!("expected outer let");
    };
    assert_eq!(name, "x");
    assert_eq!(id, Some(x_id));

    let PseudoExpr::Let { name, id, body, .. } = body.into_inner() else {
        panic!("expected inner let");
    };
    assert_eq!(name, "y");
    assert_eq!(id, Some(y_id));
    assert!(matches!(
        body.into_inner(),
        PseudoExpr::BinOp { left, right, .. }
            if matches!(left.as_ref(), PseudoExpr::Var { name, id, .. } if name == "x" && *id == Some(x_id))
                && matches!(right.as_ref(), PseudoExpr::Var { name, id, .. } if name == "y" && *id == Some(y_id))
    ));
}

#[test]
fn resolve_immediate_applications_raw_rewrite_can_require_ref_retargeting() {
    let outer_x_id = VarId::fresh_binding();
    let lambda_x_id = VarId::fresh_binding();
    let y_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_x_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Lambda {
                params: vec![Binder::new("x", lambda_x_id), Binder::new("y", y_id)],
                body: PBox::new(PseudoExpr::var_with_id("y", y_id)),
            }),
            args: vec![PseudoExpr::int(1), PseudoExpr::var_with_id("x", outer_x_id)].into(),
        }),
    };

    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr));
    let resolved = resolve_immediate_applications(expr);

    assert!(
        crate::decompile::ref_retarget::refs_need_retarget_by_scope(&resolved),
        "raw immediate-application rewrite must not be treated as a ref-id producer"
    );
}

#[test]
fn eliminate_var_aliases_retargets_pair_refs_to_alias_id() {
    let y_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(y_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(x_id),
            value: PBox::new(PseudoExpr::var_with_id("y", y_id)),
            body: PBox::new(PseudoExpr::Pair(
                PBox::new(PseudoExpr::var_with_id("x", x_id)),
                PBox::new(PseudoExpr::var_with_id("x", x_id)),
            )),
        }),
    };

    let out = eliminate_var_aliases(expr);

    assert!(
        matches!(
            &out,
            PseudoExpr::Let { name, id, body, .. }
                if name == "y"
                    && *id == Some(y_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Pair(left, right)
                            if matches!(
                                left.as_ref(),
                                PseudoExpr::Var { name, id } if name == "y" && *id == Some(y_id)
                            )
                            && matches!(
                                right.as_ref(),
                                PseudoExpr::Var { name, id } if name == "y" && *id == Some(y_id)
                            )
                    )
        ),
        "alias elimination must retarget refs inside Pair to the aliased binder id, got: {out:?}"
    );
}

#[test]
fn eliminate_var_aliases_rewrites_when_guard_and_body_refs() {
    let y_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(y_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(x_id),
            value: PBox::new(PseudoExpr::var_with_id("y", y_id)),
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("subject")),
                subject_name: None,
                clauses: vec![WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: Some(PseudoExpr::var_with_id("x", x_id)),
                    body: PseudoExpr::var_with_id("x", x_id),
                }],
            }),
        }),
    };

    let out = eliminate_var_aliases(expr);

    assert!(
        matches!(
            &out,
            PseudoExpr::Let { body, .. }
                if matches!(
                    body.as_ref(),
                    PseudoExpr::When { clauses, .. }
                        if matches!(
                            clauses.as_slice(),
                            [WhenClause { guard: Some(guard), body, .. }]
                                if matches!(guard, PseudoExpr::Var { name, id } if name == "y" && *id == Some(y_id))
                                    && matches!(body, PseudoExpr::Var { name, id } if name == "y" && *id == Some(y_id))
                        )
                )
        ),
        "alias elimination must rewrite both when guards and bodies when the alias binder is in scope, got: {out:?}"
    );
}

#[test]
fn eliminate_var_aliases_respects_when_pattern_shadowing() {
    let y_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let pattern_x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(y_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(x_id),
            value: PBox::new(PseudoExpr::var_with_id("y", y_id)),
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("subject")),
                subject_name: None,
                clauses: vec![WhenClause {
                    pattern: WhenPattern::Var(Binder::new("x", pattern_x_id)),
                    guard: Some(PseudoExpr::var_with_id("x", pattern_x_id)),
                    body: PseudoExpr::var_with_id("x", pattern_x_id),
                }],
            }),
        }),
    };

    let out = eliminate_var_aliases(expr);

    assert!(
        matches!(
            &out,
            PseudoExpr::Let { body, .. }
                if matches!(
                    body.as_ref(),
                    PseudoExpr::When { clauses, .. }
                        if matches!(
                            clauses.as_slice(),
                            [WhenClause { guard: Some(guard), body, .. }]
                                if matches!(guard, PseudoExpr::Var { name, id } if name == "x" && *id == Some(pattern_x_id))
                                    && matches!(body, PseudoExpr::Var { name, id } if name == "x" && *id == Some(pattern_x_id))
                        )
                )
        ),
        "alias elimination must not rewrite refs shadowed by a when pattern binder, got: {out:?}"
    );
}

#[test]
fn eliminate_var_aliases_respects_when_subject_name_shadowing() {
    let y_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let subject_x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(y_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(x_id),
            value: PBox::new(PseudoExpr::var_with_id("y", y_id)),
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("subject")),
                subject_name: Some(Binder::new("x", subject_x_id)),
                clauses: vec![WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: Some(PseudoExpr::var_with_id("x", subject_x_id)),
                    body: PseudoExpr::var_with_id("x", subject_x_id),
                }],
            }),
        }),
    };

    let out = eliminate_var_aliases(expr);

    assert!(
        matches!(
            &out,
            PseudoExpr::Let { body, .. }
                if matches!(
                    body.as_ref(),
                    PseudoExpr::When { clauses, .. }
                        if matches!(
                            clauses.as_slice(),
                            [WhenClause { guard: Some(guard), body, .. }]
                                if matches!(guard, PseudoExpr::Var { name, id } if name == "x" && *id == Some(subject_x_id))
                                    && matches!(body, PseudoExpr::Var { name, id } if name == "x" && *id == Some(subject_x_id))
                        )
                )
        ),
        "alias elimination must not rewrite refs shadowed by a when subject-name binder, got: {out:?}"
    );
}

#[test]
fn eliminate_var_aliases_drops_fix_residue_with_same_name_foreign_ref() {
    let outer_id = VarId::new(9451);
    let residue_id = VarId::new(9452);
    let expr = PseudoExpr::Let {
        name: "loop".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Let {
            name: "loop".to_string(),
            id: Some(residue_id),
            value: PBox::new(PseudoExpr::fix_helper()),
            body: PBox::new(PseudoExpr::var_with_id("loop", outer_id)),
        }),
    };

    let out = eliminate_var_aliases(expr);

    assert!(
        matches!(
            &out,
            PseudoExpr::Let { name, id, body, .. }
                if name == "loop"
                    && *id == Some(outer_id)
                    && matches!(body.as_ref(), PseudoExpr::Var { name, id, .. }
                        if name == "loop" && *id == Some(outer_id))
        ),
        "fix-residue let should ignore same-name refs owned by a different authoritative id, got: {out:?}"
    );
}

/// Find every `Let` with a synthetic-alias name whose `body` holds a
/// `Var` of the same name but a different `VarId` — the orphan shape
/// the `synthetic_alias` textual fallback in
/// `eliminate_dead_lets_pseudo` masks as live.
pub(crate) fn collect_synthetic_alias_orphan_lets(
    expr: &PseudoExpr,
) -> Vec<(String, Option<VarId>, Option<VarId>)> {
    fn go(expr: &PseudoExpr, out: &mut Vec<(String, Option<VarId>, Option<VarId>)>) {
        match expr {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                go(value, out);
                let synthetic_alias = name.starts_with("field_")
                    || name.starts_with("fields_")
                    || name.starts_with("item_")
                    || name.starts_with("data_literal_");
                if synthetic_alias {
                    let mut hits: Vec<Option<VarId>> = Vec::new();
                    collect_same_name_diff_id_refs(body, name, *id, &mut hits);
                    for hit in hits {
                        out.push((name.clone(), *id, hit));
                    }
                }
                go(body, out);
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => go(body, out),
            PseudoExpr::Apply { function, args } => {
                go(function, out);
                for arg in args {
                    go(arg, out);
                }
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                go(condition, out);
                go(then_branch, out);
                go(else_branch, out);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                go(subject, out);
                for clause in clauses {
                    if let Some(guard) = &clause.guard {
                        go(guard, out);
                    }
                    go(&clause.body, out);
                }
            }
            PseudoExpr::BinOp { left, right, .. } | PseudoExpr::Pair(left, right) => {
                go(left, out);
                go(right, out);
            }
            PseudoExpr::UnOp { operand, .. }
            | PseudoExpr::Delay(operand)
            | PseudoExpr::Force(operand) => go(operand, out),
            PseudoExpr::Trace { message, value } => {
                go(message, out);
                go(value, out);
            }
            PseudoExpr::List { elements, tail } => {
                for el in elements {
                    go(el, out);
                }
                if let Some(tail) = tail {
                    go(tail, out);
                }
            }
            PseudoExpr::Tuple(items) => {
                for it in items {
                    go(it, out);
                }
            }
            PseudoExpr::FieldAccess { record, .. } => go(record, out),
            PseudoExpr::IndexAccess { collection, .. } => go(collection, out),
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args {
                    go(arg, out);
                }
            }
            PseudoExpr::Constr { fields, .. } => {
                for field in fields {
                    go(field, out);
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    go(expr, &mut out);
    out
}

fn collect_same_name_diff_id_refs(
    expr: &PseudoExpr,
    target_name: &str,
    target_id: Option<VarId>,
    hits: &mut Vec<Option<VarId>>,
) {
    match expr {
        PseudoExpr::Var { name, id } => {
            if name == target_name && *id != target_id {
                hits.push(*id);
            }
        }
        PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
            collect_same_name_diff_id_refs(body, target_name, target_id, hits)
        }
        PseudoExpr::Let { value, body, .. } => {
            collect_same_name_diff_id_refs(value, target_name, target_id, hits);
            collect_same_name_diff_id_refs(body, target_name, target_id, hits);
        }
        PseudoExpr::Apply { function, args } => {
            collect_same_name_diff_id_refs(function, target_name, target_id, hits);
            for arg in args {
                collect_same_name_diff_id_refs(arg, target_name, target_id, hits);
            }
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_same_name_diff_id_refs(condition, target_name, target_id, hits);
            collect_same_name_diff_id_refs(then_branch, target_name, target_id, hits);
            collect_same_name_diff_id_refs(else_branch, target_name, target_id, hits);
        }
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            collect_same_name_diff_id_refs(subject, target_name, target_id, hits);
            for clause in clauses {
                if let Some(guard) = &clause.guard {
                    collect_same_name_diff_id_refs(guard, target_name, target_id, hits);
                }
                collect_same_name_diff_id_refs(&clause.body, target_name, target_id, hits);
            }
        }
        PseudoExpr::BinOp { left, right, .. } | PseudoExpr::Pair(left, right) => {
            collect_same_name_diff_id_refs(left, target_name, target_id, hits);
            collect_same_name_diff_id_refs(right, target_name, target_id, hits);
        }
        PseudoExpr::UnOp { operand, .. }
        | PseudoExpr::Delay(operand)
        | PseudoExpr::Force(operand) => {
            collect_same_name_diff_id_refs(operand, target_name, target_id, hits)
        }
        PseudoExpr::Trace { message, value } => {
            collect_same_name_diff_id_refs(message, target_name, target_id, hits);
            collect_same_name_diff_id_refs(value, target_name, target_id, hits);
        }
        PseudoExpr::List { elements, tail } => {
            for el in elements {
                collect_same_name_diff_id_refs(el, target_name, target_id, hits);
            }
            if let Some(tail) = tail {
                collect_same_name_diff_id_refs(tail, target_name, target_id, hits);
            }
        }
        PseudoExpr::Tuple(items) => {
            for it in items {
                collect_same_name_diff_id_refs(it, target_name, target_id, hits);
            }
        }
        PseudoExpr::FieldAccess { record, .. } => {
            collect_same_name_diff_id_refs(record, target_name, target_id, hits)
        }
        PseudoExpr::IndexAccess { collection, .. } => {
            collect_same_name_diff_id_refs(collection, target_name, target_id, hits)
        }
        PseudoExpr::BuiltinCall { args, .. } => {
            for arg in args {
                collect_same_name_diff_id_refs(arg, target_name, target_id, hits);
            }
        }
        PseudoExpr::Constr { fields, .. } => {
            for field in fields {
                collect_same_name_diff_id_refs(field, target_name, target_id, hits);
            }
        }
        _ => {}
    }
}

/// The post-pipeline AST contains zero synthetic-alias let bindings
/// whose body holds a same-name/different-VarId reference. If this
/// fires, the fix is upstream — mint-site VarKind annotation or
/// producer hygiene — not a textual fallback in DCE.
#[test]
fn audit_helper_detects_synthetic_alias_orphan() {
    // The audit walker must flag the archetype it targets: a `field_0`
    // let bound to one VarId whose body references a Var with the same
    // name and a different VarId.
    let binding_id = VarId::fresh_binding();
    let stale_ref_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "field_0".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Var {
            name: "field_0".to_string(),
            id: Some(stale_ref_id),
        }),
    };
    let orphans = collect_synthetic_alias_orphan_lets(&expr);
    assert_eq!(
        orphans.len(),
        1,
        "audit should flag the synthetic-alias orphan, got: {:?}",
        orphans
    );
    let (name, target_id, hit_id) = &orphans[0];
    assert_eq!(name, "field_0");
    assert_eq!(*target_id, Some(binding_id));
    assert_eq!(*hit_id, Some(stale_ref_id));
}

#[test]
fn audit_helper_ignores_clean_synthetic_alias_let() {
    // Same `field_0` synthetic-alias prefix, but with the body using
    // the SAME VarId — clean / no orphan.
    let binding_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "field_0".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Var {
            name: "field_0".to_string(),
            id: Some(binding_id),
        }),
    };
    let orphans = collect_synthetic_alias_orphan_lets(&expr);
    assert!(
        orphans.is_empty(),
        "audit should not flag the matching-id synthetic alias, got: {:?}",
        orphans
    );
}
