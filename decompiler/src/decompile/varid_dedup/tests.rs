use super::*;

fn collect_binding_ids(expr: &PseudoExpr) -> Vec<VarId> {
    struct Collector {
        ids: Vec<VarId>,
    }

    impl ExprVisitor for Collector {
        fn visit_let_value_post(&mut self, _name: &str, id: &Option<VarId>, _value: &PseudoExpr) {
            self.ids
                .push(id.unwrap_or_else(VarId::fresh_compat_placeholder));
        }

        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            self.ids.extend(params.iter().map(|p| p.id));
        }

        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            self.ids.push(name.id);
            self.ids.extend(params.iter().map(|p| p.id));
        }

        fn visit_when(
            &mut self,
            _subject: &PseudoExpr,
            subject_name: Option<&Binder>,
            clauses: &[WhenClause],
        ) {
            if let Some(b) = subject_name {
                self.ids.push(b.id);
            }
            for clause in clauses {
                collect_pattern_ids(&mut self.ids, &clause.pattern);
            }
        }
    }

    fn collect_pattern_ids(out: &mut Vec<VarId>, pattern: &WhenPattern) {
        match pattern {
            WhenPattern::Constructor { fields, .. } => out.extend(fields.iter().map(|b| b.id)),
            WhenPattern::List { elements, tail } => {
                out.extend(elements.iter().map(|b| b.id));
                if let Some(tail) = tail {
                    out.push(tail.id);
                }
            }
            WhenPattern::Tuple(items) => out.extend(items.iter().map(|b| b.id)),
            WhenPattern::Pair(left, right) => {
                out.push(left.id);
                out.push(right.id);
            }
            WhenPattern::Var(binder) => out.push(binder.id),
            WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
        }
    }

    let mut c = Collector { ids: Vec::new() };
    c.walk(expr);
    c.ids
}

#[test]
fn detects_duplicate_let_binder_id() {
    let dup_id = VarId::from_raw(11);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(dup_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "y".to_string(),
            id: Some(dup_id),
            value: PBox::new(PseudoExpr::int(2)),
            body: PBox::new(PseudoExpr::Unit),
        }),
    };

    assert!(has_duplicate_binding_ids(&expr));
}

#[test]
fn detects_duplicate_lambda_or_recfn_binder_id() {
    let dup_id = VarId::from_raw(12);
    let lambda_expr = PseudoExpr::Lambda {
        params: vec![Binder::new("x", dup_id), Binder::new("y", dup_id)],
        body: PBox::new(PseudoExpr::Unit),
    };
    let recfn_expr = PseudoExpr::RecFn {
        name: Binder::new("self", dup_id),
        params: vec![Binder::new("arg", dup_id)],
        body: PBox::new(PseudoExpr::Unit),
    };

    assert!(has_duplicate_binding_ids(&lambda_expr));
    assert!(has_duplicate_binding_ids(&recfn_expr));
}

#[test]
fn detects_duplicate_when_subject_or_pattern_binder_id() {
    let dup_id = VarId::from_raw(13);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("x", VarId::from_raw(14))),
        subject_name: Some(Binder::new("subject", dup_id)),
        clauses: vec![WhenClause::new(
            WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![Binder::new("field", dup_id)],
                shape: crate::pseudo::constructor::ConstructorShape::unknown_data(0, 1),
            },
            PseudoExpr::Unit,
        )],
    };

    assert!(has_duplicate_binding_ids(&expr));
}

#[test]
fn unique_binding_ids_make_deduplicate_var_ids_structural_identity() {
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(VarId::from_raw(21)),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("x", VarId::from_raw(21))),
            subject_name: Some(Binder::new("subject", VarId::from_raw(22))),
            clauses: vec![WhenClause::new(
                WhenPattern::List {
                    elements: vec![Binder::new("head", VarId::from_raw(23))],
                    tail: Some(Binder::new("tail", VarId::from_raw(24))),
                },
                PseudoExpr::Lambda {
                    params: vec![Binder::new("arg", VarId::from_raw(25))],
                    body: PBox::new(PseudoExpr::var_with_id("arg", VarId::from_raw(25))),
                },
            )],
        }),
    };

    assert!(!has_duplicate_binding_ids(&expr));
    let result = deduplicate_var_ids(expr.clone());
    assert!(result.structural_eq(&expr));
}

#[test]
fn identity_when_already_unique() {
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(VarId::from_raw(1)),
        value: PBox::new(PseudoExpr::int(42)),
        body: PBox::new(PseudoExpr::Let {
            name: "y".to_string(),
            id: Some(VarId::from_raw(2)),
            value: PBox::new(PseudoExpr::int(7)),
            body: PBox::new(PseudoExpr::Unit),
        }),
    };

    let result = deduplicate_var_ids(expr);
    let ids = collect_binding_ids(&result);
    assert_eq!(ids, vec![VarId::from_raw(1), VarId::from_raw(2)]);
}

#[test]
fn renames_duplicate_let_binder() {
    let dup_id = VarId::from_raw(5);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(dup_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(dup_id),
            value: PBox::new(PseudoExpr::int(2)),
            body: PBox::new(PseudoExpr::Unit),
        }),
    };

    let result = deduplicate_var_ids(expr);
    let ids = collect_binding_ids(&result);
    assert_eq!(ids.len(), 2);
    assert_eq!(ids[0], dup_id);
    assert_ne!(ids[1], dup_id);
}

#[test]
fn rewrites_var_reference_to_renamed_binder() {
    let dup_id = VarId::from_raw(3);
    // let x@3 = 1 in (let x@3 = 2 in x@3) — the inner binder gets a
    // fresh id and the Var ref must follow it, not the outer binder.
    let inner_var = PseudoExpr::Var {
        name: "x".to_string(),
        id: dup_id.into(),
    };
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(dup_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(dup_id),
            value: PBox::new(PseudoExpr::int(2)),
            body: PBox::new(inner_var),
        }),
    };

    let result = deduplicate_var_ids(expr);
    let binding_ids = collect_binding_ids(&result);
    let inner_binder_id = binding_ids[1];
    assert_ne!(inner_binder_id, dup_id);

    // Walk and confirm the lone Var reference now points to inner binder.
    struct VarRefCollector(Vec<Option<VarId>>);
    impl ExprVisitor for VarRefCollector {
        fn visit_var(&mut self, _name: &str, id: &Option<VarId>) {
            self.0.push(id.get());
        }
    }
    let mut refs = VarRefCollector(Vec::new());
    refs.walk(&result);
    assert_eq!(refs.0, vec![Some(inner_binder_id)]);
}

#[test]
fn preserves_compat_placeholder_let_ids() {
    let compat_id = VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(compat_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::var_with_id("x", compat_id)),
    };

    let result = deduplicate_var_ids(expr);

    match result {
        PseudoExpr::Let { id, body, .. } => {
            assert_eq!(id, Some(compat_id));
            assert!(
                matches!(body.as_ref(), PseudoExpr::Var { name, id } if name == "x" && *id == Some(compat_id))
            );
        }
        other => panic!("expected compat let to survive dedup, got {other:?}"),
    }
}
