use super::*;
use crate::pseudo::ast::PBox;

pub(super) fn y_combinator_with_ids(base: u32) -> PseudoExpr {
    let b_id = VarId::new(base);
    let c_id = VarId::new(base + 1);
    let d_id = VarId::new(base + 2);
    let e_id = VarId::new(base + 3);

    PseudoExpr::Lambda {
        params: vec![Binder::new("b", b_id)],
        body: PBox::new(PseudoExpr::Let {
            name: "c".to_string(),
            id: Some(c_id),
            value: PBox::new(PseudoExpr::Lambda {
                params: vec![Binder::new("d", d_id), Binder::new("e", e_id)],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("b", b_id)),
                    args: vec![
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var_with_id("d", d_id)),
                            args: vec![PseudoExpr::var_with_id("d", d_id)].into(),
                        },
                        PseudoExpr::var_with_id("e", e_id),
                    ]
                    .into(),
                }),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("c", c_id)),
                args: vec![PseudoExpr::var_with_id("c", c_id)].into(),
            }),
        }),
    }
}

pub(super) fn delayed_y_combinator_with_ids(base: u32) -> PseudoExpr {
    PseudoExpr::Delay(PBox::new(PseudoExpr::Delay(PBox::new(
        y_combinator_with_ids(base),
    ))))
}

pub(super) fn force_twice(expr: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Force(PBox::new(PseudoExpr::Force(PBox::new(expr))))
}

pub(super) fn assert_no_duplicate_binder_var_ids(expr: &PseudoExpr) {
    fn record_id(
        seen: &mut std::collections::HashMap<VarId, String>,
        label: impl Into<String>,
        id: VarId,
    ) {
        let Some(id) = id.get() else {
            return;
        };
        let label = label.into();
        if let Some(previous) = seen.insert(id, label.clone()) {
            panic!("duplicate binder VarId {id}: {previous} and {label}");
        }
    }

    fn record_binder(seen: &mut std::collections::HashMap<VarId, String>, binder: &Binder) {
        record_id(seen, format!("binder {}", binder.name), binder.id);
    }

    fn visit_pattern(pattern: &WhenPattern, seen: &mut std::collections::HashMap<VarId, String>) {
        match pattern {
            WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                for field in fields {
                    record_binder(seen, field);
                }
            }
            WhenPattern::List { elements, tail } => {
                for element in elements {
                    record_binder(seen, element);
                }
                if let Some(tail) = tail {
                    record_binder(seen, tail);
                }
            }
            WhenPattern::Pair(left, right) => {
                record_binder(seen, left);
                record_binder(seen, right);
            }
            WhenPattern::Var(name) => record_binder(seen, name),
            WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
        }
    }

    fn visit_expr(expr: &PseudoExpr, seen: &mut std::collections::HashMap<VarId, String>) {
        match expr {
            PseudoExpr::Lambda { params, .. } => {
                for param in params {
                    record_binder(seen, param);
                }
            }
            PseudoExpr::RecFn { name, params, .. } => {
                record_binder(seen, name);
                for param in params {
                    record_binder(seen, param);
                }
            }
            PseudoExpr::Let { name, id, .. } => {
                if let Some(vid) = *id {
                    record_id(seen, format!("let {name}"), vid);
                }
            }
            PseudoExpr::When {
                subject_name,
                clauses,
                ..
            } => {
                if let Some(subject_name) = subject_name {
                    record_binder(seen, subject_name);
                }
                for clause in clauses {
                    visit_pattern(&clause.pattern, seen);
                }
            }
            _ => {}
        }

        for child in expr.provenance_children() {
            visit_expr(child, seen);
        }
    }

    let mut seen = std::collections::HashMap::new();
    visit_expr(expr, &mut seen);
}

#[test]
fn test_delayed_rec_force_expansion_freshens_repeated_unwrapped_binders() {
    let f_id = VarId::new(9_838);
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(delayed_y_combinator_with_ids(9_850)),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                force_twice(PseudoExpr::var_with_id("f", f_id)),
                force_twice(PseudoExpr::var_with_id("f", f_id)),
            ]
            .into(),
        )),
    };

    let simplified = simplify(expr);

    assert_no_duplicate_binder_var_ids(&simplified);
    assert_eq!(
        Simplifier::count_force_chain_uses_by_id(&simplified, "f", Some(f_id), 2),
        0
    );
    let report = audit_id_orphans(&simplified, &[]);
    assert_eq!(
        report.stranded + report.truly_free,
        0,
        "repeated delayed-rec expansion should keep binder ids hygienic, got {report:?}\n{}",
        simplified.to_pretty()
    );
}

#[test]
fn test_delayed_rec_alias_force_expansion_freshens_repeated_unwrapped_binders() {
    let f_id = VarId::new(9_854);
    let g_id = VarId::new(9_855);
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(delayed_y_combinator_with_ids(9_856)),
        body: PBox::new(PseudoExpr::Let {
            name: "g".to_string(),
            id: Some(g_id),
            value: PBox::new(PseudoExpr::var_with_id("f", f_id)),
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    force_twice(PseudoExpr::var_with_id("g", g_id)),
                    force_twice(PseudoExpr::var_with_id("g", g_id)),
                ]
                .into(),
            )),
        }),
    };

    let simplified = simplify(expr);

    assert_no_duplicate_binder_var_ids(&simplified);
    assert_eq!(
        Simplifier::count_force_chain_uses_by_id(&simplified, "g", Some(g_id), 2),
        0
    );
    let report = audit_id_orphans(&simplified, &[]);
    assert_eq!(
        report.stranded + report.truly_free,
        0,
        "alias-delayed-rec expansion should keep binder ids hygienic, got {report:?}\n{}",
        simplified.to_pretty()
    );
}
