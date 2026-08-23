use super::*;
use crate::pseudo::ast::PBox;

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn binder(name: &str, id: u32) -> crate::pseudo::ast::Binder {
    crate::pseudo::ast::Binder::new(name.to_string(), VarId::new(id))
}

/// `let f = rec fn g(xs) { when xs is { [h, ..t] -> seq(use(h), g(t)) } };
///  f(un_list_data(outputs))` — h is an element of outputs; the
/// helper `use`'s param is fed only h.
#[test]
fn rec_iteration_and_param_seeding() {
    let g_body = PseudoExpr::When {
        subject: PBox::new(varref("xs", 11)),
        subject_name: None,
        clauses: vec![crate::pseudo::ast::WhenClause {
            pattern: WhenPattern::List {
                elements: vec![binder("h", 12)],
                tail: Some(binder("t", 13)),
            },
            guard: None,
            body: PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("use_fn", VarId::new(30))),
                args: vec![
                    varref("h", 12),
                    PseudoExpr::Apply {
                        function: PBox::new(varref("g", 10)),
                        args: vec![varref("t", 13)].into(),
                    },
                ]
                .into(),
            },
        }],
    };
    let tree = PseudoExpr::Let {
        name: "use_fn".to_string(),
        id: Some(VarId::new(30)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("p", 31), binder("q", 32)],
            body: PBox::new(PseudoExpr::int(0)),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "f".to_string(),
            id: Some(VarId::new(9)),
            value: PBox::new(PseudoExpr::RecFn {
                name: binder("g", 10),
                params: vec![binder("xs", 11)],
                body: PBox::new(g_body),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(varref("f", 9)),
                args: vec![PseudoExpr::BuiltinCall {
                    name: BuiltinId::DataUnList,
                    args: vec![varref("outputs", 50)].into(),
                }]
                .into(),
            }),
        }),
    };
    let ix = ListIterationIndex::build(&tree);
    let roots: BTreeSet<VarId> = [VarId::new(50)].into_iter().collect();
    let elements = ix.element_binders_of(&roots);
    assert!(
        elements.contains(&VarId::new(12)),
        "cons head is an element"
    );
    let members = ix.members_of(&roots);
    use crate::decompile::simplify::postprocess::ContextType;
    let element_claims: BTreeMap<VarId, ContextType> =
        elements.iter().map(|e| (*e, ContextType::TxOut)).collect();
    let member_claims: BTreeMap<VarId, ContextType> =
        members.iter().map(|m| (*m, ContextType::TxOut)).collect();
    let params = ix.params_with_agreed_claims(&element_claims, &member_claims);
    assert_eq!(
        params,
        vec![(VarId::new(31), ContextType::TxOut)],
        "use_fn's slot-0 param"
    );
}

/// A second call site feeding slot-0 from something ELSE disqualifies
/// the param (all-call-sites discipline).
#[test]
fn mixed_call_sites_disqualify() {
    let tree = PseudoExpr::Let {
        name: "use_fn".to_string(),
        id: Some(VarId::new(30)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("p", 31)],
            body: PBox::new(PseudoExpr::int(0)),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("seq2", VarId::new(99))),
            args: vec![
                PseudoExpr::Apply {
                    function: PBox::new(varref("use_fn", 30)),
                    args: vec![PseudoExpr::FieldAccess {
                        record: PBox::new(varref("outputs", 50)),
                        selector: FieldSelector::ListHead,
                    }]
                    .into(),
                },
                PseudoExpr::Apply {
                    function: PBox::new(varref("use_fn", 30)),
                    args: vec![varref("unrelated", 60)].into(),
                },
            ]
            .into(),
        }),
    };
    let ix = ListIterationIndex::build(&tree);
    let roots: BTreeSet<VarId> = [VarId::new(50)].into_iter().collect();
    let elements = ix.element_binders_of(&roots);
    let members = ix.members_of(&roots);
    use crate::decompile::simplify::postprocess::ContextType;
    let element_claims: BTreeMap<VarId, ContextType> =
        elements.iter().map(|e| (*e, ContextType::TxOut)).collect();
    let member_claims: BTreeMap<VarId, ContextType> =
        members.iter().map(|m| (*m, ContextType::TxOut)).collect();
    let params = ix.params_with_agreed_claims(&element_claims, &member_claims);
    assert!(params.is_empty(), "mixed sites must disqualify");
}

/// A fn referenced as a VALUE is never trusted.
#[test]
fn value_use_disqualifies() {
    let tree = PseudoExpr::Let {
        name: "use_fn".to_string(),
        id: Some(VarId::new(30)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("p", 31)],
            body: PBox::new(PseudoExpr::int(0)),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("seq2", VarId::new(99))),
            args: vec![
                PseudoExpr::Apply {
                    function: PBox::new(varref("use_fn", 30)),
                    args: vec![PseudoExpr::FieldAccess {
                        record: PBox::new(varref("outputs", 50)),
                        selector: FieldSelector::ListHead,
                    }]
                    .into(),
                },
                // value use: passed as an argument
                varref("use_fn", 30),
            ]
            .into(),
        }),
    };
    let ix = ListIterationIndex::build(&tree);
    let roots: BTreeSet<VarId> = [VarId::new(50)].into_iter().collect();
    let elements = ix.element_binders_of(&roots);
    let members = ix.members_of(&roots);
    use crate::decompile::simplify::postprocess::ContextType;
    let element_claims: BTreeMap<VarId, ContextType> =
        elements.iter().map(|e| (*e, ContextType::TxOut)).collect();
    let member_claims: BTreeMap<VarId, ContextType> =
        members.iter().map(|m| (*m, ContextType::TxOut)).collect();
    let params = ix.params_with_agreed_claims(&element_claims, &member_claims);
    assert!(params.is_empty(), "value-used fn must disqualify");
}
