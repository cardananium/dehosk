use super::*;

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn raw_some(payload: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Constr {
        type_hint: None,
        tag: 0,
        fields: vec![payload].into(),
        shape: ConstructorShape::unknown_data(0, 1),
    }
}

fn raw_none() -> PseudoExpr {
    PseudoExpr::Constr {
        type_hint: None,
        tag: 1,
        fields: vec![].into(),
        shape: ConstructorShape::unknown_data(1, 0),
    }
}

fn some_pattern() -> crate::pseudo::ast::WhenPattern {
    crate::pseudo::ast::WhenPattern::Constructor {
        type_hint: None,
        tag: 0,
        fields: vec![binder("p", 900)],
        shape: ConstructorShape::Known(KnownConstructor::Some),
    }
}

fn with_marker(body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "decompiled".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("ctx", 2)],
            body: PBox::new(body),
        }),
        body: PBox::new(varref("decompiled", 1)),
    }
}

/// Producer with raw Some/None-alias leaves + a native-Some consumer:
/// leaves relabel, the alias const stays.
#[test]
fn relabels_witnessed_producer_leaves() {
    let producer = PseudoExpr::Lambda {
        params: vec![binder("xs", 30)],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Bool(true)),
            then_branch: PBox::new(varref("d", 10)),
            else_branch: PBox::new(raw_some(varref("xs", 30))),
        }),
    };
    let consumer = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("helper", 20)),
            args: vec![PseudoExpr::int(1)].into(),
        }),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: some_pattern(),
            guard: None,
            body: PseudoExpr::Bool(true),
        }],
    };
    let input = with_marker(PseudoExpr::Let {
        name: "d".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(raw_none()),
        body: PBox::new(PseudoExpr::Let {
            name: "helper".to_string(),
            id: Some(VarId::new(20)),
            value: PBox::new(producer),
            body: PBox::new(consumer),
        }),
    });
    let out = relabel_option_producer_leaves(input);
    let rendered = format!("{out:?}");
    // The producer's leaves became Known Some/None…
    assert!(
        rendered.contains("Known(None)") && rendered.contains("Known(Some)"),
        "expected relabeled producer leaves, got: {rendered}"
    );
    // …while the alias const keeps its raw value (church sites safe).
    let PseudoExpr::Let { value, .. } = &out else {
        panic!()
    };
    let PseudoExpr::Lambda { body, .. } = value.as_ref() else {
        panic!()
    };
    let PseudoExpr::Let { value: d_value, .. } = body.as_ref() else {
        panic!()
    };
    assert!(is_raw_none(d_value), "const d must stay raw: {d_value:?}");
}

/// No native-Option consumer: the producer is untouched even though
/// its leaves are Option-shaped.
#[test]
fn no_witness_no_relabel() {
    let producer = PseudoExpr::Lambda {
        params: vec![binder("xs", 30)],
        body: PBox::new(raw_some(varref("xs", 30))),
    };
    let input = with_marker(PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(producer),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("helper", 20)),
            args: vec![PseudoExpr::int(1)].into(),
        }),
    });
    let out = relabel_option_producer_leaves(input.clone());
    assert_eq!(out, input);
}

/// Non-leaf raw constructors (a `Let` value inside the body) stay
/// raw — only RETURN leaves relabel.
#[test]
fn non_leaf_positions_stay_raw() {
    let producer = PseudoExpr::Lambda {
        params: vec![binder("xs", 30)],
        body: PBox::new(PseudoExpr::Let {
            name: "tmp".to_string(),
            id: Some(VarId::new(40)),
            // Raw Some in a LET VALUE — not a return leaf.
            value: PBox::new(raw_some(varref("xs", 30))),
            body: PBox::new(raw_none()),
        }),
    };
    let consumer = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("helper", 20)),
            args: vec![PseudoExpr::int(1)].into(),
        }),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: some_pattern(),
            guard: None,
            body: PseudoExpr::Bool(true),
        }],
    };
    let input = with_marker(PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(producer),
        body: PBox::new(consumer),
    });
    let out = relabel_option_producer_leaves(input);
    let rendered = format!("{out:?}");
    // The let VALUE keeps its raw Unknown shape; the None leaf relabels.
    assert!(
        rendered.contains("Unknown { tag: 0, arity: 1, origin: DataTag, church_true: None }"),
        "non-leaf raw Some must stay raw: {rendered}"
    );
    assert!(rendered.contains("Known(None)"));
}
