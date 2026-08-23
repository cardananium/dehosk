use super::*;

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn ok_arg(payload: PseudoExpr) -> PseudoExpr {
    PseudoExpr::constr_known(KnownConstructor::Ok, vec![payload])
}

fn raw_unknown_some(payload: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Constr {
        type_hint: None,
        tag: 0,
        fields: vec![payload].into(),
        shape: ConstructorShape::unknown_data(0, 1),
    }
}

fn raw_unknown_none() -> PseudoExpr {
    PseudoExpr::Constr {
        type_hint: None,
        tag: 1,
        fields: vec![].into(),
        shape: ConstructorShape::unknown_data(1, 0),
    }
}

fn error_arg(payload: PseudoExpr) -> PseudoExpr {
    PseudoExpr::constr_known(KnownConstructor::Error, vec![payload])
}

fn some_pattern() -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag: 0,
        fields: vec![binder("p", 900)],
        shape: ConstructorShape::Known(KnownConstructor::Some),
    }
}

fn none_pattern() -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag: 1,
        fields: vec![],
        shape: ConstructorShape::Known(KnownConstructor::None),
    }
}

fn ok_pattern() -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag: 0,
        fields: vec![binder("p", 901)],
        shape: ConstructorShape::Known(KnownConstructor::Ok),
    }
}

fn error_pattern() -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag: 1,
        fields: vec![binder("e", 902)],
        shape: ConstructorShape::Known(KnownConstructor::Error),
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

/// A fn whose 2nd param is matched as `Some`/`None`.
fn helper_with_option_param(param_ids: (u32, u32)) -> PseudoExpr {
    // fn helper(a, opt) { when opt is { Some(p) -> True; None -> False } }
    PseudoExpr::Lambda {
        params: vec![binder("a", param_ids.0), binder("opt", param_ids.1)],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(varref("opt", param_ids.1)),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: some_pattern(),
                    guard: None,
                    body: PseudoExpr::Bool(true),
                },
                WhenClause {
                    pattern: none_pattern(),
                    guard: None,
                    body: PseudoExpr::Bool(false),
                },
            ],
        }),
    }
}

#[test]
fn relabels_witnessed_ok_and_raw_args() {
    let input = with_marker(PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(helper_with_option_param((30, 31))),
        body: PBox::new(PseudoExpr::List {
            elements: vec![
                // Ok(x) at the Option position -> Some(x)
                PseudoExpr::Apply {
                    function: PBox::new(varref("helper", 20)),
                    args: vec![PseudoExpr::int(1), ok_arg(PseudoExpr::int(7))].into(),
                },
                // nullary raw Unknown tag-1 -> None
                PseudoExpr::Apply {
                    function: PBox::new(varref("helper", 20)),
                    args: vec![PseudoExpr::int(1), raw_unknown_none()].into(),
                },
                // raw Unknown tag-0 arity-1 -> Some
                PseudoExpr::Apply {
                    function: PBox::new(varref("helper", 20)),
                    args: vec![PseudoExpr::int(1), raw_unknown_some(PseudoExpr::int(9))].into(),
                },
            ]
            .into(),
            tail: None,
        }),
    });
    let out = relabel_option_consumer_args(input);
    let rendered = format!("{out:?}");
    assert!(
        rendered.contains("Known(Some)"),
        "Ok/raw arg at Option position should relabel to Some: {rendered}"
    );
    assert!(
        rendered.contains("Known(None)"),
        "nullary tag-1 arg should relabel to None: {rendered}"
    );
    // The Ok label must be gone (it was the only Ok in the tree).
    assert!(
        !rendered.contains("Known(Ok)"),
        "the mislabeled Ok should have been relabeled: {rendered}"
    );
}

#[test]
fn no_witness_no_relabel() {
    // Same helper but NO `when opt is Some/None` — a plain identity body.
    let helper = PseudoExpr::Lambda {
        params: vec![binder("a", 30), binder("opt", 31)],
        body: PBox::new(varref("opt", 31)),
    };
    let input = with_marker(PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(helper),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("helper", 20)),
            args: vec![PseudoExpr::int(1), ok_arg(PseudoExpr::int(7))].into(),
        }),
    });
    let out = relabel_option_consumer_args(input.clone());
    assert_eq!(out, input, "no Option-consuming param → no relabel");
}

#[test]
fn wrong_tag_or_arity_stays_raw() {
    // Witnessed Option position, but the arg is a nullary tag-0 (not the
    // arity-1 Some shape) — must stay raw.
    let weird_arg = PseudoExpr::Constr {
        type_hint: None,
        tag: 0,
        fields: vec![].into(),
        shape: ConstructorShape::unknown_data(0, 0),
    };
    let input = with_marker(PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(helper_with_option_param((30, 31))),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("helper", 20)),
            args: vec![PseudoExpr::int(1), weird_arg].into(),
        }),
    });
    // Whole-tree text checks would false-positive on the consuming
    // `when opt is { Some/None }` patterns, so assert structural equality.
    let out = relabel_option_consumer_args(input.clone());
    assert_eq!(out, input, "tag-0 arity-0 arg must not relabel");
}

/// A UNARY tag-1 position — a genuine `Result` consumer (`Ok`/`Error`,
/// `Error` is unary) — is NOT recorded, so an `Ok(x)` arg stays `Ok`.
#[test]
fn genuine_result_position_not_relabeled() {
    // fn helper(a, res) { when res is { Ok(p) -> True; Error(e) -> False } }
    let helper = PseudoExpr::Lambda {
        params: vec![binder("a", 30), binder("res", 31)],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(varref("res", 31)),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: ok_pattern(),
                    guard: None,
                    body: PseudoExpr::Bool(true),
                },
                WhenClause {
                    pattern: error_pattern(),
                    guard: None,
                    body: PseudoExpr::Bool(false),
                },
            ],
        }),
    };
    let input = with_marker(PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(helper),
        body: PBox::new(PseudoExpr::List {
            elements: vec![
                PseudoExpr::Apply {
                    function: PBox::new(varref("helper", 20)),
                    args: vec![PseudoExpr::int(1), ok_arg(PseudoExpr::int(7))].into(),
                },
                PseudoExpr::Apply {
                    function: PBox::new(varref("helper", 20)),
                    args: vec![PseudoExpr::int(1), error_arg(PseudoExpr::int(8))].into(),
                },
            ]
            .into(),
            tail: None,
        }),
    });
    let out = relabel_option_consumer_args(input.clone());
    assert_eq!(
        out, input,
        "genuine Result consumer (unary Error) must not be relabeled"
    );
}
