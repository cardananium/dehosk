use super::*;

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

/// Count `Constr` EXPRESSIONS (constructions, not clause patterns) whose
/// shape is `Known(Error)` — the precise relabel signal. A whole-tree text
/// check would also match the consumer's `Known(Error)` clause pattern.
fn count_known_error_constructions(e: &PseudoExpr) -> usize {
    let mut n = 0;
    fn go(e: &PseudoExpr, n: &mut usize) {
        if let PseudoExpr::Constr {
            shape: ConstructorShape::Known(KnownConstructor::Error),
            ..
        } = e
        {
            *n += 1;
        }
        for c in crate::decompile::render_prep::scope_recurse::children(e) {
            go(c, n);
        }
    }
    go(e, &mut n);
    n
}

fn raw_unknown(tag: usize, fields: Vec<PseudoExpr>) -> PseudoExpr {
    let arity = fields.len();
    PseudoExpr::Constr {
        type_hint: None,
        tag,
        fields: fields.into(),
        shape: ConstructorShape::unknown_data(tag, arity),
    }
}

fn known_pattern(kc: KnownConstructor, binders: Vec<Binder>) -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag: kc.expected_tag(),
        fields: binders,
        shape: ConstructorShape::Known(kc),
    }
}

/// `expect K(b) = subject` — a `When` with a single Known clause.
fn expect_known(
    kc: KnownConstructor,
    b: Binder,
    subject: PseudoExpr,
    body: PseudoExpr,
) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: known_pattern(kc, vec![b]),
            guard: None,
            body,
        }],
    }
}

/// `expect Pair(p0, p1) = subject` — a `When` with a single Pair clause.
fn expect_pair(p0: Binder, p1: Binder, subject: PseudoExpr, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Pair(p0, p1),
            guard: None,
            body,
        }],
    }
}

/// `when subject is { Ok(_) -> True; Error(_) -> False }` (Result consumer).
fn when_result(subject: PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: known_pattern(KnownConstructor::Ok, vec![binder("ok", 700)]),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
            WhenClause {
                pattern: known_pattern(KnownConstructor::Error, vec![binder("er", 701)]),
                guard: None,
                body: PseudoExpr::Bool(false),
            },
        ],
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

/// helper_2-like consumer: `fn helper(x, y) { expect Pair(p0, p1) = y;
/// when p0 is { Ok/Error } }`. y is param index 1; component 0 consumed
/// as Result.
fn pair_result_consumer(param_ids: (u32, u32), p0_id: u32, p1_id: u32) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![binder("x", param_ids.0), binder("y", param_ids.1)],
        body: PBox::new(expect_pair(
            binder("p0", p0_id),
            binder("p1", p1_id),
            varref("y", param_ids.1),
            when_result(varref("p0", p0_id)),
        )),
    }
}

/// A construction consumed as `Result` at a Pair-component param
/// position relabels the raw `Unknown` tag-1 arity-1 to `Error`.
#[test]
fn pair_component_result_relabels_to_error() {
    // expect Error(b=500) = subject_var(400)
    // helper(x, Pair(Unknown_tag1(Var b=500), other))
    let extraction = expect_known(
        KnownConstructor::Error,
        binder("v_385", 500),
        varref("variant_33", 400),
        {
            // body of the extraction contains the call site.
            PseudoExpr::Apply {
                function: PBox::new(varref("helper", 20)),
                args: vec![
                    PseudoExpr::int(1),
                    PseudoExpr::Pair(
                        PBox::new(raw_unknown(1, vec![varref("v_385", 500)])),
                        PBox::new(varref("v_383", 600)),
                    ),
                ]
                .into(),
            }
        },
    );
    let input = with_marker(PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(pair_result_consumer((30, 31), 40, 41)),
        body: PBox::new(extraction),
    });
    // The consumer body holds a `Known(Error)` clause PATTERN, not a
    // construction, so the count is 0 before and exactly 1 after.
    assert_eq!(count_known_error_constructions(&input), 0);
    let out = relabel_stub_consumer_args(input);
    assert_eq!(
        count_known_error_constructions(&out),
        1,
        "raw tag-1 construction of an Error-provenance binder consumed at a \
         Pair-component Result position should relabel to exactly one Error \
         construction: {out:?}"
    );
}

/// SAME binder provenance (`expect Error(b)`) and SAME construction, but
/// the fn never consumes the arg as a Result (identity body): no relabel.
#[test]
fn no_consumer_witness_stays_raw() {
    let helper = PseudoExpr::Lambda {
        params: vec![binder("x", 30), binder("y", 31)],
        body: PBox::new(varref("y", 31)), // never destructured as Result
    };
    let extraction = expect_known(
        KnownConstructor::Error,
        binder("v_385", 500),
        varref("variant_33", 400),
        PseudoExpr::Apply {
            function: PBox::new(varref("helper", 20)),
            args: vec![
                PseudoExpr::int(1),
                PseudoExpr::Pair(
                    PBox::new(raw_unknown(1, vec![varref("v_385", 500)])),
                    PBox::new(varref("v_383", 600)),
                ),
            ]
            .into(),
        },
    );
    let input = with_marker(PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(helper),
        body: PBox::new(extraction),
    });
    let out = relabel_stub_consumer_args(input.clone());
    assert_eq!(
        out, input,
        "no consumer witness (arg never consumed as Result) → no relabel"
    );
}

/// A genuine stub use whose field is NOT a bare provenance `Var`
/// (`Unknown_E_1_1(un_b_data(x))`) stays raw even at a witnessed position.
#[test]
fn non_binder_field_stays_raw() {
    let non_binder_field = PseudoExpr::builtin("un_b_data", vec![varref("field_0", 800)]);
    let extraction = expect_known(
        KnownConstructor::Error,
        binder("v_385", 500),
        varref("variant_33", 400),
        PseudoExpr::Apply {
            function: PBox::new(varref("helper", 20)),
            args: vec![
                PseudoExpr::int(1),
                PseudoExpr::Pair(
                    PBox::new(raw_unknown(1, vec![non_binder_field])),
                    PBox::new(varref("v_383", 600)),
                ),
            ]
            .into(),
        },
    );
    let input = with_marker(PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(pair_result_consumer((30, 31), 40, 41)),
        body: PBox::new(extraction),
    });
    // The construction field is a non-binder builtin call, so gate 2
    // (field must be a bare `Var(b)`) rejects it; structural equality
    // asserts the whole tree is a no-op.
    let out = relabel_stub_consumer_args(input.clone());
    assert_eq!(
        out, input,
        "a non-binder stub field must stay raw (pass is a no-op here)"
    );
}

/// A multiply-bound provenance binder is skipped (VarId collision).
#[test]
fn multiply_bound_binder_skipped() {
    // The binder id 500 is bound by TWO `expect Error(..)` extractions.
    let inner_call = PseudoExpr::Apply {
        function: PBox::new(varref("helper", 20)),
        args: vec![
            PseudoExpr::int(1),
            PseudoExpr::Pair(
                PBox::new(raw_unknown(1, vec![varref("v_385", 500)])),
                PBox::new(varref("v_383", 600)),
            ),
        ]
        .into(),
    };
    let extraction2 = expect_known(
        KnownConstructor::Error,
        binder("v_385", 500), // SAME id 500 → collision
        varref("variant_44", 401),
        inner_call,
    );
    let extraction1 = expect_known(
        KnownConstructor::Error,
        binder("v_385", 500),
        varref("variant_33", 400),
        extraction2,
    );
    let input = with_marker(PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(pair_result_consumer((30, 31), 40, 41)),
        body: PBox::new(extraction1),
    });
    // Bound twice → excluded from `provenance` → no relabel anywhere.
    let out = relabel_stub_consumer_args(input.clone());
    assert_eq!(
        out, input,
        "a multiply-bound provenance binder must be skipped (no-op)"
    );
}

/// Tag mismatch: construction tag ≠ Error's tag → stays raw even with
/// provenance + witness.
#[test]
fn tag_mismatch_stays_raw() {
    // Construction uses tag 0 (Ok's tag), but the provenance ctor is Error
    // (tag 1). A tag-0 construction of an Error-provenance binder is a
    // genuine different construction — must not relabel.
    let extraction = expect_known(
        KnownConstructor::Error,
        binder("v_385", 500),
        varref("variant_33", 400),
        PseudoExpr::Apply {
            function: PBox::new(varref("helper", 20)),
            args: vec![
                PseudoExpr::int(1),
                PseudoExpr::Pair(
                    PBox::new(raw_unknown(0, vec![varref("v_385", 500)])),
                    PBox::new(varref("v_383", 600)),
                ),
            ]
            .into(),
        },
    );
    let input = with_marker(PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(pair_result_consumer((30, 31), 40, 41)),
        body: PBox::new(extraction),
    });
    let out = relabel_stub_consumer_args(input.clone());
    assert_eq!(
        out, input,
        "tag mismatch must stay raw (pass is a no-op here)"
    );
}

/// A DIRECT (non-Pair) consumer position also relabels: `fn helper(x, res)
/// { when res is { Ok/Error } }`; `helper(1, Unknown_tag1(Var b))`.
#[test]
fn direct_result_position_relabels() {
    let direct_consumer = PseudoExpr::Lambda {
        params: vec![binder("x", 30), binder("res", 31)],
        body: PBox::new(when_result(varref("res", 31))),
    };
    let extraction = expect_known(
        KnownConstructor::Error,
        binder("v_385", 500),
        varref("variant_33", 400),
        PseudoExpr::Apply {
            function: PBox::new(varref("helper", 20)),
            args: vec![
                PseudoExpr::int(1),
                raw_unknown(1, vec![varref("v_385", 500)]),
            ]
            .into(),
        },
    );
    let input = with_marker(PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(direct_consumer),
        body: PBox::new(extraction),
    });
    assert_eq!(count_known_error_constructions(&input), 0);
    let out = relabel_stub_consumer_args(input);
    assert_eq!(
        count_known_error_constructions(&out),
        1,
        "direct Result consumer position should relabel to one Error \
         construction: {out:?}"
    );
}
