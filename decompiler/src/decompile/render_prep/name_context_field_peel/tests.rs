use super::*;
use crate::decompile::render_prep::RenderCtx;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, WhenClause};
use crate::pseudo::field_selector::FieldSelector;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn nil_pat() -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag: 0,
        fields: Vec::new(),
        shape: ConstructorShape::Known(KnownConstructor::Nil),
    }
}

fn cons_pat(head: Binder, tail: Binder) -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag: 1,
        fields: vec![head, tail],
        shape: ConstructorShape::Known(KnownConstructor::Cons),
    }
}

fn when(subject: PseudoExpr, clauses: Vec<WhenClause>) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses,
    }
}

fn clause(pattern: WhenPattern, body: PseudoExpr) -> WhenClause {
    WhenClause {
        pattern,
        guard: None,
        body,
    }
}

fn fail() -> PseudoExpr {
    PseudoExpr::Error { message: None }
}

/// `script_context.fields`, wrapped in the compiler's list-conversion call.
fn ctx_fields(wrapped: bool) -> PseudoExpr {
    let access = PseudoExpr::FieldAccess {
        record: PBox::new(var("script_context", 1)),
        selector: FieldSelector::NamedField("fields".to_string()),
    };
    if wrapped {
        PseudoExpr::Apply {
            function: PBox::new(var("o", 99)),
            args: vec![access].into(),
        }
    } else {
        access
    }
}

fn constr(tag: usize, fields: Vec<PseudoExpr>) -> PseudoExpr {
    PseudoExpr::Constr {
        tag,
        shape: ConstructorShape::unknown_data(tag, fields.len()),
        fields: fields.into(),
        type_hint: None,
    }
}

/// `rec fn o(z) { …; Cons(<head>, o(<tail>)); Nil }` — the identity
/// rebuild. `head_through` decides whether the head is passed through
/// untouched or wrapped, which is what separates a copy from a `map`.
fn rebuild_def(head_through: bool) -> PseudoExpr {
    let head = var("h", 80);
    let head_expr = if head_through {
        head
    } else {
        PseudoExpr::Apply {
            function: PBox::new(var("g", 82)),
            args: vec![head].into(),
        }
    };
    let cons = constr(
        1,
        vec![
            head_expr,
            PseudoExpr::Apply {
                function: PBox::new(var("o", 99)),
                args: vec![var("t", 81)].into(),
            },
        ],
    );
    PseudoExpr::RecFn {
        name: binder("o", 99),
        params: vec![binder("z", 83)],
        body: PBox::new(when(
            var("z", 83),
            vec![
                clause(nil_pat(), constr(0, Vec::new())),
                clause(cons_pat(binder("h", 80), binder("t", 81)), cons),
            ],
        )),
    }
}

/// Bind the wrapper next to the entry so the pass can look it up.
fn with_rebuild(head_through: bool, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "o".to_string(),
        id: Some(VarId::new(99)),
        value: PBox::new(rebuild_def(head_through)),
        body: PBox::new(body),
    }
}

/// Build the peel chain: one `when` per head, then a terminal `when` on
/// the last tail. `terminate` decides whether that terminal one carries
/// the `[]` arm — the length proof the pass requires.
fn peel_chain(subject: PseudoExpr, heads: &[&str], terminate: bool) -> PseudoExpr {
    // Innermost first: the terminal match on the final tail.
    let mut inner = when(
        var(&format!("t{}", heads.len()), 10 + heads.len() as u32),
        if terminate {
            vec![
                clause(nil_pat(), PseudoExpr::Unit),
                clause(cons_pat(binder("_extra", 90), binder("_rest", 91)), fail()),
            ]
        } else {
            vec![clause(
                cons_pat(binder("_extra", 90), binder("_rest", 91)),
                PseudoExpr::Unit,
            )]
        },
    );
    for (i, head) in heads.iter().enumerate().rev() {
        let subject_expr = if i == 0 {
            subject.clone()
        } else {
            var(&format!("t{i}"), 10 + i as u32)
        };
        inner = when(
            subject_expr,
            vec![
                clause(nil_pat(), fail()),
                clause(
                    cons_pat(
                        binder(head, 20 + i as u32),
                        binder(&format!("t{}", i + 1), 11 + i as u32),
                    ),
                    inner,
                ),
            ],
        );
    }
    inner
}

/// A V3 peel: three heads, then a `[]` match proving the length.
fn v3_peel(wrapped: bool, terminate: bool, heads: [&str; 3]) -> PseudoExpr {
    peel_chain(ctx_fields(wrapped), &heads, terminate)
}

fn entry(body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "decompiled".to_string(),
        id: Some(VarId::new(100)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("script_context", 1)],
            body: PBox::new(body),
        }),
        body: PBox::new(PseudoExpr::Unit),
    }
}

fn run(expr: PseudoExpr, version: Option<ScriptVersion>) -> PseudoExpr {
    name_context_field_peel(expr, &RenderCtx::at(version))
}

/// Same, with the version marked a GUESS.
fn run_guessed(expr: PseudoExpr, version: Option<ScriptVersion>) -> PseudoExpr {
    name_context_field_peel(expr, &RenderCtx::at(version).guessed())
}

fn rendered_binders(expr: &PseudoExpr) -> Vec<String> {
    let mut out = Vec::new();
    collect_binders(expr, &mut out);
    out
}

fn collect_binders(expr: &PseudoExpr, out: &mut Vec<String>) {
    if let PseudoExpr::When { clauses, .. } = expr {
        for c in clauses {
            if let WhenPattern::Constructor { fields, .. } = &c.pattern {
                for f in fields {
                    out.push(f.as_str().to_string());
                }
            }
        }
    }
    for child in super::children(expr) {
        collect_binders(child, out);
    }
}

/// The three V3 `ScriptContext` slots get their schema names.
#[test]
fn names_the_v3_context_triple() {
    let expr = with_rebuild(
        true,
        entry(v3_peel(true, true, ["v_225", "variant_0", "variant_0_4"])),
    );
    let out = run(expr, Some(ScriptVersion::PlutusV3));
    let names = rendered_binders(&out);
    for expected in ["tx_info", "redeemer", "script_info"] {
        assert!(
            names.iter().any(|n| n == expected),
            "expected `{expected}` among {names:?}"
        );
    }
}

/// V1/V2 `ScriptContext` is a pair, so only two slots are named.
#[test]
fn names_the_v1v2_context_pair() {
    let peel = peel_chain(ctx_fields(false), &["v_1", "v_2"], true);
    let out = run(entry(peel), Some(ScriptVersion::PlutusV2));
    let names = rendered_binders(&out);
    assert!(names.iter().any(|n| n == "tx_info"), "{names:?}");
    assert!(names.iter().any(|n| n == "purpose"), "{names:?}");
}

/// The `[]` terminator is not required. A script that peels only the
/// first few fields of a record still gets those named — position `i` is
/// field `i` whatever the chain does afterwards.
#[test]
fn names_a_short_peel() {
    let expr = with_rebuild(
        true,
        entry(v3_peel(true, false, ["v_225", "variant_0", "variant_0_4"])),
    );
    let out = run(expr, Some(ScriptVersion::PlutusV3));
    let names = rendered_binders(&out);
    for expected in ["tx_info", "redeemer", "script_info"] {
        assert!(names.iter().any(|n| n == expected), "{names:?}");
    }
}

/// A binder the body never reads came in as `_`; the schema name keeps
/// that marker so it says WHICH field is skipped without reading as a
/// live binding.
#[test]
fn keeps_the_unused_marker_on_a_skipped_field() {
    let expr = with_rebuild(
        true,
        entry(v3_peel(true, true, ["v_225", "_", "variant_0_4"])),
    );
    let out = run(expr, Some(ScriptVersion::PlutusV3));
    let names = rendered_binders(&out);
    assert!(names.iter().any(|n| n == "_redeemer"), "{names:?}");
    assert!(!names.iter().any(|n| n == "redeemer"), "{names:?}");
}

/// A name a naming pass already chose deliberately is left alone.
#[test]
fn leaves_a_deliberate_name_alone() {
    let expr = with_rebuild(
        true,
        entry(v3_peel(
            true,
            true,
            ["own_input", "variant_0", "variant_0_4"],
        )),
    );
    let out = run(expr, Some(ScriptVersion::PlutusV3));
    let names = rendered_binders(&out);
    assert!(names.iter().any(|n| n == "own_input"), "{names:?}");
    assert!(!names.iter().any(|n| n == "tx_info"), "{names:?}");
}

/// The bare `script_context.fields` subject works too — the conversion
/// call is optional.
#[test]
fn names_through_a_bare_fields_subject() {
    let expr = entry(v3_peel(false, true, ["v_225", "variant_0", "variant_0_4"]));
    let out = run(expr, Some(ScriptVersion::PlutusV3));
    assert!(
        rendered_binders(&out).iter().any(|n| n == "tx_info"),
        "bare subject must name too"
    );
}

/// No render version pinned ⇒ no schema to name against.
#[test]
fn abstains_without_a_render_version() {
    let expr = with_rebuild(
        true,
        entry(v3_peel(true, true, ["v_225", "variant_0", "variant_0_4"])),
    );
    let out = run(expr, None);
    assert!(
        !rendered_binders(&out).iter().any(|n| n == "tx_info"),
        "versionless render must abstain"
    );
}

/// A wrapper that transforms each head is a `map`, not a copy: its
/// result has the right LENGTH but its slots are not the context's
/// fields. Arity alone would let it through.
#[test]
fn rejects_a_mapping_wrapper() {
    let expr = with_rebuild(
        false,
        entry(v3_peel(true, true, ["v_225", "variant_0", "variant_0_4"])),
    );
    let out = run(expr, Some(ScriptVersion::PlutusV3));
    assert!(
        !rendered_binders(&out).iter().any(|n| n == "tx_info"),
        "a head-transforming wrapper must not be read as a copy"
    );
}

/// An unresolvable wrapper is not assumed to be a copy either.
#[test]
fn rejects_an_undefined_wrapper() {
    let expr = entry(v3_peel(true, true, ["v_225", "variant_0", "variant_0_4"]));
    let out = run(expr, Some(ScriptVersion::PlutusV3));
    assert!(
        !rendered_binders(&out).iter().any(|n| n == "tx_info"),
        "no definition ⇒ no proof"
    );
}

/// PlutusTx hoists each record's destructuring into its own function.
/// The type has to cross that call for anything below it to be named:
/// slot 0 of the context is a `TxInfo`, so the helper it is passed to
/// peels `TxInfo` fields.
#[test]
fn carries_the_record_type_into_a_helper() {
    // `fn helper(p) { when o(p.fields) is { [] -> fail; [h, ..t] -> Void } }`
    let helper_body = when(
        PseudoExpr::Apply {
            function: PBox::new(var("o", 99)),
            args: vec![PseudoExpr::FieldAccess {
                record: PBox::new(var("p", 60)),
                selector: FieldSelector::NamedField("fields".to_string()),
            }]
            .into(),
        },
        vec![
            clause(nil_pat(), fail()),
            clause(
                cons_pat(binder("v_900", 61), binder("t_900", 62)),
                PseudoExpr::Unit,
            ),
        ],
    );
    let helper = PseudoExpr::Lambda {
        params: vec![binder("p", 60)],
        body: PBox::new(helper_body),
    };
    // The context peel, whose slot 0 is handed to the helper.
    let ctx_peel = when(
        ctx_fields(true),
        vec![
            clause(nil_pat(), fail()),
            clause(
                cons_pat(binder("v_225", 20), binder("t1", 11)),
                PseudoExpr::Apply {
                    function: PBox::new(var("helper", 50)),
                    args: vec![var("v_225", 20)].into(),
                },
            ),
        ],
    );
    let expr = with_rebuild(
        true,
        PseudoExpr::Let {
            name: "helper".to_string(),
            id: Some(VarId::new(50)),
            value: PBox::new(helper),
            body: PBox::new(entry(ctx_peel)),
        },
    );
    let out = run(expr, Some(ScriptVersion::PlutusV3));
    let names = rendered_binders(&out);
    assert!(names.iter().any(|n| n == "tx_info"), "{names:?}");
    assert!(
        names.iter().any(|n| n == "inputs"),
        "the helper's peel must be named as TxInfo: {names:?}"
    );
}

/// Two call sites passing different record types say nothing about the
/// parameter, so it stays unnamed rather than taking a winner.
#[test]
fn does_not_carry_a_type_across_disagreeing_call_sites() {
    let helper_body = when(
        PseudoExpr::Apply {
            function: PBox::new(var("o", 99)),
            args: vec![PseudoExpr::FieldAccess {
                record: PBox::new(var("p", 60)),
                selector: FieldSelector::NamedField("fields".to_string()),
            }]
            .into(),
        },
        vec![
            clause(nil_pat(), fail()),
            clause(
                cons_pat(binder("v_900", 61), binder("t_900", 62)),
                PseudoExpr::Unit,
            ),
        ],
    );
    let helper = PseudoExpr::Lambda {
        params: vec![binder("p", 60)],
        body: PBox::new(helper_body),
    };
    let call = |id: u32| PseudoExpr::Apply {
        function: PBox::new(var("helper", 50)),
        args: vec![var("x", id)].into(),
    };
    // slot 0 (a TxInfo) and slot 2 (a ScriptInfo is a SUM, so untyped
    // here) reach the same parameter.
    let ctx_peel = when(
        ctx_fields(true),
        vec![
            clause(nil_pat(), fail()),
            clause(
                cons_pat(binder("v_225", 20), binder("t1", 11)),
                PseudoExpr::Apply {
                    function: PBox::new(var("seq", 70)),
                    args: vec![call(20), call(77)].into(),
                },
            ),
        ],
    );
    let expr = with_rebuild(
        true,
        PseudoExpr::Let {
            name: "helper".to_string(),
            id: Some(VarId::new(50)),
            value: PBox::new(helper),
            body: PBox::new(entry(ctx_peel)),
        },
    );
    let out = run(expr, Some(ScriptVersion::PlutusV3));
    let names = rendered_binders(&out);
    assert!(names.iter().any(|n| n == "tx_info"), "{names:?}");
    assert!(
        !names.iter().any(|n| n == "inputs"),
        "a disagreeing position must not be typed: {names:?}"
    );
}

/// Under an unsettled V1/V2 band only the positions both layouts agree
/// on are named. `TxInfo` index 0 is `inputs` either way; index 1 is
/// `reference_inputs` in V2 and `outputs` in V1, so it stays as it was.
#[test]
fn holds_back_divergent_positions_when_the_version_is_a_guess() {
    // ScriptContext slot 0 is the TxInfo; the peel below walks it. Its
    // binder ids must not collide with the outer peel's.
    let inner_tail = when(
        var("t_801", 802),
        vec![clause(
            cons_pat(binder("v_801", 801), binder("t_802", 803)),
            PseudoExpr::Unit,
        )],
    );
    let tx_peel = when(
        PseudoExpr::Apply {
            function: PBox::new(var("o", 99)),
            args: vec![PseudoExpr::FieldAccess {
                record: PBox::new(var("v_225", 20)),
                selector: FieldSelector::NamedField("fields".to_string()),
            }]
            .into(),
        },
        vec![
            clause(nil_pat(), fail()),
            clause(
                cons_pat(binder("v_800", 800), binder("t_801", 802)),
                inner_tail,
            ),
        ],
    );
    let ctx_peel = when(
        ctx_fields(true),
        vec![
            clause(nil_pat(), fail()),
            clause(cons_pat(binder("v_225", 20), binder("t1", 11)), tx_peel),
        ],
    );
    let expr = with_rebuild(true, entry(ctx_peel));

    let out = run_guessed(expr, Some(ScriptVersion::PlutusV2));

    let names = rendered_binders(&out);
    assert!(names.iter().any(|n| n == "tx_info"), "{names:?}");
    assert!(
        names.iter().any(|n| n == "inputs"),
        "index 0 is invariant: {names:?}"
    );
    assert!(
        !names.iter().any(|n| n == "reference_inputs"),
        "index 1 diverges between V1 and V2: {names:?}"
    );
}

/// A helper called once with a typed value and once with something
/// untyped is not pinned down, whichever call the walk reaches first.
#[test]
fn an_untyped_call_site_blocks_propagation() {
    for typed_first in [true, false] {
        let helper_body = when(
            PseudoExpr::Apply {
                function: PBox::new(var("o", 99)),
                args: vec![PseudoExpr::FieldAccess {
                    record: PBox::new(var("p", 60)),
                    selector: FieldSelector::NamedField("fields".to_string()),
                }]
                .into(),
            },
            vec![
                clause(nil_pat(), fail()),
                clause(
                    cons_pat(binder("v_900", 61), binder("t_900", 62)),
                    PseudoExpr::Unit,
                ),
            ],
        );
        let helper = PseudoExpr::Lambda {
            params: vec![binder("p", 60)],
            body: PBox::new(helper_body),
        };
        let call = |id: u32| PseudoExpr::Apply {
            function: PBox::new(var("helper", 50)),
            args: vec![var("x", id)].into(),
        };
        // 20 is the context's slot 0 (a TxInfo); 77 is never typed.
        let (first, second) = if typed_first {
            (call(20), call(77))
        } else {
            (call(77), call(20))
        };
        let ctx_peel = when(
            ctx_fields(true),
            vec![
                clause(nil_pat(), fail()),
                clause(
                    cons_pat(binder("v_225", 20), binder("t1", 11)),
                    PseudoExpr::Apply {
                        function: PBox::new(var("seq", 70)),
                        args: vec![first, second].into(),
                    },
                ),
            ],
        );
        let expr = with_rebuild(
            true,
            PseudoExpr::Let {
                name: "helper".to_string(),
                id: Some(VarId::new(50)),
                value: PBox::new(helper),
                body: PBox::new(entry(ctx_peel)),
            },
        );
        let out = run(expr, Some(ScriptVersion::PlutusV3));
        let names = rendered_binders(&out);
        assert!(
            !names.iter().any(|n| n == "inputs"),
            "typed_first={typed_first}: an untyped call must block it: {names:?}"
        );
    }
}

/// A callee whose name is used as a VALUE can be called from a site this
/// survey never sees, so its parameters stay unpinned.
#[test]
fn a_callee_used_as_a_value_blocks_propagation() {
    let helper_body = when(
        PseudoExpr::Apply {
            function: PBox::new(var("o", 99)),
            args: vec![PseudoExpr::FieldAccess {
                record: PBox::new(var("p", 60)),
                selector: FieldSelector::NamedField("fields".to_string()),
            }]
            .into(),
        },
        vec![
            clause(nil_pat(), fail()),
            clause(
                cons_pat(binder("v_900", 61), binder("t_900", 62)),
                PseudoExpr::Unit,
            ),
        ],
    );
    let helper = PseudoExpr::Lambda {
        params: vec![binder("p", 60)],
        body: PBox::new(helper_body),
    };
    let ctx_peel = when(
        ctx_fields(true),
        vec![
            clause(nil_pat(), fail()),
            clause(
                cons_pat(binder("v_225", 20), binder("t1", 11)),
                PseudoExpr::Apply {
                    function: PBox::new(var("seq", 70)),
                    args: vec![
                        PseudoExpr::Apply {
                            function: PBox::new(var("helper", 50)),
                            args: vec![var("v_225", 20)].into(),
                        },
                        // handed to something else, so the call set above
                        // is not the whole story
                        PseudoExpr::Apply {
                            function: PBox::new(var("register", 71)),
                            args: vec![var("helper", 50)].into(),
                        },
                    ]
                    .into(),
                },
            ),
        ],
    );
    let expr = with_rebuild(
        true,
        PseudoExpr::Let {
            name: "helper".to_string(),
            id: Some(VarId::new(50)),
            value: PBox::new(helper),
            body: PBox::new(entry(ctx_peel)),
        },
    );
    let out = run(expr, Some(ScriptVersion::PlutusV3));
    let names = rendered_binders(&out);
    assert!(names.iter().any(|n| n == "tx_info"), "{names:?}");
    assert!(
        !names.iter().any(|n| n == "inputs"),
        "an escaping callee must block it: {names:?}"
    );
}

/// A wrapper that copies on one branch and transforms on another still
/// returns a list of the same length, and its slots are not the input's.
/// One identity cell is not enough.
#[test]
fn rejects_a_wrapper_that_only_sometimes_copies() {
    let identity_cell = constr(
        1,
        vec![
            var("h", 80),
            PseudoExpr::Apply {
                function: PBox::new(var("o", 99)),
                args: vec![var("t", 81)].into(),
            },
        ],
    );
    let mapping_cell = constr(
        1,
        vec![
            PseudoExpr::Apply {
                function: PBox::new(var("g", 82)),
                args: vec![var("h", 80)].into(),
            },
            PseudoExpr::Apply {
                function: PBox::new(var("o", 99)),
                args: vec![var("t", 81)].into(),
            },
        ],
    );
    let mixed = PseudoExpr::RecFn {
        name: binder("o", 99),
        params: vec![binder("z", 83)],
        body: PBox::new(when(
            var("z", 83),
            vec![
                clause(nil_pat(), constr(0, Vec::new())),
                clause(cons_pat(binder("h", 80), binder("t", 81)), identity_cell),
                clause(cons_pat(binder("h2", 84), binder("t2", 85)), mapping_cell),
            ],
        )),
    };
    let expr = PseudoExpr::Let {
        name: "o".to_string(),
        id: Some(VarId::new(99)),
        value: PBox::new(mixed),
        body: PBox::new(entry(v3_peel(
            true,
            true,
            ["v_225", "variant_0", "variant_0_4"],
        ))),
    };
    let out = run(expr, Some(ScriptVersion::PlutusV3));
    assert!(
        !rendered_binders(&out).iter().any(|n| n == "tx_info"),
        "a sometimes-copying wrapper must not be read as a copy"
    );
}

/// Every `<record>.<field>` access in the tree, for the payload-index
/// assertions below.
fn field_accesses(expr: &PseudoExpr) -> Vec<String> {
    let mut out = Vec::new();
    walk_field_accesses(expr, &mut out);
    out
}

fn walk_field_accesses(expr: &PseudoExpr, out: &mut Vec<String>) {
    if let PseudoExpr::FieldAccess { record, selector } = expr
        && let PseudoExpr::Var { name, .. } = record.as_ref()
    {
        out.push(format!("{name}.{}", selector.as_pretty_name()));
    }
    for child in super::children(expr) {
        walk_field_accesses(child, out);
    }
}

/// `map_fn(f)` returns a walker that rebuilds the list as
/// `Cons(f(head), self(tail))`.
fn map_combinator() -> PseudoExpr {
    let cell = constr(
        1,
        vec![
            PseudoExpr::Apply {
                function: PBox::new(var("f", 120)),
                args: vec![var("h", 121)].into(),
            },
            PseudoExpr::Apply {
                function: PBox::new(var("walk", 123)),
                args: vec![var("t", 122)].into(),
            },
        ],
    );
    PseudoExpr::Lambda {
        params: vec![binder("f", 120)],
        body: PBox::new(PseudoExpr::RecFn {
            name: binder("walk", 123),
            params: vec![binder("z", 124)],
            body: PBox::new(when(
                var("z", 124),
                vec![
                    clause(nil_pat(), constr(0, Vec::new())),
                    clause(cons_pat(binder("h", 121), binder("t", 122)), cell),
                ],
            )),
        }),
    }
}

/// Bind the rebuild, the map combinator and `body` together.
fn with_map(body: PseudoExpr) -> PseudoExpr {
    with_rebuild(
        true,
        PseudoExpr::Let {
            name: "map_fn".to_string(),
            id: Some(VarId::new(110)),
            value: PBox::new(map_combinator()),
            body: PBox::new(body),
        },
    )
}

/// The context peel, with `over` run on the TxInfo's `inputs`.
fn ctx_then_tx(over: impl Fn() -> PseudoExpr) -> PseudoExpr {
    let tx_peel = when(
        PseudoExpr::Apply {
            function: PBox::new(var("o", 99)),
            args: vec![PseudoExpr::FieldAccess {
                record: PBox::new(var("v_225", 20)),
                selector: FieldSelector::NamedField("fields".to_string()),
            }]
            .into(),
        },
        vec![
            clause(nil_pat(), fail()),
            clause(cons_pat(binder("v_800", 800), binder("t_801", 802)), over()),
        ],
    );
    when(
        ctx_fields(true),
        vec![
            clause(nil_pat(), fail()),
            clause(cons_pat(binder("v_225", 20), binder("t1", 11)), tx_peel),
        ],
    )
}

/// `inputs : List<TxInInfo>`, so a callback mapped over it takes a
/// `TxInInfo` — and its own destructuring gets named from that.
#[test]
fn carries_the_element_type_into_an_inline_map_callback() {
    let callback = PseudoExpr::Lambda {
        params: vec![binder("x_31", 130)],
        body: PBox::new(when(
            var("x_31", 130),
            vec![clause(
                WhenPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![binder("field_0", 131), binder("field_1", 132)],
                    shape: ConstructorShape::unknown_data(0, 2),
                },
                PseudoExpr::Unit,
            )],
        )),
    };
    let over = || PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("map_fn", 110)),
            args: vec![callback.clone()].into(),
        }),
        args: vec![var("v_800", 800)].into(),
    };
    let out = run(
        with_map(entry(ctx_then_tx(over))),
        Some(ScriptVersion::PlutusV3),
    );
    let names = rendered_binders(&out);
    assert!(names.iter().any(|n| n == "inputs"), "{names:?}");
    for expected in ["out_ref", "resolved"] {
        assert!(
            names.iter().any(|n| n == expected),
            "the element's own fields must be named: {names:?}"
        );
    }
}

/// A combinator that transforms on one branch and copies on another is
/// not a map: its result's slots are not the input's elements.
#[test]
fn rejects_a_combinator_that_only_sometimes_maps() {
    let mapped = constr(
        1,
        vec![
            PseudoExpr::Apply {
                function: PBox::new(var("f", 120)),
                args: vec![var("h", 121)].into(),
            },
            PseudoExpr::Apply {
                function: PBox::new(var("walk", 123)),
                args: vec![var("t", 122)].into(),
            },
        ],
    );
    let raw = constr(
        1,
        vec![
            var("h", 121),
            PseudoExpr::Apply {
                function: PBox::new(var("walk", 123)),
                args: vec![var("t", 122)].into(),
            },
        ],
    );
    let mixed = PseudoExpr::Lambda {
        params: vec![binder("f", 120)],
        body: PBox::new(PseudoExpr::RecFn {
            name: binder("walk", 123),
            params: vec![binder("z", 124)],
            body: PBox::new(when(
                var("z", 124),
                vec![
                    clause(nil_pat(), constr(0, Vec::new())),
                    clause(cons_pat(binder("h", 121), binder("t", 122)), mapped),
                    clause(cons_pat(binder("h3", 125), binder("t3", 126)), raw),
                ],
            )),
        }),
    };
    let callback = PseudoExpr::Lambda {
        params: vec![binder("x_31", 130)],
        body: PBox::new(when(
            var("x_31", 130),
            vec![clause(
                WhenPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![binder("field_0", 131)],
                    shape: ConstructorShape::unknown_data(0, 1),
                },
                PseudoExpr::Unit,
            )],
        )),
    };
    let over = || PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("map_fn", 110)),
            args: vec![callback.clone()].into(),
        }),
        args: vec![var("v_800", 800)].into(),
    };
    let expr = with_rebuild(
        true,
        PseudoExpr::Let {
            name: "map_fn".to_string(),
            id: Some(VarId::new(110)),
            value: PBox::new(mixed),
            body: PBox::new(entry(ctx_then_tx(over))),
        },
    );
    let out = run(expr, Some(ScriptVersion::PlutusV3));
    let names = rendered_binders(&out);
    assert!(names.iter().any(|n| n == "inputs"), "{names:?}");
    assert!(
        !names.iter().any(|n| n == "out_ref"),
        "a sometimes-mapping combinator must not type the element: {names:?}"
    );
}

/// `let p = <record>.fields` then `p.head` / `p[1]` reads the record's
/// fields; both spellings decode the same `Data` element.
#[test]
fn resolves_a_let_bound_payload_list() {
    // slot 0 of the context is the TxInfo; its slot 7 is the interval.
    let uses = PseudoExpr::Apply {
        function: PBox::new(var("seq", 70)),
        args: vec![
            PseudoExpr::FieldAccess {
                record: PBox::new(var("p", 140)),
                selector: FieldSelector::ListHead,
            },
            PseudoExpr::IndexAccess {
                collection: PBox::new(var("p", 140)),
                index: 1,
            },
        ]
        .into(),
    };
    let body = PseudoExpr::Let {
        name: "p".to_string(),
        id: Some(VarId::new(140)),
        value: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(var("v_225", 20)),
            selector: FieldSelector::NamedField("fields".to_string()),
        }),
        body: PBox::new(uses),
    };
    let ctx_peel = when(
        ctx_fields(true),
        vec![
            clause(nil_pat(), fail()),
            clause(cons_pat(binder("v_225", 20), binder("t1", 11)), body),
        ],
    );
    let out = run(
        with_rebuild(true, entry(ctx_peel)),
        Some(ScriptVersion::PlutusV3),
    );
    let accesses = field_accesses(&out);
    assert!(
        accesses.iter().any(|a| a == "tx_info.inputs"),
        "`.head` is element 0: {accesses:?}"
    );
    assert!(
        accesses.iter().any(|a| a == "tx_info.reference_inputs"),
        "`[1]` is element 1: {accesses:?}"
    );
    assert!(
        !rendered_binders(&out).iter().any(|n| n == "p"),
        "the payload binding is left holding nothing and goes"
    );
}

/// A combinator whose cell recurses on the HEAD and maps the TAIL is not
/// a map. A free structural scan would accept it.
#[test]
fn rejects_a_combinator_whose_cell_swaps_head_and_tail() {
    let swapped = constr(
        1,
        vec![
            PseudoExpr::Apply {
                function: PBox::new(var("f", 120)),
                args: vec![var("t", 122)].into(),
            },
            PseudoExpr::Apply {
                function: PBox::new(var("walk", 123)),
                args: vec![var("h", 121)].into(),
            },
        ],
    );
    let bad = PseudoExpr::Lambda {
        params: vec![binder("f", 120)],
        body: PBox::new(PseudoExpr::RecFn {
            name: binder("walk", 123),
            params: vec![binder("z", 124)],
            body: PBox::new(when(
                var("z", 124),
                vec![
                    clause(nil_pat(), constr(0, Vec::new())),
                    clause(cons_pat(binder("h", 121), binder("t", 122)), swapped),
                ],
            )),
        }),
    };
    let callback = PseudoExpr::Lambda {
        params: vec![binder("x_31", 130)],
        body: PBox::new(when(
            var("x_31", 130),
            vec![clause(
                WhenPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![binder("field_0", 131)],
                    shape: ConstructorShape::unknown_data(0, 1),
                },
                PseudoExpr::Unit,
            )],
        )),
    };
    let over = || PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("map_fn", 110)),
            args: vec![callback.clone()].into(),
        }),
        args: vec![var("v_800", 800)].into(),
    };
    let expr = with_rebuild(
        true,
        PseudoExpr::Let {
            name: "map_fn".to_string(),
            id: Some(VarId::new(110)),
            value: PBox::new(bad),
            body: PBox::new(entry(ctx_then_tx(over))),
        },
    );
    let out = run(expr, Some(ScriptVersion::PlutusV3));
    assert!(
        !rendered_binders(&out).iter().any(|n| n == "out_ref"),
        "a swapped cell must not be read as a map"
    );
}

/// A named callback's direct calls are evidence about the same
/// parameter. With none, the map alone types it; a call passing
/// something untyped conflicts and takes the type back.
#[test]
fn merges_a_named_callbacks_direct_calls() {
    for with_untyped_call in [false, true] {
        let callback_body = when(
            var("p", 150),
            vec![clause(
                WhenPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![binder("field_0", 151), binder("field_1", 152)],
                    shape: ConstructorShape::unknown_data(0, 2),
                },
                PseudoExpr::Unit,
            )],
        );
        let callback = PseudoExpr::Lambda {
            params: vec![binder("p", 150)],
            body: PBox::new(callback_body),
        };
        let over = move || {
            let mapped = PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(var("map_fn", 110)),
                    args: vec![var("cb", 149)].into(),
                }),
                args: vec![var("v_800", 800)].into(),
            };
            if with_untyped_call {
                PseudoExpr::Apply {
                    function: PBox::new(var("seq", 70)),
                    args: vec![
                        mapped,
                        PseudoExpr::Apply {
                            function: PBox::new(var("cb", 149)),
                            args: vec![var("x", 909)].into(),
                        },
                    ]
                    .into(),
                }
            } else {
                mapped
            }
        };
        let expr = with_map(PseudoExpr::Let {
            name: "cb".to_string(),
            id: Some(VarId::new(149)),
            value: PBox::new(callback),
            body: PBox::new(entry(ctx_then_tx(over))),
        });
        let out = run(expr, Some(ScriptVersion::PlutusV3));
        let names = rendered_binders(&out);
        assert_eq!(
            names.iter().any(|n| n == "out_ref"),
            !with_untyped_call,
            "with_untyped_call={with_untyped_call}: {names:?}"
        );
    }
}
