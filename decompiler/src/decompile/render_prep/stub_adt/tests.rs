use super::*;
use crate::pseudo::ast::{Binder, WhenClause};
use crate::pseudo::constructor::ConstructorShape;

/// Build an unresolved `PseudoExpr::Constr` value (no type_hint,
/// `Unknown` shape) with `arity` field placeholders (Unit).
fn unresolved_constr_expr(tag: usize, arity: usize) -> PseudoExpr {
    PseudoExpr::Constr {
        type_hint: None,
        tag,
        fields: (0..arity).map(|_| PseudoExpr::Unit).collect(),
        shape: ConstructorShape::unknown_data(tag, arity),
    }
}

/// Build an unresolved Constructor pattern.
fn unresolved_constr_pattern(tag: usize, arity: usize) -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag,
        fields: (0..arity)
            .map(|i| Binder::synthetic(format!("f_{i}")))
            .collect(),
        shape: ConstructorShape::unknown_data(tag, arity),
    }
}

fn fresh_var(name: &str) -> (PseudoExpr, VarId) {
    let id = VarId::fresh_binding();
    (PseudoExpr::var_with_id(name, id), id)
}

/// Contract: a pattern-position unresolved `Constr<N>`
/// inside `when X is { ... }` groups under `X`'s `VarId`. The
/// arity-fallback bucket stays empty.
#[test]
fn a1_step1_pattern_inside_when_var_subject_groups_by_scrutinee() {
    let (var_expr, vid) = fresh_var("x");
    let expr = PseudoExpr::When {
        subject: PBox::new(var_expr),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: unresolved_constr_pattern(0, 0),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: unresolved_constr_pattern(1, 2),
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let groups = collect_unresolved_constr_shapes(&expr);
    assert_eq!(groups.by_scrutinee.len(), 1);
    assert_eq!(
        groups.by_scrutinee[&vid],
        BTreeSet::from([
            StubVariant { tag: 0, arity: 0 },
            StubVariant { tag: 1, arity: 2 }
        ])
    );
    assert!(groups.by_arity.is_empty());
}

/// Contract: an expression-position `Constr<N>(...)`
/// outside any `When` block drops into the arity-fallback bucket.
#[test]
fn a1_step1_expression_position_falls_back_to_arity_bucket() {
    let expr = unresolved_constr_expr(2, 3);
    let groups = collect_unresolved_constr_shapes(&expr);
    assert!(groups.by_scrutinee.is_empty());
    assert_eq!(
        groups.by_arity[&3],
        BTreeSet::from([StubVariant { tag: 2, arity: 3 }])
    );
}

/// Contract: complex `When` subjects (non-Var) have no
/// stable scrutinee identity, so their patterns drop into
/// the arity bucket.
#[test]
fn a1_step1_non_var_subject_drops_patterns_to_arity_bucket() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var_with_id("y", VarId::fresh_binding())),
            selector: crate::pseudo::field_selector::FieldSelector::PairFst,
        }),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: unresolved_constr_pattern(0, 1),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };
    let groups = collect_unresolved_constr_shapes(&expr);
    assert!(groups.by_scrutinee.is_empty());
    assert_eq!(
        groups.by_arity[&1],
        BTreeSet::from([StubVariant { tag: 0, arity: 1 }])
    );
}

/// Contract: when the same Var `x` is the subject of two
/// separate `when` blocks (e.g. re-matched after a branch),
/// both groups merge into one class under `x`'s `VarId`.
#[test]
fn a1_step1_same_var_subject_across_whens_merges_into_one_class() {
    let (var_a, vid_a) = fresh_var("x");
    let (var_b, _vid_b) = (
        PseudoExpr::var_with_id("x", vid_a), // SAME VarId — different syntactic occurrences of `x`.
        vid_a,
    );
    let inner_when_b = PseudoExpr::When {
        subject: PBox::new(var_b),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: unresolved_constr_pattern(1, 0),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(var_a),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: unresolved_constr_pattern(0, 0),
            guard: None,
            body: inner_when_b,
        }],
    };
    let groups = collect_unresolved_constr_shapes(&expr);
    assert_eq!(groups.by_scrutinee.len(), 1);
    assert_eq!(
        groups.by_scrutinee[&vid_a],
        BTreeSet::from([
            StubVariant { tag: 0, arity: 0 },
            StubVariant { tag: 1, arity: 0 }
        ])
    );
}

/// Contract: a constructor that already has a `type_hint` set
/// (the blueprint resolved it) MUST NOT be flagged as
/// unresolved, even when it carries an `Unknown` shape.
#[test]
fn a1_step1_constructor_with_existing_type_hint_skipped() {
    let hint = crate::decompile::TypeHintId::new("UserAdt");
    let expr = PseudoExpr::Constr {
        type_hint: Some(hint),
        tag: 0,
        fields: vec![].into(),
        shape: ConstructorShape::unknown_data(0, 0),
    };
    let groups = collect_unresolved_constr_shapes(&expr);
    assert!(groups.is_empty());
}

/// Contract: a known constructor shape (e.g.,
/// `Some`/`None` / `True`/`False`) MUST NOT be stubbed — only
/// `ConstructorShape::Unknown` qualifies.
#[test]
fn a1_step1_known_shape_is_not_stubbed() {
    let known_some = PseudoExpr::Constr {
        type_hint: None,
        tag: 0,
        fields: vec![PseudoExpr::Unit].into(),
        shape: ConstructorShape::Known(crate::pseudo::constructor::KnownConstructor::Some),
    };
    let groups = collect_unresolved_constr_shapes(&known_some);
    assert!(
        groups.is_empty(),
        "Known(Some) must not be stubbed; groups = {groups:?}"
    );
}

/// `WhenPattern::Literal` carries an arbitrary `PseudoExpr` —
/// including unresolved `Constr` literals like
/// `when X is { Constr<3> -> ... }` where the constructor IS the
/// literal pattern. The collector must recurse into it.
#[test]
fn a1_step1_literal_pattern_with_inner_constr_recurses() {
    let (var_expr, vid) = fresh_var("x");
    // when x is { (Constr<5>) -> ... } — the Constr is a Literal pattern.
    let expr = PseudoExpr::When {
        subject: PBox::new(var_expr),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Literal(unresolved_constr_expr(5, 1)),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };
    let groups = collect_unresolved_constr_shapes(&expr);
    assert_eq!(
        groups.by_scrutinee[&vid],
        BTreeSet::from([StubVariant { tag: 5, arity: 1 }]),
        "Literal-position Constr must surface in scrutinee group; \
         groups = {groups:?}"
    );
}

/// Def-use refinement: aliased subjects like
/// `let y = x; when y is { … }` merge with other `when`s on
/// `x` via the alias map (`y → x`), yielding a single merged
/// stub class instead of two.
#[test]
fn a1_def_use_aliased_subject_merges_with_canonical() {
    let (x_expr, x_id) = fresh_var("x");
    let y_id = VarId::fresh_binding();
    // when x is { Constr<0>(...) -> ... }
    let outer_when = PseudoExpr::When {
        subject: PBox::new(x_expr.clone()),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: unresolved_constr_pattern(0, 1),
            guard: None,
            body: PseudoExpr::let_bind_with_id(
                "y",
                y_id,
                x_expr.clone(),
                // when y is { Constr<1>(...) -> ... }
                PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var_with_id("y", y_id)),
                    subject_name: None,
                    clauses: vec![WhenClause {
                        pattern: unresolved_constr_pattern(1, 0),
                        guard: None,
                        body: PseudoExpr::Unit,
                    }],
                },
            ),
        }],
    };
    let groups = collect_unresolved_constr_shapes(&outer_when);
    assert_eq!(
        groups.by_scrutinee.len(),
        1,
        "Aliased subject must merge with canonical class; \
         groups = {groups:?}"
    );
    assert_eq!(
        groups.by_scrutinee[&x_id],
        BTreeSet::from([
            StubVariant { tag: 0, arity: 1 },
            StubVariant { tag: 1, arity: 0 },
        ]),
        "Both pattern-position constructors must group under \
         x's canonical class"
    );
    assert!(
        !groups.by_scrutinee.contains_key(&y_id),
        "y's stub class should be absorbed into x's canonical class"
    );
}

/// Def-use refinement: a value-position `Constr<N>` bound by
/// `let X = Constr<N>(...)` and then scrutinized by `when X`
/// attributes to `X`'s scrutinee class, not the arity-fallback
/// bucket — so pattern and value position share one stub.
#[test]
fn a1_def_use_let_bound_value_position_attributes_to_scrutinee() {
    let x_id = VarId::fresh_binding();
    // let x = Constr<7>(unit); when x is { Constr<7>(_) -> unit }
    let expr = PseudoExpr::let_bind_with_id(
        "x",
        x_id,
        unresolved_constr_expr(7, 1),
        PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("x", x_id)),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: unresolved_constr_pattern(7, 1),
                guard: None,
                body: PseudoExpr::Unit,
            }],
        },
    );
    let groups = collect_unresolved_constr_shapes(&expr);
    assert_eq!(
        groups.by_scrutinee[&x_id],
        BTreeSet::from([StubVariant { tag: 7, arity: 1 }]),
        "Pattern-position AND value-position Constr<7> must \
         merge under x's scrutinee class"
    );
    assert!(
        !groups.by_arity.contains_key(&1),
        "Arity bucket must be empty — let-bound value-position \
         Constr promoted to scrutinee class. groups = {groups:?}"
    );
}

/// Def-use refinement: a value-position `Constr<N>` in
/// `let X = Constr<N>(...)` where `X` is NEVER scrutinized falls
/// back to the arity bucket.
#[test]
fn a1_def_use_let_bound_value_falls_back_when_not_scrutinized() {
    let x_id = VarId::fresh_binding();
    // let x = Constr<7>(unit); x — never scrutinized
    let expr = PseudoExpr::let_bind_with_id(
        "x",
        x_id,
        unresolved_constr_expr(7, 1),
        PseudoExpr::var_with_id("x", x_id),
    );
    let groups = collect_unresolved_constr_shapes(&expr);
    assert!(
        !groups.by_scrutinee.contains_key(&x_id),
        "x has no scrutinee class — never scrutinized"
    );
    assert_eq!(
        groups.by_arity[&1],
        BTreeSet::from([StubVariant { tag: 7, arity: 1 }]),
        "Non-scrutinized let-value Constr falls back to arity bucket"
    );
}

/// Def-use refinement: transitive alias chain
/// (`let Z = Y; let Y = X; when Z is ...`) resolves to X.
#[test]
fn a1_def_use_transitive_alias_chain_resolves_to_canonical() {
    let (x_expr, x_id) = fresh_var("x");
    let y_id = VarId::fresh_binding();
    let z_id = VarId::fresh_binding();
    // let y = x in let z = y in when z is { Constr<3>(_) -> Unit }
    let expr = PseudoExpr::let_bind_with_id(
        "y",
        y_id,
        x_expr,
        PseudoExpr::let_bind_with_id(
            "z",
            z_id,
            PseudoExpr::var_with_id("y", y_id),
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var_with_id("z", z_id)),
                subject_name: None,
                clauses: vec![WhenClause {
                    pattern: unresolved_constr_pattern(3, 0),
                    guard: None,
                    body: PseudoExpr::Unit,
                }],
            },
        ),
    );
    let groups = collect_unresolved_constr_shapes(&expr);
    assert_eq!(groups.by_scrutinee.len(), 1);
    assert_eq!(
        groups.by_scrutinee[&x_id],
        BTreeSet::from([StubVariant { tag: 3, arity: 0 }]),
        "Transitive alias chain z → y → x resolves to x"
    );
    assert!(!groups.by_scrutinee.contains_key(&z_id));
    assert!(!groups.by_scrutinee.contains_key(&y_id));
}

/// The REWRITE path canonicalizes aliased When subjects so the
/// pattern-position Constr in `let Y = X; when Y is { Constr<N>
/// -> ... }` gets X's scrutinee class type-hint (not raw).
#[test]
fn a1_def_use_rewrite_canonicalizes_aliased_subject_pattern() {
    let (x_expr, x_id) = fresh_var("x");
    let y_id = VarId::fresh_binding();
    // when x is { Constr<0> -> let y = x in when y is { Constr<1> -> Unit } }
    let expr = PseudoExpr::When {
        subject: PBox::new(x_expr.clone()),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: unresolved_constr_pattern(0, 0),
            guard: None,
            body: PseudoExpr::let_bind_with_id(
                "y",
                y_id,
                x_expr,
                PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var_with_id("y", y_id)),
                    subject_name: None,
                    clauses: vec![WhenClause {
                        pattern: unresolved_constr_pattern(1, 0),
                        guard: None,
                        body: PseudoExpr::Unit,
                    }],
                },
            ),
        }],
    };
    let groups = collect_unresolved_constr_shapes(&expr);
    let ordinals = assign_class_ordinals(&groups);
    let mut registry = BlueprintHintRegistry::new();
    let names = register_stub_adts_in_registry(&groups, &ordinals, &mut registry);
    let rewritten = rewrite_unresolved_constrs(expr, &names);

    // Walk the rewritten AST: both Constructor patterns must
    // carry x's class's type hint.
    let expected_hint = names.by_scrutinee[&x_id].shards[&0].type_hint.clone();
    let mut patterns_seen = 0;
    fn walk(e: &PseudoExpr, expected: &TypeHintId, seen: &mut usize) {
        match e {
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                walk(subject, expected, seen);
                for c in clauses {
                    if let WhenPattern::Constructor { type_hint, .. } = &c.pattern {
                        assert_eq!(
                            type_hint.as_ref(),
                            Some(expected),
                            "aliased subject pattern must get canonical class hint"
                        );
                        *seen += 1;
                    }
                    walk(&c.body, expected, seen);
                }
            }
            PseudoExpr::Let { value, body, .. } => {
                walk(value, expected, seen);
                walk(body, expected, seen);
            }
            _ => {}
        }
    }
    walk(&rewritten, &expected_hint, &mut patterns_seen);
    assert_eq!(patterns_seen, 2, "both patterns must have been visited");
}

/// Def-use: a Literal pattern wrapping a `Constr` (`when X is
/// { Constr<0> -> ...}` through the literal-pattern path) must
/// get the scrutinee class's type-hint, not raw `Constr<N>` —
/// the general expression rewriter checks only `by_arity`.
#[test]
fn a1_def_use_rewrite_literal_pattern_constr_gets_scrutinee_hint() {
    let (x_expr, x_id) = fresh_var("x");
    // when x is { Literal(Constr<5>(unit)) -> Unit }
    let expr = PseudoExpr::When {
        subject: PBox::new(x_expr),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Literal(unresolved_constr_expr(5, 1)),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };
    let groups = collect_unresolved_constr_shapes(&expr);
    let ordinals = assign_class_ordinals(&groups);
    let mut registry = BlueprintHintRegistry::new();
    let names = register_stub_adts_in_registry(&groups, &ordinals, &mut registry);
    let expected_hint = names.by_scrutinee[&x_id].shards[&1].type_hint.clone();
    let rewritten = rewrite_unresolved_constrs(expr, &names);

    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!("expected When");
    };
    let WhenPattern::Literal(inner) = &clauses[0].pattern else {
        panic!("expected Literal pattern");
    };
    match inner {
        PseudoExpr::Constr { type_hint, .. } => {
            assert_eq!(
                type_hint.clone(),
                Some(expected_hint),
                "Literal-pattern Constr must get canonical scrutinee class hint"
            );
        }
        other => panic!("expected Constr inside Literal, got {other:?}"),
    }
}

/// The REWRITE path attributes a let-bound value-position
/// Constr to the scrutinee class's type-hint (not the arity
/// bucket).
#[test]
fn a1_def_use_rewrite_let_value_constr_gets_scrutinee_hint() {
    let x_id = VarId::fresh_binding();
    // let x = Constr<7>(unit); when x is { Constr<7>(_) -> Unit }
    let expr = PseudoExpr::let_bind_with_id(
        "x",
        x_id,
        unresolved_constr_expr(7, 1),
        PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("x", x_id)),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: unresolved_constr_pattern(7, 1),
                guard: None,
                body: PseudoExpr::Unit,
            }],
        },
    );
    let groups = collect_unresolved_constr_shapes(&expr);
    let ordinals = assign_class_ordinals(&groups);
    let mut registry = BlueprintHintRegistry::new();
    let names = register_stub_adts_in_registry(&groups, &ordinals, &mut registry);
    let expected_hint = names.by_scrutinee[&x_id].shards[&1].type_hint.clone();
    let rewritten = rewrite_unresolved_constrs(expr, &names);

    // The Let value's Constr must have x's class hint, not None
    // (which would leave a raw `Constr<7>`).
    let PseudoExpr::Let { value, .. } = rewritten else {
        panic!("expected Let");
    };
    match value.into_inner() {
        PseudoExpr::Constr { type_hint, .. } => {
            assert_eq!(
                type_hint,
                Some(expected_hint),
                "let-value Constr must get canonical scrutinee class hint"
            );
        }
        other => panic!("expected Constr, got {other:?}"),
    }
}

/// Contract: `register_stub_adts_in_registry` mints the synthetic
/// type hints, registers every variant, and returns the name map.
/// The renderer's resolve chain then maps `Constr<N>` →
/// `Unknown_S_<ord>_<N>` once the AST rewrite sets the `type_hint`.
#[test]
fn a1_step2_registers_scrutinee_stub_adt_in_registry() {
    let (var_expr, vid) = fresh_var("x");
    let expr = PseudoExpr::When {
        subject: PBox::new(var_expr),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: unresolved_constr_pattern(0, 0),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: unresolved_constr_pattern(1, 2),
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let groups = collect_unresolved_constr_shapes(&expr);
    let ordinals = assign_class_ordinals(&groups);
    let mut registry = BlueprintHintRegistry::new();
    let names = register_stub_adts_in_registry(&groups, &ordinals, &mut registry);

    let class = &names.by_scrutinee[&vid];
    // Under conflict-only sharding: variants
    // {tag 0, arity 0} + {tag 1, arity 2} share distinct tags,
    // so there's no registry conflict — emit ONE ADT covering
    // both, named `Unknown_S_1` (no `_A<arity>` suffix). Both
    // shard-map keys point at the same `StubAdtTypeNames`.
    let shard_0 = &class.shards[&0];
    let shard_2 = &class.shards[&2];
    assert_eq!(shard_0.type_name, "Unknown_S_1");
    assert_eq!(shard_2.type_name, "Unknown_S_1");
    assert_eq!(shard_0.type_hint, shard_2.type_hint);
    assert_eq!(
        shard_0.variant_names[&StubVariant { tag: 0, arity: 0 }],
        "Unknown_S_1_0"
    );
    assert_eq!(
        shard_0.variant_names[&StubVariant { tag: 1, arity: 2 }],
        "Unknown_S_1_1"
    );

    let resolved_0 = registry.resolve(
        ConstructorShape::unknown_data(0, 0),
        Some(&shard_0.type_hint),
    );
    assert_eq!(resolved_0.as_deref(), Some("Unknown_S_1_0"));
    let resolved_1 = registry.resolve(
        ConstructorShape::unknown_data(1, 2),
        Some(&shard_0.type_hint),
    );
    assert_eq!(resolved_1.as_deref(), Some("Unknown_S_1_1"));
}

/// Contract: arity-fallback bucket names use the
/// `Unknown_E_<arity>` prefix; both scrutinee-class and arity
/// stubs share the registry, no conflict.
#[test]
fn a1_step2_registers_arity_fallback_stub_adt_alongside_scrutinee() {
    let (var_expr, vid) = fresh_var("x");
    let expr = PseudoExpr::When {
        subject: PBox::new(var_expr),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: unresolved_constr_pattern(0, 0),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };
    // Plus a stand-alone expression-position Constr<3>(unit) outside any When.
    let outer = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("f", VarId::fresh_binding())),
        args: vec![expr, unresolved_constr_expr(3, 1)].into(),
    };
    let groups = collect_unresolved_constr_shapes(&outer);
    let ordinals = assign_class_ordinals(&groups);
    let mut registry = BlueprintHintRegistry::new();
    let names = register_stub_adts_in_registry(&groups, &ordinals, &mut registry);

    // Scrutinee class has one variant {tag 0, arity 0} — no
    // conflict, so `Unknown_S_1` (conflict-only sharding).
    assert!(names.by_scrutinee.contains_key(&vid));
    assert_eq!(names.by_scrutinee[&vid].shards[&0].type_name, "Unknown_S_1");
    assert!(names.by_arity.contains_key(&1));
    assert_eq!(names.by_arity[&1].type_name, "Unknown_E_1");
    let bucket_resolve = registry.resolve(
        ConstructorShape::unknown_data(3, 1),
        Some(&names.by_arity[&1].type_hint),
    );
    assert_eq!(bucket_resolve.as_deref(), Some("Unknown_E_1_3"));
}

/// Contract: minting and registration are deterministic —
/// running the function twice on the same input produces the
/// same names.
#[test]
fn a1_step2_deterministic_names_across_runs() {
    let (var_expr, _vid) = fresh_var("x");
    let expr = PseudoExpr::When {
        subject: PBox::new(var_expr),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: unresolved_constr_pattern(2, 1),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };
    let groups = collect_unresolved_constr_shapes(&expr);
    let ordinals = assign_class_ordinals(&groups);

    let mut reg1 = BlueprintHintRegistry::new();
    let names1 = register_stub_adts_in_registry(&groups, &ordinals, &mut reg1);
    let mut reg2 = BlueprintHintRegistry::new();
    let names2 = register_stub_adts_in_registry(&groups, &ordinals, &mut reg2);
    assert_eq!(
        names1, names2,
        "names must be deterministic; got {names1:?} vs {names2:?}"
    );
}

/// Contract: `rewrite_unresolved_constrs` attaches the
/// synthetic `type_hint` to each unresolved `Constr` AST node.
/// Pattern-position `Constructor`s pick the scrutinee class's
/// hint; expression-position `Constr`s pick the arity bucket's
/// hint.
#[test]
fn a1_step3_attaches_type_hint_to_pattern_constructor() {
    let (var_expr, vid) = fresh_var("x");
    let expr = PseudoExpr::When {
        subject: PBox::new(var_expr),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: unresolved_constr_pattern(2, 1),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };
    let groups = collect_unresolved_constr_shapes(&expr);
    let ordinals = assign_class_ordinals(&groups);
    let mut registry = BlueprintHintRegistry::new();
    let names = register_stub_adts_in_registry(&groups, &ordinals, &mut registry);
    let rewritten = rewrite_unresolved_constrs(expr, &names);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!("expected When at top level");
    };
    let WhenPattern::Constructor { type_hint, .. } = &clauses[0].pattern else {
        panic!("expected Constructor pattern in first clause");
    };
    // Constructor pattern { tag: 2, arity: 1 } resolves via
    // the arity-1 shard key.
    let expected_hint = &names.by_scrutinee[&vid].shards[&1].type_hint;
    assert_eq!(
        type_hint.as_ref(),
        Some(expected_hint),
        "Constructor pattern must carry the scrutinee class's arity-shard TypeHintId after rewrite"
    );
}

/// Contract: expression-position `Constr` gets the
/// arity bucket's TypeHintId attached.
#[test]
fn a1_step3_attaches_type_hint_to_expression_constr_via_arity_bucket() {
    let expr = unresolved_constr_expr(7, 2);
    let groups = collect_unresolved_constr_shapes(&expr);
    let ordinals = assign_class_ordinals(&groups);
    let mut registry = BlueprintHintRegistry::new();
    let names = register_stub_adts_in_registry(&groups, &ordinals, &mut registry);
    let rewritten = rewrite_unresolved_constrs(expr, &names);
    let PseudoExpr::Constr { type_hint, .. } = rewritten else {
        panic!("expected Constr at top level");
    };
    let expected_hint = &names.by_arity[&2].type_hint;
    assert_eq!(
        type_hint.as_ref(),
        Some(expected_hint),
        "expression-position Constr must carry arity bucket's TypeHintId"
    );
}

/// Contract: an existing type_hint is preserved (Known
/// constructors or already-resolved shapes are not overwritten).
#[test]
fn a1_step3_preserves_existing_type_hint() {
    let pre_existing_hint = TypeHintId::new("UserAdt");
    let expr = PseudoExpr::Constr {
        type_hint: Some(pre_existing_hint.clone()),
        tag: 0,
        fields: vec![].into(),
        shape: ConstructorShape::unknown_data(0, 0),
    };
    let groups = collect_unresolved_constr_shapes(&expr); // empty — type_hint set
    let ordinals = assign_class_ordinals(&groups);
    let mut registry = BlueprintHintRegistry::new();
    let names = register_stub_adts_in_registry(&groups, &ordinals, &mut registry);
    let rewritten = rewrite_unresolved_constrs(expr, &names);
    let PseudoExpr::Constr { type_hint, .. } = rewritten else {
        panic!("expected Constr");
    };
    assert_eq!(
        type_hint,
        Some(pre_existing_hint),
        "pre-existing type_hint must be preserved"
    );
}

/// Contract: `format_stub_adt_prefix` produces
/// deterministic, surface `pub type ... { ... }` blocks
/// covering both scrutinee classes and arity fallback buckets.
#[test]
fn a1_step4a_format_prefix_emits_both_scrutinee_and_arity_blocks() {
    let (var_expr, _vid) = fresh_var("x");
    let when_expr = PseudoExpr::When {
        subject: PBox::new(var_expr),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: unresolved_constr_pattern(0, 0),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: unresolved_constr_pattern(1, 2),
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let outer = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("f", VarId::fresh_binding())),
        args: vec![when_expr, unresolved_constr_expr(5, 1)].into(),
    };
    let groups = collect_unresolved_constr_shapes(&outer);
    let ordinals = assign_class_ordinals(&groups);
    let mut registry = BlueprintHintRegistry::new();
    let names = register_stub_adts_in_registry(&groups, &ordinals, &mut registry);
    let prefix = format_stub_adt_prefix(&names);

    // Scrutinee class block — conflict-only sharding: tags 0
    // and 1 differ, so no registry conflict and ONE ADT covers
    // both variants despite the arity difference (0 vs 2).
    assert!(
        prefix.contains("pub type Unknown_S_1 {"),
        "missing scrutinee class single ADT; got:\n{prefix}"
    );
    assert!(
        prefix.contains("  Unknown_S_1_0\n"),
        "tag-0 nullary variant must render without parens; got:\n{prefix}"
    );
    assert!(
        prefix.contains("  Unknown_S_1_1(Data, Data)\n"),
        "tag-1 arity-2 variant must render with `(Data, Data)`; got:\n{prefix}"
    );

    assert!(
        prefix.contains("pub type Unknown_E_1 {"),
        "missing arity bucket block; got:\n{prefix}"
    );
    // Single-variant ADTs render in compact one-line form
    // (`pub type X { X_5(Data) }`); multi-variant in vertical form
    // (`  X_5(Data)\n`). Either way the `(Data)` payload must be
    // present.
    assert!(
        prefix.contains("Unknown_E_1_5(Data)"),
        "tag-5 arity-1 variant must render with `(Data)`; got:\n{prefix}"
    );
}

/// A tag observed at multiple collection arities is NOT sharded
/// into `Unknown_S_<ord>_A<arity>` types — that would split one
/// Scott value's `when` across several declared types, invalid
/// surface. The multi-arity observation is an overflow-expansion
/// artifact and the registry lookup is arity-agnostic, so one
/// `Unknown_S_<ord>` covers all of them, with the field count
/// reconciled to a uniform arity by `reconcile_declared_arities`.
#[test]
fn a1_same_tag_multiple_arities_emits_single_unsharded_type() {
    let (var_expr, vid) = fresh_var("x");
    let expr = PseudoExpr::When {
        subject: PBox::new(var_expr),
        subject_name: None,
        clauses: vec![
            // Same tag (0) at DIFFERENT collection arities.
            WhenClause {
                pattern: unresolved_constr_pattern(0, 0),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: unresolved_constr_pattern(0, 1),
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let groups = collect_unresolved_constr_shapes(&expr);
    let ordinals = assign_class_ordinals(&groups);
    let mut registry = BlueprintHintRegistry::new();
    let names = register_stub_adts_in_registry(&groups, &ordinals, &mut registry);
    let class = &names.by_scrutinee[&vid];
    let shard_0 = &class.shards[&0];
    let shard_1 = &class.shards[&1];
    assert_eq!(shard_0.type_name, "Unknown_S_1");
    assert_eq!(shard_1.type_name, "Unknown_S_1");
    assert_eq!(shard_0.type_hint, shard_1.type_hint);
    assert_eq!(
        shard_0.variant_names[&StubVariant { tag: 0, arity: 0 }],
        "Unknown_S_1_0"
    );
    assert_eq!(
        shard_0.variant_names[&StubVariant { tag: 0, arity: 1 }],
        "Unknown_S_1_0"
    );
}

/// When a class has NO tag-arity conflict (all tag-arity pairs
/// are unique), no sharding fires. One ADT covers all variants,
/// like a real ADT with mixed arities at distinct tags.
#[test]
fn a1_conflict_only_no_sharding_when_no_real_conflict() {
    let (var_expr, vid) = fresh_var("x");
    let expr = PseudoExpr::When {
        subject: PBox::new(var_expr),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: unresolved_constr_pattern(0, 0),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: unresolved_constr_pattern(1, 1),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: unresolved_constr_pattern(2, 3),
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let groups = collect_unresolved_constr_shapes(&expr);
    let ordinals = assign_class_ordinals(&groups);
    let mut registry = BlueprintHintRegistry::new();
    let names = register_stub_adts_in_registry(&groups, &ordinals, &mut registry);
    let class = &names.by_scrutinee[&vid];
    let shard_0 = &class.shards[&0];
    let shard_1 = &class.shards[&1];
    let shard_3 = &class.shards[&3];
    assert_eq!(shard_0.type_name, "Unknown_S_1");
    assert_eq!(shard_1.type_name, "Unknown_S_1");
    assert_eq!(shard_3.type_name, "Unknown_S_1");
    assert_eq!(shard_0.type_hint, shard_1.type_hint);
    assert_eq!(shard_1.type_hint, shard_3.type_hint);
    // Prefix emits exactly ONE block (dedup-by-hint).
    let prefix = format_stub_adt_prefix(&names);
    let block_count = prefix.matches("pub type Unknown_S_1 {").count();
    assert_eq!(
        block_count, 1,
        "single ADT emitted exactly once; got:\n{prefix}"
    );
    assert!(prefix.contains("  Unknown_S_1_0\n"));
    assert!(prefix.contains("  Unknown_S_1_1(Data)\n"));
    assert!(prefix.contains("  Unknown_S_1_2(Data, Data, Data)\n"));
}

/// Contract: empty groups → empty prefix string.
#[test]
fn a1_step4a_empty_groups_produces_empty_prefix() {
    let names = StubAdtNames {
        by_scrutinee: BTreeMap::new(),
        by_arity: BTreeMap::new(),
    };
    let prefix = format_stub_adt_prefix(&names);
    assert!(prefix.is_empty());
}

/// Contract: end-to-end happy path. Two unresolved
/// Constrs in a When → after rewrite, both carry the same
/// scrutinee class's TypeHintId.
#[test]
fn a1_step3_end_to_end_two_clause_when_resolves_to_same_class() {
    let (var_expr, vid) = fresh_var("x");
    let expr = PseudoExpr::When {
        subject: PBox::new(var_expr),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: unresolved_constr_pattern(0, 0),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: unresolved_constr_pattern(1, 1),
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let groups = collect_unresolved_constr_shapes(&expr);
    let ordinals = assign_class_ordinals(&groups);
    let mut registry = BlueprintHintRegistry::new();
    let names = register_stub_adts_in_registry(&groups, &ordinals, &mut registry);
    let rewritten = rewrite_unresolved_constrs(expr, &names);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!("expected When");
    };
    let hint_0 = match &clauses[0].pattern {
        WhenPattern::Constructor { type_hint, .. } => type_hint.clone(),
        _ => panic!(),
    };
    let hint_1 = match &clauses[1].pattern {
        WhenPattern::Constructor { type_hint, .. } => type_hint.clone(),
        _ => panic!(),
    };
    // Conflict-only sharding: the two tags are DISTINCT —
    // no registry conflict — one `Unknown_S_1` ADT and one
    // shared TypeHintId for both clauses.
    let expected = Some(names.by_scrutinee[&vid].shards[&0].type_hint.clone());
    assert_eq!(hint_0, expected);
    assert_eq!(hint_1, expected);
    assert_eq!(hint_0, hint_1, "no-conflict class shares one TypeHintId");
}

/// Contract: `assign_class_ordinals` produces stable
/// 1-indexed ordinals regardless of the raw `VarId` values used
/// internally. Two scrutinee classes → ordinals 1 and 2 in
/// `BTreeMap` order (sorted by VarId).
#[test]
fn a1_step1_assign_class_ordinals_is_stable_and_one_indexed() {
    let mut groups = StubAdtGroups::default();
    let vid_smaller = VarId::fresh_binding();
    let vid_bigger = VarId::fresh_binding();
    // Insert in reverse order to verify BTreeMap sorts ascending.
    groups.by_scrutinee.insert(
        vid_bigger,
        BTreeSet::from([StubVariant { tag: 0, arity: 0 }]),
    );
    groups.by_scrutinee.insert(
        vid_smaller,
        BTreeSet::from([StubVariant { tag: 0, arity: 0 }]),
    );

    let ordinals = assign_class_ordinals(&groups);
    assert_eq!(ordinals[&vid_smaller], 1);
    assert_eq!(ordinals[&vid_bigger], 2);
}
