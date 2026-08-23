use super::*;

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// Wrap a tree in the `decompiled` marker let so G0 passes.
fn with_marker(body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "decompiled".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("ctx".to_string(), VarId::new(2))],
            body: PBox::new(body),
        }),
        body: PBox::new(varref("decompiled", 1)),
    }
}

/// `let rhs_origin = 1; <body>` — gives the RHS var a known binder kind.
fn with_rhs_origin(name: &str, id: u32, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: name.to_string(),
        id: Some(VarId::new(id)),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(body),
    }
}

fn alias_let(name: &str, aid: u32, rhs: PseudoExpr, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: name.to_string(),
        id: Some(VarId::new(aid)),
        value: PBox::new(rhs),
        body: PBox::new(body),
    }
}

/// `let w = 1; let p10 = w; f(p10)` -> `let w = 1; f(w)`.
#[test]
fn fires_on_single_use_alias() {
    let input = with_marker(with_rhs_origin(
        "w",
        10,
        alias_let(
            "p10",
            20,
            varref("w", 10),
            PseudoExpr::Apply {
                function: PBox::new(varref("f", 30)),
                args: vec![varref("p10", 20)].into(),
            },
        ),
    ));
    let out = copy_propagate_var_aliases(input);
    let expected = with_marker(with_rhs_origin(
        "w",
        10,
        PseudoExpr::Apply {
            function: PBox::new(varref("f", 30)),
            args: vec![varref("w", 10)].into(),
        },
    ));
    assert_eq!(out, expected);
}

/// Two uses keep the alias when its name is not the synthetic CSE
/// `w`-family (G5) — a deliberate rename or annotation carrier.
#[test]
fn veto_multi_use_non_w_family() {
    let input = with_marker(with_rhs_origin(
        "src",
        10,
        alias_let(
            "p10",
            20,
            varref("src", 10),
            PseudoExpr::Apply {
                function: PBox::new(varref("p10", 20)),
                args: vec![varref("p10", 20)].into(),
            },
        ),
    ));
    let out = copy_propagate_var_aliases(input.clone());
    assert_eq!(out, input);
}

/// The CSE scope-overlap residue `let w_2 = w; … w_2 … w_2 …` folds:
/// every use rewired to `w`, alias dropped (G5 w-family multi-use).
#[test]
fn folds_multi_use_w_family_alias() {
    let input = with_marker(with_rhs_origin(
        "w",
        10,
        alias_let(
            "w_2",
            20,
            varref("w", 10),
            PseudoExpr::Apply {
                function: PBox::new(varref("f", 30)),
                args: vec![varref("w_2", 20), varref("w_2", 20)].into(),
            },
        ),
    ));
    let out = copy_propagate_var_aliases(input);
    let expected = with_marker(with_rhs_origin(
        "w",
        10,
        PseudoExpr::Apply {
            function: PBox::new(varref("f", 30)),
            args: vec![varref("w", 10), varref("w", 10)].into(),
        },
    ));
    assert_eq!(out, expected);
}

/// Multi-use w-family alias where ONE use sits under a binder that
/// renders like the RHS — the whole fold is vetoed (G4 must hold at
/// EVERY use, not just the first).
#[test]
fn veto_multi_use_when_any_use_captured() {
    let input = with_marker(with_rhs_origin(
        "w",
        10,
        alias_let(
            "w_2",
            20,
            varref("w", 10),
            PseudoExpr::Apply {
                function: PBox::new(varref("f", 30)),
                args: vec![
                    varref("w_2", 20),
                    PseudoExpr::Lambda {
                        params: vec![Binder::new("w".to_string(), VarId::new(40))],
                        body: PBox::new(varref("w_2", 20)),
                    },
                ]
                .into(),
            },
        ),
    ));
    let out = copy_propagate_var_aliases(input.clone());
    assert_eq!(out, input);
}

/// `is_synthetic_w_family` accepts exactly the CSE mint + suffix forms.
#[test]
fn w_family_name_predicate() {
    assert!(is_synthetic_w_family("w"));
    assert!(is_synthetic_w_family("w_2"));
    assert!(is_synthetic_w_family("w_10_3"));
    assert!(!is_synthetic_w_family("w2"));
    assert!(!is_synthetic_w_family("wx"));
    assert!(!is_synthetic_w_family("w_"));
    assert!(!is_synthetic_w_family("w_a"));
    assert!(!is_synthetic_w_family("ww_2"));
    assert!(!is_synthetic_w_family("src"));
}

/// A binder named like the RHS between the alias and the use would
/// print-capture the moved reference — vetoed.
#[test]
fn veto_print_capture_on_path() {
    let input = with_marker(with_rhs_origin(
        "w",
        10,
        alias_let(
            "p10",
            20,
            varref("w", 10),
            PseudoExpr::Lambda {
                params: vec![Binder::new("w".to_string(), VarId::new(40))],
                body: PBox::new(varref("p10", 20)),
            },
        ),
    ));
    let out = copy_propagate_var_aliases(input.clone());
    assert_eq!(out, input);
}

/// An id-less RHS is not a candidate (G1).
#[test]
fn veto_idless_rhs() {
    let input = with_marker(with_rhs_origin(
        "w",
        10,
        alias_let(
            "p10",
            20,
            PseudoExpr::var("w"),
            PseudoExpr::Apply {
                function: PBox::new(varref("f", 30)),
                args: vec![varref("p10", 20)].into(),
            },
        ),
    ));
    let out = copy_propagate_var_aliases(input.clone());
    assert_eq!(out, input);
}

/// A second name-only compat reference (`Var { id: None }`) keeps the
/// alias — dropping the let would orphan it (G3 dual key).
#[test]
fn veto_name_only_compat_ref() {
    let input = with_marker(with_rhs_origin(
        "w",
        10,
        alias_let(
            "p10",
            20,
            varref("w", 10),
            PseudoExpr::Apply {
                function: PBox::new(varref("p10", 20)),
                args: vec![PseudoExpr::var("p10")].into(),
            },
        ),
    ));
    let out = copy_propagate_var_aliases(input.clone());
    assert_eq!(out, input);
}

/// An alias to a RecFn NAME binder is never propagated (G2).
#[test]
fn veto_recfn_name_rhs() {
    let recfn = PseudoExpr::RecFn {
        name: Binder::new("self_fn".to_string(), VarId::new(50)),
        params: vec![Binder::new("x".to_string(), VarId::new(51))],
        body: PBox::new(alias_let(
            "a",
            20,
            varref("self_fn", 50),
            PseudoExpr::Apply {
                function: PBox::new(varref("a", 20)),
                args: vec![varref("x", 51)].into(),
            },
        )),
    };
    let input = with_marker(recfn);
    let out = copy_propagate_var_aliases(input.clone());
    assert_eq!(out, input);
}

/// `when A is { … }` use: subject and a matching subject_name are both
/// rewritten to the RHS.
#[test]
fn fires_on_when_subject_with_subject_name() {
    let clause = |body: PseudoExpr| WhenClause {
        pattern: crate::pseudo::ast::WhenPattern::Wildcard,
        guard: None,
        body,
    };
    let input = with_marker(with_rhs_origin(
        "e",
        10,
        alias_let(
            "variant_61",
            20,
            varref("e", 10),
            PseudoExpr::When {
                subject: PBox::new(varref("variant_61", 20)),
                subject_name: Some(Binder::new("variant_61".to_string(), VarId::new(20))),
                clauses: vec![clause(PseudoExpr::int(1))],
            },
        ),
    ));
    let out = copy_propagate_var_aliases(input);
    let expected = with_marker(with_rhs_origin(
        "e",
        10,
        PseudoExpr::When {
            subject: PBox::new(varref("e", 10)),
            subject_name: Some(Binder::new("e".to_string(), VarId::new(10))),
            clauses: vec![clause(PseudoExpr::int(1))],
        },
    ));
    assert_eq!(out, expected);
}

/// Chains collapse via the fixpoint: `let a = b; let c = a; f(c)` ->
/// `f(b)`.
#[test]
fn fixpoint_collapses_chain() {
    let input = with_marker(with_rhs_origin(
        "b",
        10,
        alias_let(
            "a",
            20,
            varref("b", 10),
            alias_let(
                "c",
                21,
                varref("a", 20),
                PseudoExpr::Apply {
                    function: PBox::new(varref("f", 30)),
                    args: vec![varref("c", 21)].into(),
                },
            ),
        ),
    ));
    let out = copy_propagate_var_aliases(input);
    let expected = with_marker(with_rhs_origin(
        "b",
        10,
        PseudoExpr::Apply {
            function: PBox::new(varref("f", 30)),
            args: vec![varref("b", 10)].into(),
        },
    ));
    assert_eq!(out, expected);
}

/// The RHS raw name `when` RENDERS as `when_`, so an
/// intervening binder literally named `when_` print-captures the moved
/// reference — the sanitized-name comparison must veto.
#[test]
fn veto_sanitized_print_capture_on_path() {
    let input = with_marker(with_rhs_origin(
        "when",
        10,
        alias_let(
            "p10",
            20,
            varref("when", 10),
            PseudoExpr::Lambda {
                params: vec![Binder::new("when_".to_string(), VarId::new(40))],
                body: PBox::new(varref("p10", 20)),
            },
        ),
    ));
    let out = copy_propagate_var_aliases(input.clone());
    assert_eq!(out, input);
}

/// An alias raw-named `when` renders `when_`; an id-less
/// compat ref spelled `when_` aliases it at the render layer and must
/// keep the let (sanitized dual count).
#[test]
fn veto_sanitized_name_only_compat_ref() {
    let input = with_marker(with_rhs_origin(
        "w",
        10,
        alias_let(
            "when",
            20,
            varref("w", 10),
            PseudoExpr::Apply {
                function: PBox::new(varref("when", 20)),
                args: vec![PseudoExpr::var("when_")].into(),
            },
        ),
    ));
    let out = copy_propagate_var_aliases(input.clone());
    assert_eq!(out, input);
}

/// Idempotence.
#[test]
fn idempotent() {
    let input = with_marker(with_rhs_origin(
        "w",
        10,
        alias_let(
            "p10",
            20,
            varref("w", 10),
            PseudoExpr::Apply {
                function: PBox::new(varref("f", 30)),
                args: vec![varref("p10", 20)].into(),
            },
        ),
    ));
    let once = copy_propagate_var_aliases(input);
    let twice = copy_propagate_var_aliases(once.clone());
    assert_eq!(twice, once);
}

/// Without the `decompiled` marker the pass is a no-op (G0).
#[test]
fn noop_without_marker() {
    let input = with_rhs_origin(
        "w",
        10,
        alias_let(
            "p10",
            20,
            varref("w", 10),
            PseudoExpr::Apply {
                function: PBox::new(varref("f", 30)),
                args: vec![varref("p10", 20)].into(),
            },
        ),
    );
    let out = copy_propagate_var_aliases(input.clone());
    assert_eq!(out, input);
}
