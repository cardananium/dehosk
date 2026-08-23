use super::*;
use crate::pseudo::ast::PBox;

/// Naming determinism across fixed-point iterations.
///
/// Two sibling `Data.un_int(field_access)` bindings both get pretty-name
/// "int" from `suggest_generated_binding_name`; the within-pass
/// `naming.renames` collision check dedups the second to "int_1". Later
/// passes over the converged tree must keep `int` / `int_1`, not drift to
/// `int_2`, `int_3`, ... — `state.used_semantic_names` accumulates
/// monotonically across passes and `is_generated_temp_name("int_1")` is
/// true (last char is a digit), so the second binding is re-suggested
/// "int" on every pass and bumped past every used suffix.
#[test]
fn test_simplify_dedup_suffix_is_a_fixed_point_across_passes() {
    let z_id = VarId::from_raw(7);
    let outer_id = VarId::from_raw(20);
    let inner_id = VarId::from_raw(21);

    let z_var = || PseudoExpr::Var {
        name: "z".to_string(),
        id: Some(z_id),
    };
    let un_int = |arg| PseudoExpr::BuiltinCall {
        name: BuiltinId::expect_known("Data.un_int"),
        args: vec![arg].into(),
    };

    let expr = PseudoExpr::Lambda {
        params: vec!["z".to_string().into()],
        body: PBox::new(PseudoExpr::Let {
            name: "x_10".to_string(),
            id: outer_id.into(),
            value: PBox::new(un_int(PseudoExpr::field_access(z_var(), "a".to_string()))),
            body: PBox::new(PseudoExpr::Let {
                name: "x_11".to_string(),
                id: inner_id.into(),
                value: PBox::new(un_int(PseudoExpr::field_access(z_var(), "b".to_string()))),
                body: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Add,
                    left: PBox::new(PseudoExpr::BinOp {
                        op: BinaryOp::Add,
                        left: PBox::new(PseudoExpr::Var {
                            name: "x_10".to_string(),
                            id: Some(outer_id),
                        }),
                        right: PBox::new(PseudoExpr::Var {
                            name: "x_10".to_string(),
                            id: Some(outer_id),
                        }),
                    }),
                    right: PBox::new(PseudoExpr::BinOp {
                        op: BinaryOp::Add,
                        left: PBox::new(PseudoExpr::Var {
                            name: "x_11".to_string(),
                            id: Some(inner_id),
                        }),
                        right: PBox::new(PseudoExpr::Var {
                            name: "x_11".to_string(),
                            id: Some(inner_id),
                        }),
                    }),
                }),
            }),
        }),
    };

    let mut state = SimplifyState::default();
    let pass1 = simplify_with_state(expr.clone(), None, false, None, &mut state).expr;
    let pass2 = simplify_with_state(pass1.clone(), None, false, None, &mut state).expr;
    let pass3 = simplify_with_state(pass2.clone(), None, false, None, &mut state).expr;

    let p1 = pass1.to_pretty();
    let p2 = pass2.to_pretty();
    let p3 = pass3.to_pretty();

    // Baseline: pass 1 must give the two sibling `Data.un_int(z.{a,b})`
    // bindings distinct names. Unprefixed they are `int` and `int_1`; the
    // render-time field-name prefix pass upgrades the first to `a_int` or
    // `b_int` from its FieldAccess source and leaves the dedup-suffixed
    // sibling alone. Any of these mixed shapes is acceptable — the real
    // invariant is the cross-pass fixed point below.
    let has_legacy_dedup = p1.contains("let int_1 =") && p1.contains("let int =");
    let has_full_field_prefixed = p1.contains("let a_int =") && p1.contains("let b_int =");
    let has_mixed_a_int_int_1 = p1.contains("let a_int =") && p1.contains("let int_1 =");
    let has_mixed_b_int_int_1 = p1.contains("let b_int =") && p1.contains("let int_1 =");
    assert!(
        has_legacy_dedup
            || has_full_field_prefixed
            || has_mixed_a_int_int_1
            || has_mixed_b_int_int_1,
        "baseline assumption: pass 1 must produce two distinct un_int aliases:\n{p1}"
    );
    assert_eq!(
        p1, p2,
        "pass 2 must be a fixed point of pass 1 (no transient suffix drift):\n--- pass1 ---\n{p1}\n--- pass2 ---\n{p2}"
    );
    assert_eq!(
        p2, p3,
        "pass 3 must also be a fixed point (no monotonic drift):\n--- pass2 ---\n{p2}\n--- pass3 ---\n{p3}"
    );
}

/// TP12 - `suggest_generated_binding_name` must not synthesise an
/// `{fn}_result` alias for bare generic helper names like `f` / `f_2` /
/// `f_10`. Those collide with the early-rename placeholders for
/// top-level helpers that hoisting later promotes to `fn_N` at root
/// level, so `f_N_result_M` bindings in inner scopes can dangle once
/// hoisting rearranges scopes. Mirrors the prefix filter in
/// `decompile/rename.rs::hint_from_value`.
#[test]
fn test_tp12_generated_name_skips_bare_generic_f_n_callee() {
    let f2_id = VarId::from_raw(42);
    let arg_id = VarId::from_raw(43);
    let tmp_id = VarId::from_raw(44);

    // Shape: let f_2 = fn(x) { ... } in
    //        let tmp_17 = f_2(arg) in
    //        tmp_17
    let expr = PseudoExpr::Let {
        name: "f_2".to_string(),
        id: f2_id.into(),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(VarId::fresh_compat_placeholder()),
            }),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "tmp_17".to_string(),
            id: tmp_id.into(),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Var {
                    name: "f_2".to_string(),
                    id: Some(f2_id),
                }),
                args: vec![PseudoExpr::Var {
                    name: "arg".to_string(),
                    id: Some(arg_id),
                }]
                .into(),
            }),
            body: PBox::new(PseudoExpr::Var {
                name: "tmp_17".to_string(),
                id: Some(tmp_id),
            }),
        }),
    };

    let rendered = simplify(expr).to_pretty();
    assert!(
        !rendered.contains("f_2_result"),
        "simplify must not name the `let tmp = f_2(arg)` binding `f_2_result`:\n{rendered}"
    );
}

/// TP12 - the prefix filter must be narrow: `f_2_result` is blocked,
/// but clearly non-generic names like `fn_3` still get their
/// `{fn}_result` alias.
#[test]
fn test_tp12_generated_name_still_fires_for_non_generic_callee() {
    let fn_id = VarId::from_raw(50);
    let arg_id = VarId::from_raw(51);
    let tmp_id = VarId::from_raw(52);

    let expr = PseudoExpr::Let {
        name: "tmp_17".to_string(),
        id: tmp_id.into(),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Var {
                name: "fn_3".to_string(),
                id: Some(fn_id),
            }),
            args: vec![PseudoExpr::Var {
                name: "arg".to_string(),
                id: Some(arg_id),
            }]
            .into(),
        }),
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::Var {
                name: "tmp_17".to_string(),
                id: Some(tmp_id),
            }),
            right: PBox::new(PseudoExpr::Var {
                name: "tmp_17".to_string(),
                id: Some(tmp_id),
            }),
        }),
    };

    let rendered = simplify(expr).to_pretty();
    assert!(
        rendered.contains("fn_3_result"),
        "simplify must still surface `fn_3_result` for non-bare-generic callees:\n{rendered}"
    );
}

#[test]
fn test_call_result_mint_site_gates_match_fallback_inference() {
    let foo_id = VarId::from_raw(61);
    let arg_id = VarId::from_raw(62);
    let call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("foo", foo_id)),
        args: vec![PseudoExpr::var_with_id("arg", arg_id)].into(),
    };

    assert_eq!(
        Simplifier::call_result_callee_for_binding_name("foo_result", &call),
        Some(foo_id)
    );
    assert_eq!(
        Simplifier::call_result_callee_for_binding_name("bar_result", &call),
        None,
        "mismatched binding stem must not be tagged as a foo() call result"
    );

    let bare_generic_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("f_2", foo_id)),
        args: vec![PseudoExpr::var_with_id("arg", arg_id)].into(),
    };
    assert_eq!(
        Simplifier::call_result_callee_for_binding_name("f_2_result", &bare_generic_call),
        None,
        "bare generic helpers are deliberately excluded from CallResult minting"
    );

    let zero_arg_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("foo", foo_id)),
        args: vec![].into(),
    };
    assert_eq!(
        Simplifier::call_result_callee_for_binding_name("foo_result", &zero_arg_call),
        None,
        "zero-arg Apply is not a real call result"
    );
}

#[test]
fn test_call_result_mint_site_records_only_non_generic_real_calls() {
    let fn_id = VarId::from_raw(63);
    let arg_id = VarId::from_raw(64);
    let tmp_id = VarId::from_raw(65);
    let expr = PseudoExpr::Let {
        name: "tmp_17".to_string(),
        id: tmp_id.into(),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("fn_3", fn_id)),
            args: vec![PseudoExpr::var_with_id("arg", arg_id)].into(),
        }),
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::var_with_id("tmp_17", tmp_id)),
            right: PBox::new(PseudoExpr::var_with_id("tmp_17", tmp_id)),
        }),
    };

    let mut state = SimplifyState::default();
    let output = simplify_with_state(expr, None, false, None, &mut state);

    assert!(
        matches!(
            &output.expr,
            PseudoExpr::Let { name, .. } if name == "fn_3_result"
        ),
        "expected call result readability rename, got: {:?}",
        output.expr
    );
    assert!(
        matches!(
            state.var_kinds.kind_annotations.get(&tmp_id),
            Some(crate::pseudo::nameless::VarKind::CallResult { callee }) if *callee == fn_id
        ),
        "expected CallResult annotation for tmp binding, got: {:?}",
        state.var_kinds.kind_annotations.get(&tmp_id)
    );

    let bare_id = VarId::from_raw(66);
    let bare_tmp_id = VarId::from_raw(67);
    let bare_expr = PseudoExpr::Let {
        name: "tmp_18".to_string(),
        id: bare_tmp_id.into(),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("f_2", bare_id)),
            args: vec![PseudoExpr::var_with_id("arg", arg_id)].into(),
        }),
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::var_with_id("tmp_18", bare_tmp_id)),
            right: PBox::new(PseudoExpr::var_with_id("tmp_18", bare_tmp_id)),
        }),
    };

    let mut state = SimplifyState::default();
    let _output = simplify_with_state(bare_expr, None, false, None, &mut state);

    assert!(
        !state.var_kinds.kind_annotations.contains_key(&bare_tmp_id),
        "bare generic call result must not mint a CallResult annotation: {:?}",
        state.var_kinds.kind_annotations.get(&bare_tmp_id)
    );
}

#[test]
fn test_call_result_mint_site_records_existing_result_name() {
    let fn_id = VarId::from_raw(68);
    let arg_id = VarId::from_raw(69);
    let tmp_id = VarId::from_raw(70);
    let expr = PseudoExpr::Let {
        name: "fn_3_result".to_string(),
        id: tmp_id.into(),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("fn_3", fn_id)),
            args: vec![PseudoExpr::var_with_id("arg", arg_id)].into(),
        }),
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::var_with_id("fn_3_result", tmp_id)),
            right: PBox::new(PseudoExpr::var_with_id("fn_3_result", tmp_id)),
        }),
    };

    let mut state = SimplifyState::default();
    let output = simplify_with_state(expr, None, false, None, &mut state);

    assert!(
        matches!(
            &output.expr,
            PseudoExpr::Let { name, .. } if name == "fn_3_result"
        ),
        "expected existing result name to stay intact, got: {:?}",
        output.expr
    );
    assert!(
        matches!(
            state.var_kinds.kind_annotations.get(&tmp_id),
            Some(crate::pseudo::nameless::VarKind::CallResult { callee }) if *callee == fn_id
        ),
        "existing result-name let should mint CallResult annotation, got: {:?}",
        state.var_kinds.kind_annotations.get(&tmp_id)
    );
}

/// B16 - extend TP12's filter to the recursive placeholders `rec_fn_N` /
/// `self_fn_N`. Hoisting rearranges these like bare `f_N`, so
/// `rec_fn_N_result` aliases in inner scopes would be stranded.
#[test]
fn test_b16_generated_name_skips_bare_rec_fn_callee() {
    let rec_id = VarId::from_raw(70);
    let arg_id = VarId::from_raw(71);
    let tmp_id = VarId::from_raw(72);

    let expr = PseudoExpr::Let {
        name: "tmp_18".to_string(),
        id: tmp_id.into(),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Var {
                name: "rec_fn_6".to_string(),
                id: Some(rec_id),
            }),
            args: vec![PseudoExpr::Var {
                name: "arg".to_string(),
                id: Some(arg_id),
            }]
            .into(),
        }),
        body: PBox::new(PseudoExpr::Var {
            name: "tmp_18".to_string(),
            id: Some(tmp_id),
        }),
    };

    let rendered = simplify(expr).to_pretty();
    assert!(
        !rendered.contains("rec_fn_6_result"),
        "simplify must not name the `let tmp = rec_fn_6(arg)` binding `rec_fn_6_result`:\n{rendered}"
    );
}

/// B17 - `let k20 = subject.fields[3]; k20.tag` must not leave a dangling
/// `k20.tag` reference. Both outcomes after simplify+to_pretty are fine:
///   1. `let k20 = ...` survives and the body keeps `k20.tag`.
///   2. `let k20 = ...` is dropped and the body inlines
///      `subject.fields[3].tag`.
///      The failure: the let is dropped AND the body still references `k20`.
#[test]
fn test_b17_let_with_only_tag_use_does_not_become_dangling() {
    let subject_id = VarId::from_raw(60);
    let k20_id = VarId::from_raw(61);

    // let subject = #"00" in
    //   let k20: Data = subject.fields[3] in
    //     k20.tag
    let expr = PseudoExpr::Let {
        name: "subject".to_string(),
        id: subject_id.into(),
        value: PBox::new(PseudoExpr::ByteArray(vec![0])),
        body: PBox::new(PseudoExpr::Let {
            name: "k20".to_string(),
            id: k20_id.into(),
            value: PBox::new(PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::FieldAccess {
                    record: PBox::new(PseudoExpr::Var {
                        name: "subject".to_string(),
                        id: Some(subject_id),
                    }),
                    selector: crate::pseudo::field_selector::FieldSelector::NamedField(
                        "fields".to_string(),
                    ),
                }),
                index: 3,
            }),
            body: PBox::new(PseudoExpr::FieldAccess {
                record: PBox::new(PseudoExpr::Var {
                    name: "k20".to_string(),
                    id: Some(k20_id),
                }),
                selector: crate::pseudo::field_selector::FieldSelector::NamedField(
                    "tag".to_string(),
                ),
            }),
        }),
    };

    let rendered = simplify(expr).to_pretty();

    // Either k20 is preserved as a binder, or it has been inlined.
    let bound = rendered.contains("let k20") || rendered.contains("let k20:");
    let inlined = !rendered.contains("k20.tag");
    assert!(
        bound || inlined,
        "simplify dropped `let k20` while keeping a `k20.tag` reference:\n{rendered}"
    );
}

/// B17 inside a `rec fn` body: the rec-fn boundary can break var-use
/// counting across scopes if shadowing in `count_var_uses_by_id` does
/// not match the dead-let elimination's view.
#[test]
fn test_b17_let_with_only_tag_use_inside_rec_fn() {
    use crate::pseudo::field_selector::FieldSelector;

    let v_1006_id = VarId::from_raw(70);
    let k20_id = VarId::from_raw(71);
    let g21_id = VarId::from_raw(72);

    // Rec fn rec_fn_25(v_1006) {
    //   let k20 = v_1006.fields[3] in
    //     let g21 = k20.tag in
    //       g21
    // }
    let rec_body = PseudoExpr::Let {
        name: "k20".to_string(),
        id: k20_id.into(),
        value: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::FieldAccess {
                record: PBox::new(PseudoExpr::Var {
                    name: "v_1006".to_string(),
                    id: Some(v_1006_id),
                }),
                selector: FieldSelector::NamedField("fields".to_string()),
            }),
            index: 3,
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "g21".to_string(),
            id: g21_id.into(),
            value: PBox::new(PseudoExpr::FieldAccess {
                record: PBox::new(PseudoExpr::Var {
                    name: "k20".to_string(),
                    id: Some(k20_id),
                }),
                selector: FieldSelector::NamedField("tag".to_string()),
            }),
            body: PBox::new(PseudoExpr::Var {
                name: "g21".to_string(),
                id: Some(g21_id),
            }),
        }),
    };

    let expr = PseudoExpr::RecFn {
        name: Binder::new("rec_fn_25", VarId::from_raw(73)),
        params: vec![Binder::new("v_1006", v_1006_id)],
        body: PBox::new(rec_body),
    };

    let rendered = simplify(expr).to_pretty();

    let bound_k20 = rendered.contains("let k20");
    let inlined_k20 = !rendered.contains("k20.tag");
    assert!(
        bound_k20 || inlined_k20,
        "simplify inside rec_fn dropped `let k20` while keeping `k20.tag`:\n{rendered}"
    );
}
