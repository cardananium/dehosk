use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PVec;
use crate::pseudo::ast::PseudoType;
use std::rc::Rc;

#[test]
fn test_print_int() {
    let expr = PseudoExpr::int(42);
    assert_eq!(expr.to_pretty(), "42");
}

#[test]
fn sanitize_identifier_escapes_keywords_not_purpose_words() {
    // Surface keywords must be escaped.
    assert_eq!(sanitize_identifier("fn"), "fn_");
    assert_eq!(sanitize_identifier("when"), "when_");
    assert_eq!(sanitize_identifier("expect"), "expect_");
    assert_eq!(sanitize_identifier("Some"), "Some_");
    // Validator-purpose words are NOT reserved value identifiers — the
    // canonical TxInfo `mint` field must render as `mint`, not `mint_`.
    assert_eq!(sanitize_identifier("mint"), "mint");
    assert_eq!(sanitize_identifier("spend"), "spend");
    assert_eq!(sanitize_identifier("withdraw"), "withdraw");
    assert_eq!(sanitize_identifier("certificate"), "certificate");
    assert_eq!(sanitize_identifier("publish"), "publish");
    assert_eq!(sanitize_identifier("vote"), "vote");
    // Ordinary names pass through.
    assert_eq!(sanitize_identifier("inputs"), "inputs");
}

#[test]
fn parametrized_script_renders_with_section_markers() {
    // applied param prologue → main entry lambda → helpers
    let policy_id = vec![0xea, 0x07];
    let param_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let helper_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let helper_param_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let ctx_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();

    // A non-identity, non-forwarder helper body, so render-prep leaves it
    // alone: `inline_identity_helper` collapses `fn(x){x}`, and
    // `eta_reduce_lambda_forwarder` collapses `fn(x){F(x)}` to `F` —
    // losing the Lambda shape this test pins section-marker layout
    // against. The `+ 1` wrap blocks both; `+ 0` would not, since
    // `fold_arith_identity` strips additive identities.
    let helper = PseudoExpr::Lambda {
        params: vec![Binder::new("x", helper_param_id)],
        body: PBox::new(PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Add,
            left: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("decode_inner")),
                args: vec![PseudoExpr::var_with_id("x", helper_param_id)].into(),
            }),
            right: PBox::new(PseudoExpr::int(1)),
        }),
    };

    let main_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", ctx_id)],
        body: PBox::new(PseudoExpr::var_with_id("script_context", ctx_id)),
    };

    let helper_let = PseudoExpr::Let {
        name: "decode".to_string(),
        id: Some(helper_id),
        value: PBox::new(helper),
        body: PBox::new(main_lambda),
    };

    let expr = PseudoExpr::Let {
        name: "policy".to_string(),
        id: Some(param_id),
        value: PBox::new(PseudoExpr::Constr {
            type_hint: None,
            tag: 1,
            fields: vec![PseudoExpr::byte_array(policy_id)].into(),
            shape: ConstructorShape::unknown_data(1, 1),
        }),
        body: PBox::new(helper_let),
    };

    let rendered = expr.to_pretty();
    // Section markers must be present in the parametrized layout
    assert!(
        rendered.contains("// Parameters"),
        "missing Parameters marker in:\n{}",
        rendered
    );
    assert!(
        rendered.contains("// Main"),
        "missing Main marker in:\n{}",
        rendered
    );
    assert!(
        rendered.contains("// Helpers"),
        "missing Helpers marker in:\n{}",
        rendered
    );
    // Parameters section should appear before Main, Main before Helpers
    let p_idx = rendered.find("// Parameters").unwrap();
    let m_idx = rendered.find("// Main").unwrap();
    let h_idx = rendered.find("// Helpers").unwrap();
    assert!(
        p_idx < m_idx && m_idx < h_idx,
        "section ordering violated: P={} M={} H={}\n{}",
        p_idx,
        m_idx,
        h_idx,
        rendered
    );
    // Parameter binding should look like `let policy = ...`
    assert!(
        rendered.contains("let policy ="),
        "parameter let not rendered in:\n{}",
        rendered
    );
}

#[test]
fn non_parametrized_script_does_not_emit_section_markers() {
    // Pure helper-prologue + main entry lambda; should stay LambdaWithHelpers.
    let helper_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let helper_param_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let ctx_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();

    // A non-identity, non-forwarder helper body, so render-prep leaves it
    // alone: `inline_identity_helper` collapses `fn(x){x}`, and
    // `eta_reduce_lambda_forwarder` collapses `fn(x){F(x)}` to `F` —
    // losing the Lambda shape this test pins section-marker layout
    // against. The `+ 1` wrap blocks both; `+ 0` would not, since
    // `fold_arith_identity` strips additive identities.
    let helper = PseudoExpr::Lambda {
        params: vec![Binder::new("x", helper_param_id)],
        body: PBox::new(PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Add,
            left: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("decode_inner")),
                args: vec![PseudoExpr::var_with_id("x", helper_param_id)].into(),
            }),
            right: PBox::new(PseudoExpr::int(1)),
        }),
    };

    let main_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", ctx_id)],
        body: PBox::new(PseudoExpr::var_with_id("script_context", ctx_id)),
    };

    let expr = PseudoExpr::Let {
        name: "decode".to_string(),
        id: Some(helper_id),
        value: PBox::new(helper),
        body: PBox::new(main_lambda),
    };

    let rendered = expr.to_pretty();
    assert!(
        !rendered.contains("// Parameters"),
        "non-param script should not emit Parameters marker:\n{}",
        rendered
    );
    assert!(
        !rendered.contains("// Main"),
        "non-param script should not emit Main marker:\n{}",
        rendered
    );
    assert!(
        !rendered.contains("// Helpers"),
        "non-param script should not emit Helpers marker:\n{}",
        rendered
    );
}

#[test]
fn test_print_bool() {
    assert_eq!(PseudoExpr::bool(true).to_pretty(), "True");
    assert_eq!(PseudoExpr::bool(false).to_pretty(), "False");
}

#[test]
fn test_print_string() {
    let expr = PseudoExpr::string("hello");
    assert_eq!(expr.to_pretty(), "@\"hello\"");
}

#[test]
fn test_print_byte_array() {
    let expr = PseudoExpr::byte_array(vec![0xca, 0xfe]);
    assert_eq!(expr.to_pretty(), "#\"cafe\"");
}

#[test]
fn test_print_binop() {
    let expr = PseudoExpr::binop(BinaryOp::Add, PseudoExpr::int(1), PseudoExpr::int(2));
    assert_eq!(expr.to_pretty(), "1 + 2");
}

#[test]
fn test_to_pretty_with_spans_covers_root_expr() {
    let expr = PseudoExpr::binop(BinaryOp::Add, PseudoExpr::int(1), PseudoExpr::int(2));
    let root_id = expr.provenance_graph().root_id;

    let (output, spans) = expr.to_pretty_with_spans();
    let root_span = spans
        .iter()
        .find(|(node_id, _)| *node_id == root_id)
        .map(|(_, span)| *span)
        .expect("root span should be present");

    assert_eq!(output, "1 + 2");
    assert_eq!(
        root_span,
        SourceSpan {
            start_line: 1,
            start_col: 1,
            end_line: 1,
            end_col: 5,
        }
    );
}

#[test]
fn test_to_pretty_with_spans_and_config_respects_show_types() {
    let expr = PseudoExpr::Var {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
    };

    let (output, spans) = expr.to_pretty_with_spans_and_config(PrettyConfig {
        show_types: true,
        ..PrettyConfig::default()
    });

    let root_id = expr.provenance_graph().root_id;
    let root_span = spans
        .iter()
        .find(|(node_id, _)| *node_id == root_id)
        .map(|(_, span)| *span)
        .expect("root span should be present");

    // Declaration-only rendering: Var references never emit `: Type`
    // even when show_types is on.
    assert_eq!(output, "x");
    assert_eq!(
        root_span,
        SourceSpan {
            start_line: 1,
            start_col: 1,
            end_line: 1,
            end_col: 1,
        }
    );
}

/// A trailing newline terminates the last line; it does not open another.
///
/// The line table and `str::lines` must agree on how many lines exist: a
/// span's `start_line` is handed to a reader as a position to show, and a
/// phantom table entry at `source.len()` numbers an end-of-document offset
/// one line past the document — a line no reader can resolve.
#[test]
fn the_line_table_counts_the_lines_a_reader_sees() {
    for source in ["a\nb\n", "a\nb", "\n", "x", "a\n\n\n"] {
        assert_eq!(
            collect_line_starts(source).len(),
            source.lines().count(),
            "line table disagrees with str::lines for {source:?}"
        );
    }

    // The end-of-document offset resolves to the last REAL line, not past it.
    let source = "a\nbc\n";
    let line_starts = collect_line_starts(source);
    let span = byte_range_to_span(&line_starts, source.len(), source.len(), source.len());
    assert_eq!(span.start_line, 2, "end offset must land on the last line");
    assert!(span.start_line as usize <= source.lines().count());
}

/// The renderer's last edit of the text happens BEFORE the offsets are numbered.
///
/// `strip_validator_entry_terminator` removes the trailing `Void` from a
/// validator-entry spine. Numbering against the pre-strip text leaves
/// annotations ending in the removed region with offsets past the new end, so
/// they come out as spans one line past the document. Every span this renderer
/// hands out must name a line that exists in the text it hands out.
#[test]
fn every_span_starts_on_a_line_that_exists_after_the_terminator_is_stripped() {
    let expr = PseudoExpr::let_bind(
        "decompiled",
        PseudoExpr::int(1),
        PseudoExpr::let_bind("helper", PseudoExpr::int(2), PseudoExpr::Unit),
    );

    let (rendered, spans) = expr.to_pretty_with_spans();
    assert!(
        !rendered.trim_end().ends_with("Void"),
        "this fixture must exercise the strip; got {rendered:?}"
    );

    let line_count = rendered.lines().count() as u32;
    let bad: Vec<_> = spans
        .iter()
        .filter(|(_, span)| span.start_line == 0 || span.start_line > line_count)
        .collect();
    assert!(
        bad.is_empty(),
        "spans start outside 1..={line_count} of {rendered:?}: {bad:?}"
    );
}

#[test]
fn byte_range_to_span_preserves_multiline_byte_offsets() {
    let source = "a\nbc\ndef";
    let line_starts = collect_line_starts(source);

    assert_eq!(
        byte_range_to_span(&line_starts, source.len(), 2, 4),
        SourceSpan {
            start_line: 2,
            start_col: 1,
            end_line: 2,
            end_col: 2,
        }
    );
    assert_eq!(
        byte_range_to_span(&line_starts, source.len(), 5, 8),
        SourceSpan {
            start_line: 3,
            start_col: 1,
            end_line: 3,
            end_col: 3,
        }
    );
}

#[test]
fn test_logical_chain_prints_one_condition_per_line() {
    let expr = PseudoExpr::binop(
        BinaryOp::And,
        PseudoExpr::binop(BinaryOp::And, PseudoExpr::var("a"), PseudoExpr::var("b")),
        PseudoExpr::var("c"),
    );
    let output = expr.to_pretty();

    assert_eq!(output, "a &&\nb &&\nc");
}

#[test]
fn test_long_builtin_call_with_simple_var_args_stays_one_line() {
    // 3+ simple Var args defer to the pretty printer's natural width-based
    // wrapping — short calls stay on one line.
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("verify_ed25519_signature"),
        args: vec![
            PseudoExpr::var("a"),
            PseudoExpr::var("b"),
            PseudoExpr::var("c"),
        ]
        .into(),
    };

    let output = expr.to_pretty();
    assert_eq!(
        output, "Crypto.verify_ed25519(a, b, c)",
        "output was:\n{}",
        output
    );
}

#[test]
fn test_partial_if_builtin_name_is_readable() {
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("if"),
        args: vec![].into(),
    };
    assert_eq!(expr.to_pretty(), "if_then_else");
}

#[test]
fn test_partial_if_builtin_call_name_is_readable() {
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("if"),
        args: vec![PseudoExpr::var("cond")].into(),
    };
    assert_eq!(expr.to_pretty(), "if_then_else(cond)");
}

#[test]
fn test_print_binop_precedence() {
    // (1 + 2) * 3 should be "(1 + 2) * 3"
    let expr = PseudoExpr::binop(
        BinaryOp::Mul,
        PseudoExpr::binop(BinaryOp::Add, PseudoExpr::int(1), PseudoExpr::int(2)),
        PseudoExpr::int(3),
    );
    assert_eq!(expr.to_pretty(), "(1 + 2) * 3");

    // 1 + 2 * 3 should be "1 + 2 * 3"
    let expr = PseudoExpr::binop(
        BinaryOp::Add,
        PseudoExpr::int(1),
        PseudoExpr::binop(BinaryOp::Mul, PseudoExpr::int(2), PseudoExpr::int(3)),
    );
    assert_eq!(expr.to_pretty(), "1 + 2 * 3");
}

#[test]
fn test_binop_rhs_let_prints_as_block_operand() {
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(PseudoExpr::var("hash")),
        right: PBox::new(PseudoExpr::let_bind(
            "field_0_2",
            PseudoExpr::builtin("Data.to_bytes", vec![PseudoExpr::var("field_0")]),
            PseudoExpr::var("field_0_2"),
        )),
    };

    let expected = "\
hash == (
  let field_0_2 = Data.to_bytes(field_0)
  field_0_2
)";
    assert_eq!(expr.to_pretty(), expected);
}

#[test]
fn test_or_rhs_let_prints_as_block_operand() {
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Lte,
            left: PBox::new(PseudoExpr::var("snd")),
            right: PBox::new(PseudoExpr::int(0)),
        }),
        right: PBox::new(PseudoExpr::let_bind(
            "redeemer_fields",
            PseudoExpr::field_access(PseudoExpr::var("redeemer"), "fields".to_string()),
            PseudoExpr::var("redeemer_fields"),
        )),
    };

    // Default render (compilable-data-access OFF): `lower_constr_field_sugar`
    // is gated off, so `redeemer.fields` stays the readable pseudo accessor;
    // ON it would lower to `builtin.un_constr_data(redeemer).2nd`.
    let expected = "\
snd <= 0 || (
  let redeemer_fields = redeemer.fields
  redeemer_fields
)";
    assert_eq!(expr.to_pretty(), expected);
}

#[test]
fn test_print_list() {
    let expr = PseudoExpr::list(vec![
        PseudoExpr::int(1),
        PseudoExpr::int(2),
        PseudoExpr::int(3),
    ]);
    assert_eq!(expr.to_pretty(), "[1, 2, 3]");
}

#[test]
fn test_print_constr() {
    let expr = PseudoExpr::some(PseudoExpr::int(42));
    assert_eq!(expr.to_pretty(), "Some(42)");

    let expr = PseudoExpr::none();
    assert_eq!(expr.to_pretty(), "None");
}

#[test]
fn test_print_if() {
    let expr = PseudoExpr::if_then_else(
        PseudoExpr::bool(true),
        PseudoExpr::int(1),
        PseudoExpr::int(0),
    );
    let output = expr.to_pretty();
    assert!(output.contains("if"));
    assert!(output.contains("True"));
    assert!(output.contains("else"));
}

#[test]
fn test_nested_let_flattening_simple() {
    // let x = (let y = 1 in y) in x
    // should flatten to sequential lets
    let inner_let = PseudoExpr::let_bind("y", PseudoExpr::int(1), PseudoExpr::var("y"));
    let outer_let = PseudoExpr::let_bind("x", inner_let, PseudoExpr::var("x"));
    let output = outer_let.to_pretty();
    assert!(output.starts_with("let y ="), "output was: {}", output);
    assert!(output.contains("let x ="), "output was: {}", output);
    // y binding should come before x binding
    let y_pos = output.find("let y =").unwrap();
    let x_pos = output.find("let x =").unwrap();
    assert!(
        y_pos < x_pos,
        "let y should come before let x, output was: {}",
        output
    );
    assert!(output.ends_with("x"), "output was: {}", output);
}

#[test]
fn test_nested_let_flattening_triple() {
    // let a = (let b = (let c = 1 in c) in b) in a
    // should flatten all three lets in order: c, b, a
    let inner_let = PseudoExpr::let_bind("c", PseudoExpr::int(1), PseudoExpr::var("c"));
    let mid_let = PseudoExpr::let_bind("b", inner_let, PseudoExpr::var("b"));
    let outer_let = PseudoExpr::let_bind("a", mid_let, PseudoExpr::var("a"));
    let output = outer_let.to_pretty();
    let c_pos = output.find("let c =").unwrap();
    let b_pos = output.find("let b =").unwrap();
    let a_pos = output.find("let a =").unwrap();
    assert!(c_pos < b_pos, "let c before let b, output: {}", output);
    assert!(b_pos < a_pos, "let b before let a, output: {}", output);
    assert!(output.ends_with("a"), "output was: {}", output);
}

#[test]
fn test_nested_let_non_identity_value_flattened_when_safe() {
    // let x = (let y = 1 in y + 1) in x
    // Should flatten to top-level sequential bindings.
    let inner_let = PseudoExpr::let_bind(
        "y",
        PseudoExpr::int(1),
        PseudoExpr::binop(BinaryOp::Add, PseudoExpr::var("y"), PseudoExpr::int(1)),
    );
    let outer_let = PseudoExpr::let_bind("x", inner_let, PseudoExpr::var("x"));
    let output = outer_let.to_pretty();

    let expected = "\
let y = 1
let x = y + 1
x";
    assert_eq!(output, expected, "output was:\n{}", output);
}

#[test]
fn test_nested_let_self_ref_binding_renamed_when_flattened() {
    // let x = (let b = (let c = 1 in b[0]) in b) in x
    // Flattening should avoid confusing `let b = b[0]` by renaming.
    let inner_let = PseudoExpr::let_bind(
        "b",
        PseudoExpr::let_bind(
            "c",
            PseudoExpr::int(1),
            PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::var("b")),
                index: 0,
            },
        ),
        PseudoExpr::var("b"),
    );
    let outer_let = PseudoExpr::let_bind("x", inner_let, PseudoExpr::var("x"));
    let output = outer_let.to_pretty();

    // Naming heuristics may rename the inner `c = 1`; the invariant is that
    // flattening renames the self-referencing `b = b[0]` to `b_2 = b[0]`.
    assert!(
        output.contains("let b_2 ="),
        "expected b_2 rename, output was:\n{}",
        output
    );
    assert!(
        !output.contains("let b =\n  b[0]"),
        "self-ref should be renamed, output was:\n{}",
        output
    );
}

#[test]
fn test_nested_let_deep_self_reference_blocks_flattening() {
    let inner_let = PseudoExpr::let_bind(
        "tmp_bytes",
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
            args: vec![PseudoExpr::field_access(
                PseudoExpr::var("entry"),
                "fst".to_string(),
            )]
            .into(),
        },
        PseudoExpr::If {
            condition: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Lte,
                left: PBox::new(PseudoExpr::var("needle")),
                right: PBox::new(PseudoExpr::var("bytes")),
            }),
            then_branch: PBox::new(PseudoExpr::var("tmp_bytes")),
            else_branch: PBox::new(PseudoExpr::Bool(false)),
        },
    );
    let expr = PseudoExpr::let_bind("bytes", inner_let, PseudoExpr::var("bytes"));

    let output = expr.to_pretty();

    assert!(
        !output.contains("let bytes =\n  if needle <= bytes"),
        "output was:\n{}",
        output
    );
    assert!(
        // the renderer emits the `builtin.un_b_data` surface
        // form, not the pseudonym `Data.un_bytearray`.
        output.contains("let tmp_bytes = builtin.un_b_data(entry.1st)"),
        "output was:\n{}",
        output
    );
}

#[test]
fn test_clause_local_binder_does_not_capture_renamed_let_value() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("pairs")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Var("l2".to_string().into()),
            guard: None,
            body: PseudoExpr::let_bind(
                "l2",
                PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var("l2")),
                    subject_name: None,
                    clauses: vec![WhenClause {
                        pattern: WhenPattern::Wildcard,
                        guard: None,
                        body: PseudoExpr::int(0),
                    }],
                },
                PseudoExpr::var("l2"),
            ),
        }],
    };

    let output = expr.to_pretty();

    assert!(
        !output.contains("let l2 = when l2 is"),
        "output was:\n{}",
        output
    );
    assert!(
        output.contains("let l2_2 = when l2 is") || output.contains("let l2_2 =\n      when l2 is"),
        "output was:\n{}",
        output
    );
}

#[test]
fn test_renaming_body_with_nested_let_keeps_inner_let_order() {
    let expr = PseudoExpr::let_bind(
        "flag",
        PseudoExpr::bool(true),
        PseudoExpr::let_bind(
            "flag",
            PseudoExpr::bool(false),
            PseudoExpr::let_bind(
                "inner",
                PseudoExpr::int(1),
                PseudoExpr::if_then_else(
                    PseudoExpr::var("flag"),
                    PseudoExpr::var("inner"),
                    PseudoExpr::var("inner"),
                ),
            ),
        ),
    );

    let output = expr.to_pretty();

    assert!(output.contains("let inner = 1"), "output was:\n{}", output);
    assert!(
        !output.contains("let inner =\n      if flag_2")
            && !output.contains("let inner =\n    if flag_2"),
        "output was:\n{}",
        output
    );
    assert!(
        output.contains("if flag_2 {") || output.contains("if flag_2: Bool {"),
        "output was:\n{}",
        output
    );
}

#[test]
fn test_nested_let_no_flatten_non_let_value() {
    // let x = 42 in x -- no nested let, should render normally
    let expr = PseudoExpr::let_bind("x", PseudoExpr::int(42), PseudoExpr::var("x"));
    let output = expr.to_pretty();
    assert!(output.contains("let x ="), "output was: {}", output);
    assert!(output.contains("42"), "output was: {}", output);
    assert!(output.ends_with("x"), "output was: {}", output);
}

#[test]
fn test_nested_let_no_flatten_lambda_value() {
    // let x = (let f = fn(a) { Data.to_bytes(a) } in f(1)) in x
    // A Lambda value blocks flattening — the lambda gets `fn name(...)`
    // rendering. The body is non-identity so `inline_identity_helper`
    // doesn't drop the `fn f(a)` helper.
    let inner_let = PseudoExpr::let_bind(
        "f",
        PseudoExpr::Lambda {
            params: vec!["a".to_string().into()],
            body: PBox::new(PseudoExpr::builtin(
                "Data.to_bytes",
                vec![PseudoExpr::var("a")],
            )),
        },
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![PseudoExpr::int(1)].into(),
        },
    );
    let outer_let = PseudoExpr::let_bind("x", inner_let, PseudoExpr::var("x"));
    let output = outer_let.to_pretty();
    // Flattening stops: the inner let keeps its `fn f(a)` lambda form.
    assert!(output.contains("let x ="), "output was: {}", output);
    assert!(output.contains("fn f(a)"), "output was: {}", output);
}

#[test]
fn test_lambda_let_without_direct_calls_keeps_let_form() {
    let expr = PseudoExpr::let_bind(
        "m9",
        PseudoExpr::lambda(
            vec!["x".to_string()],
            PseudoExpr::builtin("Data.to_bytes", vec![PseudoExpr::var("x")]),
        ),
        PseudoExpr::if_then_else(
            PseudoExpr::var("m9"),
            PseudoExpr::int(1),
            PseudoExpr::int(0),
        ),
    );

    let output = expr.to_pretty();
    assert!(output.starts_with("let m9 ="), "output was:\n{}", output);
    assert!(!output.starts_with("fn m9("), "output was:\n{}", output);
}

#[test]
fn test_inverted_rec_let_renders_rec_then_call() {
    // Cosmetic recovery for:
    // let f = f(1) in rec fn f(x) { x }
    // Should print as:
    // rec fn f(x) { x }
    // f(1)
    let expr = PseudoExpr::let_bind(
        "f",
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![PseudoExpr::int(1)].into(),
        },
        PseudoExpr::RecFn {
            name: "f".to_string().into(),
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::var("x")),
        },
    );

    let output = expr.to_pretty();
    assert!(output.starts_with("rec fn "), "output was:\n{}", output);
    assert!(output.ends_with("(1)"), "output was:\n{}", output);
    assert!(!output.contains("let f = f(1)"), "output was:\n{}", output);
}

#[test]
fn test_root_recfn_chain_renders_after_root_lambda() {
    let expr = PseudoExpr::let_bind(
        "lookup",
        PseudoExpr::RecFn {
            name: "lookup".to_string().into(),
            params: vec!["pairs".to_string().into()],
            body: PBox::new(PseudoExpr::var("pairs")),
        },
        PseudoExpr::let_bind(
            "get_at",
            PseudoExpr::RecFn {
                name: "get_at".to_string().into(),
                params: vec!["list".to_string().into(), "index".to_string().into()],
                body: PBox::new(PseudoExpr::var("list")),
            },
            PseudoExpr::Lambda {
                params: vec![
                    "redeemer".to_string().into(),
                    "script_context".to_string().into(),
                ],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("lookup")),
                    args: vec![PseudoExpr::var("redeemer")].into(),
                }),
            },
        ),
    );

    let output = expr.to_pretty();
    let main_pos = output
        .find("fn(redeemer, script_context)")
        .expect("output was missing the root lambda");
    let lookup_pos = output
        .find("rec fn lookup(pairs)")
        .expect("output was missing lookup");
    let get_at_pos = output
        .find("rec fn get_at(list, index)")
        .expect("output was missing get_at");

    assert!(main_pos < lookup_pos, "output was:\n{}", output);
    assert!(lookup_pos < get_at_pos, "output was:\n{}", output);
}

#[test]
fn test_root_helper_chain_with_named_lambda_renders_after_root_lambda() {
    let expr = PseudoExpr::let_bind(
        "lookup",
        PseudoExpr::RecFn {
            name: "lookup".to_string().into(),
            params: vec!["pairs".to_string().into()],
            body: PBox::new(PseudoExpr::var("pairs")),
        },
        PseudoExpr::let_bind(
            "score",
            PseudoExpr::lambda(
                vec!["pairs".to_string(), "needle".to_string()],
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("lookup")),
                    args: vec![PseudoExpr::var("pairs")].into(),
                },
            ),
            PseudoExpr::Lambda {
                params: vec![
                    "redeemer".to_string().into(),
                    "script_context".to_string().into(),
                ],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("score")),
                    args: vec![
                        PseudoExpr::var("redeemer"),
                        PseudoExpr::var("script_context"),
                    ]
                    .into(),
                }),
            },
        ),
    );

    let output = expr.to_pretty();
    let main_pos = output
        .find("fn(redeemer, script_context)")
        .expect("output was missing the root lambda");
    let lookup_pos = output
        .find("rec fn lookup(pairs)")
        .expect("output was missing lookup");
    let score_pos = output
        .find("fn score(pairs, needle)")
        .expect("output was missing score");

    assert!(main_pos < lookup_pos, "output was:\n{}", output);
    assert!(lookup_pos < score_pos, "output was:\n{}", output);
}

#[test]
fn test_nested_let_flattening_not_in_body() {
    // let x = 1 in (let y = 2 in x + y)
    // The body is a Let, but value is NOT a Let -- no flattening needed
    // (body lets are already sequential by nature of how to_doc recurses)
    let body_let = PseudoExpr::let_bind(
        "y",
        PseudoExpr::int(2),
        PseudoExpr::binop(BinaryOp::Add, PseudoExpr::var("x"), PseudoExpr::var("y")),
    );
    let expr = PseudoExpr::let_bind("x", PseudoExpr::int(1), body_let);
    let output = expr.to_pretty();
    // x should come before y since x's value is not a let
    let x_pos = output.find("let x =").unwrap();
    let y_pos = output.find("let y =").unwrap();
    assert!(x_pos < y_pos, "let x before let y, output: {}", output);
}

#[test]
fn test_short_let_bindings_stay_inline() {
    let expr = PseudoExpr::let_bind(
        "policy_id_bytes",
        PseudoExpr::builtin("Data.to_bytes", vec![PseudoExpr::var("policy_id")]),
        PseudoExpr::let_bind(
            "outputs",
            PseudoExpr::builtin(
                "Data.to_list",
                vec![PseudoExpr::field_access(
                    PseudoExpr::var("tx_info"),
                    "outputs".to_string(),
                )],
            ),
            PseudoExpr::var("outputs"),
        ),
    );

    let output = expr.to_pretty();
    let expected = "\
let policy_id_bytes = Data.to_bytes(policy_id)
let outputs = Data.to_list(tx_info.outputs)
outputs";
    assert_eq!(output, expected, "output was:\n{}", output);
}

#[test]
fn test_delay_with_simple_body_stripped() {
    // Standalone Delay is stripped for readability — the surface has no delay keyword
    let expr = PseudoExpr::Delay(PBox::new(PseudoExpr::var("x")));
    assert_eq!(expr.to_pretty(), "x");
}

#[test]
fn test_delay_with_let_body_stripped() {
    // Standalone Delay is stripped — inner let body renders directly
    let expr = PseudoExpr::Delay(PBox::new(PseudoExpr::let_bind(
        "x",
        PseudoExpr::int(1),
        PseudoExpr::var("x"),
    )));

    let expected = "\
let x = 1
x";
    assert_eq!(
        expr.to_pretty(),
        expected,
        "output was:\n{}",
        expr.to_pretty()
    );
}

#[test]
fn test_inline_when_adapter_let_in_lambda_body() {
    let expr = PseudoExpr::let_bind(
        "condition_ok",
        PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("x")),
            subject_name: None,
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(
                        ConstructorShape::unknown_data(0, 2),
                        vec![
                            Binder::from("head".to_string()),
                            Binder::from("tail".to_string()),
                        ],
                    ),
                    PseudoExpr::var("head"),
                ),
                WhenClause::new(WhenPattern::wildcard(), PseudoExpr::error()),
            ],
        },
        PseudoExpr::lambda(
            vec!["arg".to_string()],
            PseudoExpr::apply(
                PseudoExpr::var("condition_ok"),
                vec![PseudoExpr::builtin(
                    "Data.to_map",
                    vec![PseudoExpr::var("arg")],
                )],
            ),
        ),
    );

    let output = expr.to_pretty();
    assert!(
        output.contains("let condition_ok ="),
        "output was:\n{}",
        output
    );
    assert!(
        output.contains("fn(arg) { condition_ok(Data.to_map(arg)) }"),
        "output was:\n{}",
        output
    );
}

#[test]
fn expect_or_fail_flag_preserves_dropped_fail_message() {
    // `when x is { Ctor(head, tail) -> head; _ -> fail @"boom" }`: the
    // default `expect` sugar collapses this to `expect Ctor(..) = x`,
    // DROPPING the `@"boom"` message. The opt-in `expect_or_fail` config
    // re-attaches it as `expect Ctor(..) = x or fail @"boom"`.
    let make_when = || PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 2),
                    vec![
                        Binder::from("head".to_string()),
                        Binder::from("tail".to_string()),
                    ],
                ),
                PseudoExpr::var("head"),
            ),
            WhenClause::new(
                WhenPattern::wildcard(),
                PseudoExpr::error_with_message("boom"),
            ),
        ],
    };

    // Default (flag off): expect sugar fires but drops the fail message.
    let default_out = make_when().to_pretty();
    assert!(
        default_out.contains("expect "),
        "default should render expect sugar, got:\n{default_out}"
    );
    assert!(
        !default_out.contains("or fail"),
        "default must NOT emit `or fail`, got:\n{default_out}"
    );

    // Opt-in (flag on): the dropped fail message is preserved.
    let opt_in_out = make_when().to_pretty_with_config(PrettyConfig {
        render_ctx: crate::decompile::RenderCtx::default().with_expect_or_fail(true),
        ..PrettyConfig::default()
    });
    assert!(
        opt_in_out.contains("or fail @\"boom\""),
        "expect_or_fail must preserve the fail message, got:\n{opt_in_out}"
    );
}

#[test]
fn expect_or_fail_uses_catch_all_fail_message_not_pattern_specific() {
    // Soundness: `when x is { A -> fail @"A"; B(v) -> v; _ -> fail @"D" }`.
    // The `expect B(v) = x or fail @"..."` form represents the CATCH-ALL
    // failure (`x` doesn't match `B`), so it must use the wildcard arm's
    // message (@"D") — NOT the pattern-specific `A -> fail @"A"` arm, a
    // distinct failure condition the expect-collapse already drops.
    let when = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::error_with_message("A"),
            ),
            WhenClause::new(
                WhenPattern::constructor(
                    ConstructorShape::unknown_data(1, 1),
                    vec![Binder::from("v".to_string())],
                ),
                PseudoExpr::var("v"),
            ),
            WhenClause::new(WhenPattern::wildcard(), PseudoExpr::error_with_message("D")),
        ],
    };

    let out = when.to_pretty_with_config(PrettyConfig {
        render_ctx: crate::decompile::RenderCtx::default().with_expect_or_fail(true),
        ..PrettyConfig::default()
    });
    assert!(
        out.contains("or fail @\"D\"") && !out.contains("@\"A\""),
        "must attach the catch-all message @\"D\", not the pattern-specific @\"A\", got:\n{out}"
    );
}

#[test]
fn expect_or_fail_preserves_sole_complement_fail_message() {
    // `when x is { Some(v) -> v; None -> fail @"msg" }` — the `None` arm
    // is a SPECIFIC pattern (not a literal wildcard) but is the exhaustive
    // complement of `Some`, so its message DOES represent the expect failure.
    // The sole-message rule must preserve it.
    let when = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 1),
                    vec![Binder::from("v".to_string())],
                ),
                PseudoExpr::var("v"),
            ),
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                PseudoExpr::error_with_message("nope"),
            ),
        ],
    };

    let out = when.to_pretty_with_config(PrettyConfig {
        render_ctx: crate::decompile::RenderCtx::default().with_expect_or_fail(true),
        ..PrettyConfig::default()
    });
    assert!(
        out.contains("or fail @\"nope\""),
        "sole specific-pattern complement fail message must be preserved, got:\n{out}"
    );
}

#[test]
fn expect_or_fail_preserves_empty_string_fail_message() {
    // `Some("")` IS a message (renders `fail @""`, matching the
    // `PseudoExpr::Error` renderer) — distinct from a message-LESS `fail`
    // (`Error { message: None }`). So `_ -> fail @""` yields `or fail @""`.
    let when = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 1),
                    vec![Binder::from("v".to_string())],
                ),
                PseudoExpr::var("v"),
            ),
            WhenClause::new(WhenPattern::wildcard(), PseudoExpr::error_with_message("")),
        ],
    };

    let out = when.to_pretty_with_config(PrettyConfig {
        render_ctx: crate::decompile::RenderCtx::default().with_expect_or_fail(true),
        ..PrettyConfig::default()
    });
    assert!(
        out.contains("or fail @\"\""),
        "empty-string fail message must render `or fail @\"\"`, got:\n{out}"
    );
}

#[test]
fn expect_or_fail_omits_clause_when_fail_arm_has_no_message() {
    // A message-less `fail` arm has nothing to preserve — even with the
    // flag on, no `or fail` clause is appended (matches default sugar).
    let when = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 2),
                    vec![
                        Binder::from("head".to_string()),
                        Binder::from("tail".to_string()),
                    ],
                ),
                PseudoExpr::var("head"),
            ),
            WhenClause::new(WhenPattern::wildcard(), PseudoExpr::error()),
        ],
    };

    let out = when.to_pretty_with_config(PrettyConfig {
        render_ctx: crate::decompile::RenderCtx::default().with_expect_or_fail(true),
        ..PrettyConfig::default()
    });
    assert!(
        out.contains("expect ") && !out.contains("or fail"),
        "message-less fail arm must not produce `or fail`, got:\n{out}"
    );
}

#[test]
fn test_when_adapter_not_inlined_when_subject_var_used_in_clause_body() {
    let expr = PseudoExpr::let_bind(
        "condition_ok",
        PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("x")),
            subject_name: None,
            clauses: vec![WhenClause::new(
                WhenPattern::wildcard(),
                PseudoExpr::var("x"),
            )],
        },
        PseudoExpr::lambda(
            vec!["arg".to_string()],
            PseudoExpr::apply(
                PseudoExpr::var("condition_ok"),
                vec![PseudoExpr::var("arg")],
            ),
        ),
    );

    let output = expr.to_pretty();
    assert!(
        output.contains("let condition_ok ="),
        "output was:\n{}",
        output
    );
}

#[test]
fn test_nested_let_flattening_preserves_inner_types_when_show_types() {
    let expr = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Let {
            name: "b".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::bool(true)),
            body: PBox::new(PseudoExpr::var("b")),
        }),
        body: PBox::new(PseudoExpr::var("a")),
    };

    let output = expr.to_pretty_with_config(PrettyConfig {
        show_types: true,
        ..PrettyConfig::default()
    });
    // Type annotations come from the type environment only; without one,
    // only literal types (Bool for True) are visible.
    let expected = "\
let b = True
let a = b
a";
    assert_eq!(output, expected, "output was:\n{}", output);
}

#[test]
fn test_chained_else_if_two_levels() {
    // if A { B } else { if C { D } else { E } }
    // should render as flat else-if chain
    let expr = PseudoExpr::if_then_else(
        PseudoExpr::var("a"),
        PseudoExpr::int(1),
        PseudoExpr::if_then_else(PseudoExpr::var("b"), PseudoExpr::int(2), PseudoExpr::int(3)),
    );
    let output = expr.to_pretty();
    let expected = "\
if a {
  1
} else if b {
  2
} else {
  3
}";
    assert_eq!(output, expected, "output was:\n{}", output);
}

#[test]
fn test_chained_else_if_three_levels() {
    // if A { 1 } else { if B { 2 } else { if C { 3 } else { 4 } } }
    // should render as flat 3-level else-if chain
    let expr = PseudoExpr::if_then_else(
        PseudoExpr::var("a"),
        PseudoExpr::int(1),
        PseudoExpr::if_then_else(
            PseudoExpr::var("b"),
            PseudoExpr::int(2),
            PseudoExpr::if_then_else(PseudoExpr::var("c"), PseudoExpr::int(3), PseudoExpr::int(4)),
        ),
    );
    let output = expr.to_pretty();
    let expected = "\
if a {
  1
} else if b {
  2
} else if c {
  3
} else {
  4
}";
    assert_eq!(output, expected, "output was:\n{}", output);
}

#[test]
fn test_simple_if_no_chain() {
    // Simple if/else with no nesting should still render correctly
    let expr =
        PseudoExpr::if_then_else(PseudoExpr::var("x"), PseudoExpr::int(1), PseudoExpr::int(0));
    let output = expr.to_pretty();
    let expected = "\
if x {
  1
} else {
  0
}";
    assert_eq!(output, expected, "output was:\n{}", output);
}

#[test]
fn test_sorted_assoc_lookup_nested_if_renders_as_else_if_chain() {
    let expr = PseudoExpr::if_then_else(
        PseudoExpr::BinOp {
            op: BinaryOp::Lte,
            left: PBox::new(PseudoExpr::var("needle")),
            right: PBox::new(PseudoExpr::var("fst")),
        },
        PseudoExpr::if_then_else(
            PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::var("needle")),
                right: PBox::new(PseudoExpr::var("fst")),
            },
            PseudoExpr::constr_known(KnownConstructor::Some, vec![PseudoExpr::var("value")]),
            PseudoExpr::constr_known(KnownConstructor::None, vec![]),
        ),
        PseudoExpr::var("recurse"),
    );

    let output = expr.to_pretty();
    let expected = "\
if needle == fst {
  Some(value)
} else if needle < fst {
  None
} else {
  recurse
}";
    assert_eq!(output, expected, "output was:\n{}", output);
}

#[test]
fn test_byte_array_printable_ascii_renders_as_text_literal() {
    let expr = PseudoExpr::byte_array(b"ADA DOGE".to_vec());
    assert_eq!(expr.to_pretty(), "\"ADA DOGE\"");
}

#[test]
fn test_byte_array_protocol_params_render_as_text_literal() {
    let expr = PseudoExpr::byte_array(b"protocol-params".to_vec());
    assert_eq!(expr.to_pretty(), "\"protocol-params\"");
}

#[test]
fn test_byte_array_invalid_renders_as_text_literal() {
    let expr = PseudoExpr::byte_array(b"Invalid".to_vec());
    assert_eq!(expr.to_pretty(), "\"Invalid\"");
}

#[test]
fn test_byte_array_non_printable_stays_hex() {
    // 0x00, 0xFF are not printable ASCII
    let expr = PseudoExpr::byte_array(vec![0x00, 0xFF]);
    assert_eq!(expr.to_pretty(), "#\"00ff\"");
}

#[test]
fn test_byte_array_empty_stays_hex() {
    let expr = PseudoExpr::byte_array(vec![]);
    assert_eq!(expr.to_pretty(), "#\"\"");
}

#[test]
fn test_byte_array_mixed_printable_and_non_printable_stays_hex() {
    // 'A' (0x41) is printable, 0x00 is not
    let expr = PseudoExpr::byte_array(vec![0x41, 0x00]);
    assert_eq!(expr.to_pretty(), "#\"4100\"");
}

#[test]
fn test_byte_array_with_quotes_escapes_properly() {
    // String with a double quote character inside
    let expr = PseudoExpr::byte_array(b"say \"hello\"".to_vec());
    assert_eq!(expr.to_pretty(), "\"say \\\"hello\\\"\"");
}

#[test]
fn test_byte_array_boundary_printable_chars() {
    // Test boundary: 0x20 (space) and 0x7E (~) are both printable
    let expr = PseudoExpr::byte_array(vec![0x20, 0x7E]);
    assert_eq!(expr.to_pretty(), "\" ~\"");
}

#[test]
fn test_byte_array_just_below_boundary_stays_hex() {
    // 0x1F (unit separator) is just below printable range
    let expr = PseudoExpr::byte_array(vec![0x1F]);
    assert_eq!(expr.to_pretty(), "#\"1f\"");
}

#[test]
fn test_byte_array_just_above_boundary_stays_hex() {
    // 0x7F (DEL) is just above printable range
    let expr = PseudoExpr::byte_array(vec![0x7F]);
    assert_eq!(expr.to_pretty(), "#\"7f\"");
}

#[test]
fn test_pseudo_data_bytestring_printable_ascii_renders_as_text_literal() {
    let data = PseudoData::ByteString(b"hello".to_vec());
    let expr = PseudoExpr::Data(Box::new(data));
    assert_eq!(expr.to_pretty(), "\"hello\"");
}

#[test]
fn test_pseudo_data_bytestring_non_printable_stays_hex() {
    let data = PseudoData::ByteString(vec![0x00, 0x01, 0x02]);
    let expr = PseudoExpr::Data(Box::new(data));
    assert_eq!(expr.to_pretty(), "#\"000102\"");
}

#[test]
fn test_byte_array_in_builtin_call_renders_as_text_literal() {
    // ByteArray.to_data(#"496e76616c6964") should render the inner byte array as @"Invalid"
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("ByteArray.to_data"),
        args: vec![PseudoExpr::byte_array(b"Invalid".to_vec())].into(),
    };
    let output = expr.to_pretty();
    assert_eq!(output, "ByteArray.to_data(\"Invalid\")");
}

#[test]
fn test_seq_single_flattened() {
    // seq(A, B) should render as two statements separated by newline
    let expr = PseudoExpr::builtin("seq", vec![PseudoExpr::var("a"), PseudoExpr::var("b")]);
    let output = expr.to_pretty();
    assert_eq!(output, "a\nb", "output was: {}", output);
}

#[test]
fn test_seq_nested_chain_flattened() {
    // seq(A, seq(B, seq(C, D))) should render as four newline-separated statements
    let expr = PseudoExpr::builtin(
        "seq",
        vec![
            PseudoExpr::var("a"),
            PseudoExpr::builtin(
                "seq",
                vec![
                    PseudoExpr::var("b"),
                    PseudoExpr::builtin("seq", vec![PseudoExpr::var("c"), PseudoExpr::var("d")]),
                ],
            ),
        ],
    );
    let output = expr.to_pretty();
    assert_eq!(output, "a\nb\nc\nd", "output was: {}", output);
}

#[test]
fn test_seq_with_trace_flattened() {
    // seq(trace @"" check1, seq(trace @"" check2, result))
    // should flatten to sequential trace statements
    let trace1 = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::string("")),
        value: PBox::new(PseudoExpr::var("check1")),
    };
    let trace2 = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::string("")),
        value: PBox::new(PseudoExpr::var("check2")),
    };
    let expr = PseudoExpr::builtin(
        "seq",
        vec![
            trace1,
            PseudoExpr::builtin("seq", vec![trace2, PseudoExpr::var("result")]),
        ],
    );
    let output = expr.to_pretty();
    let expected = "trace @\"\": check1\ntrace @\"\": check2\nresult";
    assert_eq!(output, expected, "output was:\n{}", output);
}

#[test]
fn test_seq_non_nested_no_flatten() {
    // seq with != 2 args should render as regular builtin call
    let expr = PseudoExpr::builtin("seq", vec![PseudoExpr::var("a")]);
    let output = expr.to_pretty();
    assert_eq!(output, "seq(a)", "output was: {}", output);
}

#[test]
fn test_seq_apply_form_flattened() {
    // Apply(BuiltinCall("seq", []), [A, B]) should also flatten
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::builtin("seq", vec![])),
        args: vec![PseudoExpr::var("a"), PseudoExpr::var("b")].into(),
    };
    let output = expr.to_pretty();
    assert_eq!(output, "a\nb", "output was: {}", output);
}

#[test]
fn test_expect_chain_renders_with_expect_keyword() {
    // Rendered output must use the surface keyword `expect`, not the
    // internal helper symbol `expect!`, which the AST keeps as a
    // non-identifier marker.
    //
    // Shape: Apply(Var("expect!"), [cond1, Apply(Var("expect!"), [cond2, value])])
    // Rendered: `expect cond1\nexpect cond2\nvalue`
    let inner = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![PseudoExpr::var("cond2"), PseudoExpr::var("value")].into(),
    };
    let chain = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![PseudoExpr::var("cond1"), inner].into(),
    };
    let output = chain.to_pretty();
    assert!(
        !output.contains("expect!"),
        "rendered output must not contain the internal `expect!` marker: {output}"
    );
    assert!(
        output.contains("expect cond1"),
        "expected rendered `expect cond1`, got: {output}"
    );
    assert!(
        output.contains("expect cond2"),
        "expected rendered `expect cond2`, got: {output}"
    );
}

#[test]
fn test_seq_mixed_forms_flattened() {
    // BuiltinCall("seq", [A, Apply(BuiltinCall("seq", []), [B, C])])
    // should flatten across both forms
    let inner = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::builtin("seq", vec![])),
        args: vec![PseudoExpr::var("b"), PseudoExpr::var("c")].into(),
    };
    let expr = PseudoExpr::builtin("seq", vec![PseudoExpr::var("a"), inner]);
    let output = expr.to_pretty();
    assert_eq!(output, "a\nb\nc", "output was: {}", output);
}

#[test]
fn test_collect_seq_chain_helper() {
    // Test the collect_seq_chain helper directly
    let expr = PseudoExpr::builtin(
        "seq",
        vec![
            PseudoExpr::int(1),
            PseudoExpr::builtin("seq", vec![PseudoExpr::int(2), PseudoExpr::int(3)]),
        ],
    );
    let chain = collect_seq_chain(&expr);
    assert_eq!(chain.len(), 3, "expected 3 statements in chain");
    assert_eq!(*chain[0], PseudoExpr::int(1));
    assert_eq!(*chain[1], PseudoExpr::int(2));
    assert_eq!(*chain[2], PseudoExpr::int(3));
}

#[test]
fn test_trace_if_false_simple_var() {
    // s8 || trace @"nft_check ? False" False -> s8?
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: PBox::new(PseudoExpr::var("s8")),
        right: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::String("nft_check ? False".to_string())),
            value: PBox::new(PseudoExpr::Bool(false)),
        }),
    };
    let output = expr.to_pretty();
    assert_eq!(output, "s8?", "output was: {}", output);
}

#[test]
fn test_trace_if_false_complex_expr() {
    // (x == 1) || trace @"msg" False -> (x == 1)?
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::var("x")),
            right: PBox::new(PseudoExpr::int(1)),
        }),
        right: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::String("check ? False".to_string())),
            value: PBox::new(PseudoExpr::Bool(false)),
        }),
    };
    let output = expr.to_pretty();
    assert_eq!(output, "(x == 1)?", "output was: {}", output);
}

#[test]
fn test_trace_if_false_function_call() {
    // is_valid(x) || trace @"msg" False -> is_valid(x)?
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("is_valid")),
            args: vec![PseudoExpr::var("x")].into(),
        }),
        right: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::String("is_valid ? False".to_string())),
            value: PBox::new(PseudoExpr::Bool(false)),
        }),
    };
    let output = expr.to_pretty();
    assert_eq!(output, "is_valid(x)?", "output was: {}", output);
}

#[test]
fn test_trace_if_false_not_triggered_when_value_is_not_false() {
    // x || trace @"msg" True should NOT be converted (value is True, not False)
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: PBox::new(PseudoExpr::var("x")),
        right: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::String("msg".to_string())),
            value: PBox::new(PseudoExpr::Bool(true)),
        }),
    };
    let output = expr.to_pretty();
    // Should remain as regular ||
    assert!(output.contains("||"), "output was: {}", output);
}

#[test]
fn test_trace_if_false_not_triggered_for_and() {
    // x && trace @"msg" False should NOT trigger trace_if_false (that's for ||)
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(PseudoExpr::var("x")),
        right: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::String("msg".to_string())),
            value: PBox::new(PseudoExpr::Bool(false)),
        }),
    };
    let output = expr.to_pretty();
    // Should remain as regular &&
    assert!(output.contains("&&"), "output was: {}", output);
}

#[test]
fn test_trace_if_true_simple() {
    // x && trace @"msg" True -> !x?
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(PseudoExpr::var("x")),
        right: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::String("msg".to_string())),
            value: PBox::new(PseudoExpr::Bool(true)),
        }),
    };
    let output = expr.to_pretty();
    assert_eq!(output, "!x?", "output was: {}", output);
}

#[test]
fn test_trace_if_true_binop_expr() {
    // (a && b) && trace @"msg" True -> !(a && b)?
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::And,
            left: PBox::new(PseudoExpr::var("a")),
            right: PBox::new(PseudoExpr::var("b")),
        }),
        right: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::String("msg".to_string())),
            value: PBox::new(PseudoExpr::Bool(true)),
        }),
    };
    let output = expr.to_pretty();
    assert_eq!(output, "!(a && b)?", "output was: {}", output);
}

#[test]
fn test_trace_if_false_with_if_condition() {
    // (if a { b } else { c }) || trace @"... ? False" False -> (if a { b } else { c })?
    // (the `?`-auto-format message collapses; a custom message would be kept).
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: PBox::new(PseudoExpr::if_then_else(
            PseudoExpr::var("a"),
            PseudoExpr::var("b"),
            PseudoExpr::var("c"),
        )),
        right: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::String("branch ? False".to_string())),
            value: PBox::new(PseudoExpr::Bool(false)),
        }),
    };
    let output = expr.to_pretty();
    assert!(output.starts_with("(if a"), "output was: {}", output);
    assert!(output.ends_with(")?"), "output was: {}", output);
}

// ===== Shadowed let disambiguation tests =====

#[test]
fn test_shadowed_let_simple_body_chain() {
    // let x = 1 in (let x = x + 1 in x)
    // Should render as:
    //   let x = 1
    //   let x_2 = x + 1
    //   x_2
    let expr = PseudoExpr::let_bind(
        "x",
        PseudoExpr::int(1),
        PseudoExpr::let_bind(
            "x",
            PseudoExpr::binop(BinaryOp::Add, PseudoExpr::var("x"), PseudoExpr::int(1)),
            PseudoExpr::var("x"),
        ),
    );
    let output = expr.to_pretty();
    assert!(
        output.contains("let x =") || output.contains("let count ="),
        "output was:\n{}",
        output
    );
    assert!(
        output.contains("let x_2 =") || output.contains("let count_2 ="),
        "output was:\n{}",
        output
    );
    assert!(
        output.contains("x + 1") || output.contains("count + 1"),
        "output was:\n{}",
        output
    );
    assert!(
        output.trim().ends_with("x_2") || output.trim().ends_with("count_2"),
        "output was:\n{}",
        output
    );
}

#[test]
fn test_shadowed_let_triple() {
    // let x = 1 in (let x = x + 1 in (let x = x * 2 in x))
    // Should render as:
    //   let x = 1
    //   let x_2 = x + 1
    //   let x_3 = x_2 * 2
    //   x_3
    let expr = PseudoExpr::let_bind(
        "x",
        PseudoExpr::int(1),
        PseudoExpr::let_bind(
            "x",
            PseudoExpr::binop(BinaryOp::Add, PseudoExpr::var("x"), PseudoExpr::int(1)),
            PseudoExpr::let_bind(
                "x",
                PseudoExpr::binop(BinaryOp::Mul, PseudoExpr::var("x"), PseudoExpr::int(2)),
                PseudoExpr::var("x"),
            ),
        ),
    );
    let output = expr.to_pretty();
    assert!(
        output.contains("let x =") || output.contains("let count ="),
        "output was:\n{}",
        output
    );
    assert!(
        output.contains("let x_2 =") || output.contains("let count_2 ="),
        "output was:\n{}",
        output
    );
    assert!(
        output.contains("let x_3 =") || output.contains("let count_3 ="),
        "output was:\n{}",
        output
    );
    assert!(
        output.contains("x + 1") || output.contains("count + 1"),
        "output was:\n{}",
        output
    );
    assert!(
        output.contains("x_2 * 2") || output.contains("count_2 * 2"),
        "output was:\n{}",
        output
    );
    assert!(
        output.trim().ends_with("x_3") || output.trim().ends_with("count_3"),
        "output was:\n{}",
        output
    );
}

#[test]
fn test_shadowed_let_with_field_access() {
    // let x_34 = y.fields in (let x_34 = x_34[0].fields in x_34[0])
    let expr = PseudoExpr::let_bind(
        "x_34",
        PseudoExpr::field_access(PseudoExpr::var("y"), "fields".to_string()),
        PseudoExpr::let_bind(
            "x_34",
            PseudoExpr::field_access(
                PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::var("x_34")),
                    index: 0,
                },
                "fields".to_string(),
            ),
            PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::var("x_34")),
                index: 0,
            },
        ),
    );
    let output = expr.to_pretty();
    // First binding keeps original name
    assert!(output.contains("let x_34 ="), "output was:\n{}", output);
    // Second binding gets renamed
    assert!(output.contains("let x_34_2 ="), "output was:\n{}", output);
    // The second binding's value still references the original x_34. With
    // compilable-data-access OFF (the default), `.fields` and `[0]` stay the
    // readable pseudo, giving `x_34[0].fields`; ON it lowers to
    // `builtin.un_constr_data(x_34[0]).2nd`.
    assert!(output.contains("x_34[0].fields"), "output was:\n{}", output);
    // The final expression references the renamed x_34_2 — disambiguation
    // rewires the shadowed reference — and a bare-Var index stays bracketed.
    assert!(output.contains("x_34_2[0]"), "output was:\n{}", output);
}

#[test]
fn test_no_shadowing_different_names() {
    // let x = 1 in (let y = x + 1 in y)
    // No shadowing, names should remain unchanged
    let expr = PseudoExpr::let_bind(
        "x",
        PseudoExpr::int(1),
        PseudoExpr::let_bind(
            "y",
            PseudoExpr::binop(BinaryOp::Add, PseudoExpr::var("x"), PseudoExpr::int(1)),
            PseudoExpr::var("y"),
        ),
    );
    let output = expr.to_pretty();
    assert!(output.contains("let x ="), "output was:\n{}", output);
    assert!(!output.contains("_2"), "output was:\n{}", output);
}

#[test]
fn test_shadowed_let_in_lambda_body_independent() {
    // let x = 1 in fn(y) { let x = 2 in x }
    // The lambda-body let is a different scope, rendered at a deeper
    // indent, but disambiguation still applies because x is in scope.
    let expr = PseudoExpr::let_bind(
        "x",
        PseudoExpr::int(1),
        PseudoExpr::Lambda {
            params: vec!["y".to_string().into()],
            body: PBox::new(PseudoExpr::let_bind(
                "x",
                PseudoExpr::int(2),
                PseudoExpr::var("x"),
            )),
        },
    );
    let output = expr.to_pretty();
    // The naming heuristic may rename `x` from its value (e.g. to `check`);
    // the invariant is only that the inner binding gets a distinct name.
    let lines: Vec<&str> = output.lines().collect();
    let let_lines: Vec<&&str> = lines
        .iter()
        .filter(|l| l.trim_start().starts_with("let "))
        .collect();
    assert!(
        let_lines.len() >= 2,
        "expected at least 2 let bindings, output was:\n{}",
        output
    );
}

#[test]
fn test_rename_var_in_expr_basic() {
    let expr = PseudoExpr::var("x");
    let result = crate::decompile::debug_rename_render_var_in_expr(&expr, "x", "x_2");
    assert_eq!(result, PseudoExpr::var("x_2"));
}

#[test]
fn test_rename_var_in_expr_no_match() {
    let expr = PseudoExpr::var("y");
    let result = crate::decompile::debug_rename_render_var_in_expr(&expr, "x", "x_2");
    assert_eq!(result, PseudoExpr::var("y"));
}

#[test]
fn test_rename_var_in_expr_stops_at_let_rebind() {
    // let x = (uses old x) in (should NOT rename x here)
    let expr = PseudoExpr::let_bind(
        "x",
        PseudoExpr::var("x"), // value uses old x -> should rename
        PseudoExpr::var("x"), // body has new x -> should NOT rename
    );
    let result = crate::decompile::debug_rename_render_var_in_expr(&expr, "x", "x_2");
    match &result {
        PseudoExpr::Let { value, body, .. } => {
            // Value should have x renamed to x_2
            assert_eq!(**value, PseudoExpr::var("x_2"));
            // Body should keep x (shadowed by this let)
            assert_eq!(**body, PseudoExpr::var("x"));
        }
        _ => panic!("Expected Let"),
    }
}

#[test]
fn test_rename_var_in_expr_stops_at_lambda_shadow() {
    // fn(x) { x } -- lambda param shadows, don't rename inside
    let expr = PseudoExpr::Lambda {
        params: vec!["x".to_string().into()],
        body: PBox::new(PseudoExpr::var("x")),
    };
    let result = crate::decompile::debug_rename_render_var_in_expr(&expr, "x", "x_2");
    // Should be unchanged since x is shadowed by the lambda param
    assert_eq!(result, expr);
}

#[test]
fn test_final_types_driven_type_annotation_on_let() {
    // Type annotations flow through
    // `with_final_types(FinalTypeTable)` rather than the legacy
    // `with_env(TypeEnvironment)`.
    use crate::decompile::final_type_table::FinalTypeTable;

    let var_id = crate::pseudo::var_id::VarId::from_raw(100);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(var_id),
        value: PBox::new(PseudoExpr::int(42)),
        body: PBox::new(PseudoExpr::var_with_id("x", var_id)),
    };

    let config = PrettyConfig {
        show_types: true,
        ..Default::default()
    };

    let without_table = PrettyPrinter::with_config(config.clone()).print(&expr);
    assert!(
        !without_table.contains(": Int"),
        "should have no annotation without final_types: {without_table}"
    );

    let mut final_types = FinalTypeTable::new();
    final_types.bind_var(var_id, Rc::new(PseudoType::Int));
    final_types.freeze();
    let with_table = PrettyPrinter::with_config(config)
        .with_final_types(Rc::new(final_types))
        .print(&expr);
    assert!(
        with_table.contains("x: Int"),
        "final_types-driven annotation should appear: {with_table}"
    );
}

#[test]
fn p2_2_slice_b_function_type_renders_unknown_as_underscore() {
    // A `Function { params: [Unknown], ret: Unknown }` binding must
    // render as `fn(_) -> _`, not the structurally meaningless
    // `fn(Data) -> Data` the `Display` impl would produce.
    use crate::decompile::final_type_table::FinalTypeTable;

    let var_id = crate::pseudo::var_id::VarId::from_raw(2200);
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(var_id),
        value: PBox::new(PseudoExpr::var("g")),
        body: PBox::new(PseudoExpr::var_with_id("f", var_id)),
    };

    let mut final_types = FinalTypeTable::new();
    final_types.bind_var(
        var_id,
        Rc::new(PseudoType::Function {
            params: vec![Rc::new(PseudoType::Unknown)],
            ret: Rc::new(PseudoType::Unknown),
        }),
    );
    final_types.freeze();

    let config = PrettyConfig {
        show_types: true,
        ..Default::default()
    };
    let rendered = PrettyPrinter::with_config(config)
        .with_final_types(Rc::new(final_types))
        .print(&expr);

    assert!(
        rendered.contains("f: fn(_) -> _"),
        "expected `fn(_) -> _` annotation, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("fn(Data) -> Data"),
        "Function children must render Unknown as `_`, not `Data`:\n{rendered}"
    );
}

#[test]
fn p2_2_slice_b_nested_function_type_preserves_concrete_inner() {
    // Mixed Function: concrete params keep their Display
    // rendering; only Unknown swaps to `_`.
    use crate::decompile::final_type_table::FinalTypeTable;

    let var_id = crate::pseudo::var_id::VarId::from_raw(2201);
    let expr = PseudoExpr::Let {
        name: "h".to_string(),
        id: Some(var_id),
        value: PBox::new(PseudoExpr::var("g")),
        body: PBox::new(PseudoExpr::var_with_id("h", var_id)),
    };

    let mut final_types = FinalTypeTable::new();
    final_types.bind_var(
        var_id,
        Rc::new(PseudoType::Function {
            params: vec![Rc::new(PseudoType::Int), Rc::new(PseudoType::Unknown)],
            ret: Rc::new(PseudoType::Bool),
        }),
    );
    final_types.freeze();

    let config = PrettyConfig {
        show_types: true,
        ..Default::default()
    };
    let rendered = PrettyPrinter::with_config(config)
        .with_final_types(Rc::new(final_types))
        .print(&expr);

    assert!(
        rendered.contains("h: fn(Int, _) -> Bool"),
        "expected `fn(Int, _) -> Bool` annotation, got:\n{rendered}"
    );
}

#[test]
fn p2_2_slice_b_function_inside_list_wrapper_recurses_for_underscore() {
    // A Function nested in a wrapper type like `List<...>` must
    // also render its Unknown children as `_`, not delegate to
    // `Display`, which would produce `Data`.
    use crate::decompile::final_type_table::FinalTypeTable;

    let var_id = crate::pseudo::var_id::VarId::from_raw(2202);
    let expr = PseudoExpr::Let {
        name: "callbacks".to_string(),
        id: Some(var_id),
        value: PBox::new(PseudoExpr::var("xs")),
        body: PBox::new(PseudoExpr::var_with_id("callbacks", var_id)),
    };

    let mut final_types = FinalTypeTable::new();
    final_types.bind_var(
        var_id,
        Rc::new(PseudoType::List(Rc::new(PseudoType::Function {
            params: vec![Rc::new(PseudoType::Unknown)],
            ret: Rc::new(PseudoType::Unknown),
        }))),
    );
    final_types.freeze();

    let config = PrettyConfig {
        show_types: true,
        ..Default::default()
    };
    let rendered = PrettyPrinter::with_config(config)
        .with_final_types(Rc::new(final_types))
        .print(&expr);

    assert!(
        rendered.contains("callbacks: List<fn(_) -> _>"),
        "Function nested inside List must recurse for `_`, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("fn(Data) -> Data"),
        "wrapper recursion must not leak `Data`:\n{rendered}"
    );
}

mod when_body_groups {
    use super::*;
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;

    fn ctor(tag: usize, body: PseudoExpr) -> WhenClause {
        WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag,
                fields: vec![],
                shape: ConstructorShape::unknown_data(tag, 0),
            },
            guard: None,
            body,
        }
    }

    fn lit(n: i64, body: PseudoExpr) -> WhenClause {
        WhenClause {
            pattern: WhenPattern::Literal(PseudoExpr::int(n)),
            guard: None,
            body,
        }
    }

    /// Ctor arms with equal bodies merge across a disjoint-tag
    /// constructor span: `0->a; 1->b; 2->a` groups as `[[0,2],[1]]`.
    #[test]
    fn non_adjacent_disjoint_ctors_merge() {
        let a = || PseudoExpr::var("a");
        let clauses = vec![ctor(0, a()), ctor(1, PseudoExpr::var("b")), ctor(2, a())];
        assert_eq!(
            compute_when_body_groups(&clauses),
            vec![vec![0, 2], vec![1]]
        );
    }

    /// A non-Constructor pattern in the span (a Literal can overlap a
    /// constructor subject in Data-land) vetoes the hoist.
    #[test]
    fn non_adjacent_veto_literal_in_span() {
        let a = || PseudoExpr::var("a");
        let clauses = vec![ctor(0, a()), lit(5, PseudoExpr::var("b")), ctor(2, a())];
        assert_eq!(
            compute_when_body_groups(&clauses),
            vec![vec![0], vec![1], vec![2]]
        );
    }

    /// A binder-carrying constructor IN THE SPAN is fine (only tag
    /// disjointness matters for arms the hoisted value can't match).
    #[test]
    fn non_adjacent_merge_across_binder_ctor() {
        let a = || PseudoExpr::var("a");
        let mid = WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 1,
                fields: vec![crate::pseudo::ast::Binder::new(
                    "x".to_string(),
                    crate::pseudo::var_id::VarId::new(900),
                )],
                shape: ConstructorShape::unknown_data(1, 1),
            },
            guard: None,
            body: PseudoExpr::var("b"),
        };
        let clauses = vec![ctor(0, a()), mid, ctor(2, a())];
        assert_eq!(
            compute_when_body_groups(&clauses),
            vec![vec![0, 2], vec![1]]
        );
    }

    /// Adjacent grouping of binder-free non-constructor patterns is
    /// preserved (literals still merge when adjacent).
    #[test]
    fn adjacent_literals_still_merge() {
        let a = || PseudoExpr::var("a");
        let clauses = vec![lit(0, a()), lit(1, a()), ctor(2, PseudoExpr::var("b"))];
        assert_eq!(
            compute_when_body_groups(&clauses),
            vec![vec![0, 1], vec![2]]
        );
    }

    /// A SPAN clause carrying the candidate's tag vetoes the hoist (a
    /// value matching the candidate would be intercepted by that arm).
    #[test]
    fn non_adjacent_veto_same_tag_in_span() {
        let a = || PseudoExpr::var("a");
        let clauses = vec![ctor(0, a()), ctor(1, PseudoExpr::var("b")), ctor(1, a())];
        assert_eq!(
            compute_when_body_groups(&clauses),
            vec![vec![0], vec![1], vec![2]]
        );
    }

    /// Same-tag candidate never merges (not disjoint with the leader).
    #[test]
    fn non_adjacent_veto_same_tag() {
        let a = || PseudoExpr::var("a");
        let clauses = vec![ctor(0, a()), ctor(1, PseudoExpr::var("b")), ctor(0, a())];
        assert_eq!(
            compute_when_body_groups(&clauses),
            vec![vec![0], vec![1], vec![2]]
        );
    }

    /// A guarded clause in the span does not block the hoist (the value
    /// can't match its disjoint-tag pattern, so its guard never runs),
    /// but a guarded CANDIDATE/LEADER never merges.
    #[test]
    fn guards_block_membership_not_span() {
        let a = || PseudoExpr::var("a");
        let mut guarded_mid = ctor(1, PseudoExpr::var("b"));
        guarded_mid.guard = Some(PseudoExpr::Bool(true));
        let clauses = vec![ctor(0, a()), guarded_mid, ctor(2, a())];
        assert_eq!(
            compute_when_body_groups(&clauses),
            vec![vec![0, 2], vec![1]]
        );

        let mut guarded_candidate = ctor(2, a());
        guarded_candidate.guard = Some(PseudoExpr::Bool(true));
        let clauses = vec![
            ctor(0, a()),
            ctor(1, PseudoExpr::var("b")),
            guarded_candidate,
        ];
        assert_eq!(
            compute_when_body_groups(&clauses),
            vec![vec![0], vec![1], vec![2]]
        );
    }
}

#[test]
fn value_is_definitely_not_function_discriminates() {
    use super::value_is_definitely_not_function as not_fn;
    let v = PseudoExpr::var("a");
    // Data aggregates / literals: definitely not functions.
    assert!(not_fn(&PseudoExpr::Pair(
        PBox::new(v.clone()),
        PBox::new(v.clone())
    )));
    assert!(not_fn(&PseudoExpr::Tuple(
        (vec![v.clone(), v.clone()]).into()
    )));
    assert!(not_fn(&PseudoExpr::List {
        elements: vec![].into(),
        tail: None
    }));
    assert!(not_fn(&PseudoExpr::int(0)));
    assert!(not_fn(&PseudoExpr::Bool(true)));
    // Could be / return a function — must NOT be classified non-function.
    assert!(!not_fn(&v));
    assert!(!not_fn(&PseudoExpr::Lambda {
        params: vec![],
        body: PBox::new(v.clone()),
    }));
    assert!(!not_fn(&PseudoExpr::FieldAccess {
        record: PBox::new(v.clone()),
        selector: crate::pseudo::FieldSelector::PairFst,
    }));
    assert!(!not_fn(&PseudoExpr::Apply {
        function: PBox::new(v.clone()),
        args: vec![].into(),
    }));
    // Structural fail-labels: an applied fail-label binder gets a solver
    // Function type, but the value provably diverges — suppress.
    assert!(not_fn(&PseudoExpr::Error {
        message: Some("PT1".to_string()),
    }));
    assert!(not_fn(&PseudoExpr::Error { message: None }));
    assert!(not_fn(&PseudoExpr::Delay(PBox::new(PseudoExpr::Error {
        message: Some("m".to_string()),
    }))));
    assert!(not_fn(&PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::String("m".to_string())),
        value: PBox::new(PseudoExpr::Error { message: None }),
    }));
    // A Trace around a NON-Error value stays annotatable.
    assert!(!not_fn(&PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::String("m".to_string())),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![],
            body: PBox::new(v.clone()),
        }),
    }));
}

#[test]
fn false_fn_annotation_on_pair_value_is_suppressed() {
    // A binder the solver typed `fn(_) -> _` but bound to a `Pair(..)` literal
    // is a flat lie — drop the annotation. A genuine function value keeps it.
    use crate::decompile::final_type_table::FinalTypeTable;

    let p_id = crate::pseudo::var_id::VarId::new(7401);
    let pair_let = PseudoExpr::Let {
        name: "f_30".to_string(),
        id: Some(p_id),
        value: PBox::new(PseudoExpr::Pair(
            PBox::new(PseudoExpr::var("helper_18")),
            PBox::new(PseudoExpr::var("choose_fst")),
        )),
        body: PBox::new(PseudoExpr::var_with_id("f_30", p_id)),
    };

    let mut final_types = FinalTypeTable::new();
    // Mis-inferred: `fn(_) -> _` on a Pair value.
    final_types.bind_var(
        p_id,
        Rc::new(PseudoType::Function {
            params: vec![Rc::new(PseudoType::Unknown)],
            ret: Rc::new(PseudoType::Unknown),
        }),
    );
    final_types.freeze();

    let config = PrettyConfig {
        show_types: true,
        ..Default::default()
    };
    let rendered = PrettyPrinter::with_config(config)
        .with_final_types(Rc::new(final_types))
        .print(&pair_let);

    assert!(
        rendered.contains("let f_30 = Pair(helper_18, choose_fst)"),
        "the false `fn(_) -> _` annotation on a Pair value must be dropped, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("f_30: fn"),
        "no function annotation should survive on a Pair value, got:\n{rendered}"
    );
}

#[test]
fn p2_2_slice_a_integration_named_fn_does_not_double_function_annotation() {
    // End-to-end invariant: `let f = fn(x) { 0 } in f` rendered
    // with `show_types` and a FinalTypeTable binding `f_id` to
    // `Function { params: [Unknown], ret: Unknown }` must NOT
    // produce the doubled return type `fn f(x) -> fn(_) -> _`.
    // The named-fn renderer unwraps `Function.ret` for the
    // return-type slot; an Unknown ret suppresses it entirely.
    use crate::decompile::final_type_table::FinalTypeTable;

    let f_id = crate::pseudo::var_id::VarId::new(2230);
    let x_id = crate::pseudo::var_id::VarId::new(2231);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::int(0)),
    };
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(lambda),
        body: PBox::new(PseudoExpr::var_with_id("f", f_id)),
    };

    let mut final_types = FinalTypeTable::new();
    final_types.bind_var(
        f_id,
        Rc::new(PseudoType::Function {
            params: vec![Rc::new(PseudoType::Unknown)],
            ret: Rc::new(PseudoType::Unknown),
        }),
    );
    final_types.freeze();

    let config = PrettyConfig {
        show_types: true,
        ..Default::default()
    };
    let rendered = PrettyPrinter::with_config(config)
        .with_final_types(Rc::new(final_types))
        .print(&expr);

    // Doubled annotation regression: `fn f(x) -> fn(_) -> _ { ... }`.
    assert!(
        !rendered.contains("-> fn(_) -> _"),
        "named-fn must unwrap Function.ret for the return-type slot, got:\n{rendered}"
    );
    // The named-fn shape itself is emitted.
    assert!(
        rendered.contains("fn f(x)"),
        "expected named-fn `fn f(x)` shape, got:\n{rendered}"
    );
}

#[test]
fn p2_2_slice_a_integration_named_fn_unwraps_function_ret_to_concrete_type() {
    // A concrete `Function.ret` (e.g. `Int`) becomes the named-fn
    // return type — `fn g(x) -> Int` — not the wrapped
    // `fn g(x) -> fn(_) -> Int`.
    use crate::decompile::final_type_table::FinalTypeTable;

    let f_id = crate::pseudo::var_id::VarId::new(2240);
    let x_id = crate::pseudo::var_id::VarId::new(2241);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::int(0)),
    };
    let expr = PseudoExpr::Let {
        name: "g".to_string(),
        id: Some(f_id),
        value: PBox::new(lambda),
        body: PBox::new(PseudoExpr::var_with_id("g", f_id)),
    };

    let mut final_types = FinalTypeTable::new();
    final_types.bind_var(
        f_id,
        Rc::new(PseudoType::Function {
            params: vec![Rc::new(PseudoType::Unknown)],
            ret: Rc::new(PseudoType::Int),
        }),
    );
    final_types.freeze();

    let config = PrettyConfig {
        show_types: true,
        ..Default::default()
    };
    let rendered = PrettyPrinter::with_config(config)
        .with_final_types(Rc::new(final_types))
        .print(&expr);

    assert!(
        rendered.contains("fn g(x) -> Int"),
        "expected unwrapped concrete return type `-> Int`, got:\n{rendered}"
    );
}

#[test]
fn test_constr_pretty_uses_shape_display_name_for_known() {
    // Known closed-set constructor renders via shape.display_name_or,
    // which returns the shape's closed-set name. Option tags:
    // Some=0 (arity 1), None=1 (nullary).
    let expr = PseudoExpr::constr_known(KnownConstructor::Some, vec![PseudoExpr::int(42)]);
    assert_eq!(expr.to_pretty(), "Some(42)");

    let none = PseudoExpr::constr_known(KnownConstructor::None, vec![]);
    assert_eq!(none.to_pretty(), "None");
}

#[test]
fn test_constr_pretty_resolves_user_name_via_registry() {
    // User-defined constructor outside the closed set — shape is Unknown,
    // so pretty consults `BlueprintHintRegistry` via the `TypeHintId`.
    let nil_hint = crate::decompile::TypeHintId::new("MyList");
    let nil = PseudoExpr::constr_with_hint(
        ConstructorShape::unknown_data(1, 0),
        vec![],
        Some(nil_hint.clone()),
    );
    let cons_hint = crate::decompile::TypeHintId::new("MyList");
    let cons = PseudoExpr::constr_with_hint(
        ConstructorShape::unknown_data(0, 2),
        vec![PseudoExpr::int(1), PseudoExpr::var("rest")],
        Some(cons_hint.clone()),
    );

    let mut registry = BlueprintHintRegistry::new();
    registry.register_user(nil_hint, 1, "Nil");
    registry.register_user(cons_hint, 0, "Cons");
    let registry = Rc::new(registry);

    let render = |expr: &PseudoExpr| {
        PrettyPrinter::new()
            .with_registry(registry.clone())
            .print(expr)
    };
    assert_eq!(render(&nil), "Nil");
    assert_eq!(render(&cons), "Cons(1, rest)");
}

#[test]
fn test_constr_pretty_uses_constr_tag_when_no_name_and_unknown_shape() {
    // Unknown shape + no name → Constr<tag> fallback.
    let anon = PseudoExpr::constr(ConstructorShape::unknown_data(7, 0), vec![]);
    assert_eq!(anon.to_pretty(), "Constr<7>");

    let anon_fields = PseudoExpr::constr(
        ConstructorShape::unknown_data(3, 1),
        vec![PseudoExpr::int(0)],
    );
    assert_eq!(anon_fields.to_pretty(), "Constr<3>(0)");
}

#[test]
fn test_when_data_constr_pattern_emits_wildcards_for_zero_bound_fields() {
    // `when y is { Constr -> y }` is invalid surface syntax: the
    // `Data.Constr` variant has arity 2 (Int, List<Data>), so a
    // shape-test that binds no fields must still render
    // arity-matching `_` wildcards.
    let data_hint = crate::decompile::TypeHintId::new("Data");
    let mut registry = BlueprintHintRegistry::new();
    // Tag 0 of the "Data" namespace resolves to "Constr".
    registry.register_user(data_hint.clone(), 0, "Constr");
    let registry = Rc::new(registry);

    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("y")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor_with_hint(
                    ConstructorShape::unknown_data(0, 0),
                    vec![],
                    Some(data_hint.clone()),
                ),
                PseudoExpr::var("y"),
            ),
            WhenClause::new(WhenPattern::wildcard(), PseudoExpr::error()),
        ],
    };

    let out = PrettyPrinter::new()
        .with_registry(registry.clone())
        .print(&when_expr);
    assert!(
        out.contains("Constr(_, _)"),
        "expected `Constr(_, _)` arity-matched wildcards, got:\n{out}"
    );
    assert!(
        !out.contains("Constr ->"),
        "must not render bare `Constr` arm: {out}"
    );

    // Map/List/Int/ByteString — each has arity 1.
    for label in &["Map", "List", "Int", "ByteString"] {
        let mut reg = BlueprintHintRegistry::new();
        reg.register_user(data_hint.clone(), 0, *label);
        let reg = Rc::new(reg);
        let single_arm = PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("y")),
            subject_name: None,
            clauses: vec![WhenClause::new(
                WhenPattern::constructor_with_hint(
                    ConstructorShape::unknown_data(0, 0),
                    vec![],
                    Some(data_hint.clone()),
                ),
                PseudoExpr::var("y"),
            )],
        };
        let out = PrettyPrinter::new().with_registry(reg).print(&single_arm);
        assert!(
            out.contains(&format!("{}(_)", label)),
            "expected `{label}(_)` arity-1 wildcard, got:\n{out}"
        );
    }
}

// ---- gate Data-arity override on Data type_hint ----

#[test]
fn user_adt_named_constr_no_data_hint_keeps_shape_arity() {
    // A user ADT registering a variant literally named "Constr". The
    // pattern's `type_hint` is not the "Data" namespace, so the
    // Data-arity override (which would force arity 2) must not fire:
    // declared arity 0 renders bare `Constr`.
    let my_hint = crate::decompile::TypeHintId::new("MyAdt");
    let mut registry = BlueprintHintRegistry::new();
    registry.register_user(my_hint.clone(), 0, "Constr");
    let registry = Rc::new(registry);

    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("y")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor_with_hint(
                    ConstructorShape::unknown_data(0, 0),
                    vec![],
                    Some(my_hint.clone()),
                ),
                PseudoExpr::var("y"),
            ),
            WhenClause::new(WhenPattern::wildcard(), PseudoExpr::error()),
        ],
    };
    let out = PrettyPrinter::new()
        .with_registry(registry.clone())
        .print(&when_expr);
    // Either arm form is valid surface syntax for a nullary user-ADT
    // constructor; `Constr(_, _)` would mean the Data-arity
    // fallback fired.
    assert!(
        !out.contains("Constr(_"),
        "Data-arity fallback must not fire for non-Data type_hint:\n{out}"
    );
    assert!(
        out.contains("Constr ->") || out.contains("Constr = y"),
        "expected bare `Constr` pattern or `expect Constr = …` sugar, got:\n{out}"
    );
}

#[test]
fn partial_data_constr_pattern_pads_with_wildcards() {
    // Data.Constr is arity 2 but the pattern binds only 1 field —
    // render `Constr(a, _)`.
    let data_hint = crate::decompile::TypeHintId::new("Data");
    let mut registry = BlueprintHintRegistry::new();
    registry.register_user(data_hint.clone(), 0, "Constr");
    let registry = Rc::new(registry);

    let bound_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("y")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::constructor_with_hint(
                ConstructorShape::unknown_data(0, 1),
                vec![Binder::new("a", bound_id)],
                Some(data_hint.clone()),
            ),
            PseudoExpr::var_with_id("a", bound_id),
        )],
    };
    let out = PrettyPrinter::new()
        .with_registry(registry.clone())
        .print(&when_expr);
    assert!(
        out.contains("Constr(a, _)"),
        "expected `Constr(a, _)` partial-padded pattern, got:\n{out}"
    );
}

#[test]
fn bare_some_pattern_pads_to_unary_wildcard() {
    // A shape-test on an `Option` that binds no payload mints a 0-arity
    // `Unknown` shape that the registry resolves to the prelude label
    // `Some`. `Some` is 1-ary, so a bare `Some ->` is invalid surface syntax — it
    // must render `Some(_) ->`. The sibling nullary `None` arm stays bare.
    let opt_hint = crate::decompile::TypeHintId::new("Option");
    let mut registry = BlueprintHintRegistry::new();
    registry.register_user(opt_hint.clone(), 0, "Some");
    registry.register_user(opt_hint.clone(), 1, "None");
    let registry = Rc::new(registry);

    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("opt")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor_with_hint(
                    ConstructorShape::unknown_data(0, 0),
                    vec![],
                    Some(opt_hint.clone()),
                ),
                PseudoExpr::Bool(true),
            ),
            WhenClause::new(
                WhenPattern::constructor_with_hint(
                    ConstructorShape::unknown_data(1, 0),
                    vec![],
                    Some(opt_hint.clone()),
                ),
                PseudoExpr::Bool(false),
            ),
        ],
    };
    let out = PrettyPrinter::new()
        .with_registry(registry.clone())
        .print(&when_expr);
    assert!(
        out.contains("Some(_) ->"),
        "expected `Some(_) ->` padded unary pattern, got:\n{out}"
    );
    assert!(
        out.contains("None ->") && !out.contains("None(_)"),
        "nullary `None` must stay bare, got:\n{out}"
    );
}

#[test]
fn non_option_constructor_named_some_is_not_padded() {
    // The `Some` arity override is gated on the canonical `Option` namespace,
    // not the bare label: a 0-ary `Some` under any other hint stays bare, not
    // padded to `Some(_)`.
    let user_hint = crate::decompile::TypeHintId::new("MyAdt");
    let mut registry = BlueprintHintRegistry::new();
    registry.register_user(user_hint.clone(), 0, "Some");
    let registry = Rc::new(registry);

    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::constructor_with_hint(
                ConstructorShape::unknown_data(0, 0),
                vec![],
                Some(user_hint.clone()),
            ),
            PseudoExpr::Bool(true),
        )],
    };
    let out = PrettyPrinter::new()
        .with_registry(registry.clone())
        .print(&when_expr);
    // A non-Option-namespace `Some` keeps its declared 0 arity (the
    // single-clause `when` further renders as `expect Some = x` sugar — only
    // the absence of padding matters).
    assert!(
        !out.contains("Some(_)") && out.contains("Some"),
        "a non-Option-namespace ctor named `Some` must stay bare (unpadded), got:\n{out}"
    );
}

#[test]
fn full_data_constr_pattern_unchanged() {
    // Data.Constr arity 2 + 2 bound fields — render `Constr(a, b)`.
    let data_hint = crate::decompile::TypeHintId::new("Data");
    let mut registry = BlueprintHintRegistry::new();
    registry.register_user(data_hint.clone(), 0, "Constr");
    let registry = Rc::new(registry);

    let a_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let b_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("y")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::constructor_with_hint(
                ConstructorShape::unknown_data(0, 2),
                vec![Binder::new("a", a_id), Binder::new("b", b_id)],
                Some(data_hint.clone()),
            ),
            // Use both binders so the unused-binder pass leaves them as-is:
            // this test checks full-arity rendering, not usage cleanup.
            PseudoExpr::Pair(
                PBox::new(PseudoExpr::var_with_id("a", a_id)),
                PBox::new(PseudoExpr::var_with_id("b", b_id)),
            ),
        )],
    };
    let out = PrettyPrinter::new()
        .with_registry(registry.clone())
        .print(&when_expr);
    assert!(
        out.contains("Constr(a, b)"),
        "expected `Constr(a, b)` unchanged, got:\n{out}"
    );
}

#[test]
fn p3_2_render_named_fn_param_with_named_type_annotation() {
    // With `show_types` on, a named-fn param whose VarId resolves
    // to a Named type in `FinalTypeTable` gets its annotation.
    use crate::decompile::final_type_table::FinalTypeTable;

    let sc_id = crate::pseudo::var_id::VarId::from_raw(3400);
    let entry_id = crate::pseudo::var_id::VarId::from_raw(3401);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", sc_id)],
        body: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
    };
    let expr = PseudoExpr::Let {
        name: "entry".to_string(),
        id: Some(entry_id),
        value: PBox::new(lambda),
        body: PBox::new(PseudoExpr::var_with_id("entry", entry_id)),
    };

    let mut final_types = FinalTypeTable::new();
    final_types.bind_var(
        sc_id,
        Rc::new(PseudoType::Named("ScriptContext".to_string())),
    );
    final_types.freeze();

    let config = PrettyConfig {
        show_types: true,
        ..Default::default()
    };
    let rendered = PrettyPrinter::with_config(config)
        .with_final_types(Rc::new(final_types))
        .print(&expr);

    assert!(
        rendered.contains("script_context: ScriptContext"),
        "expected `script_context: ScriptContext` annotation in named-fn render, got:\n{rendered}"
    );
}

#[test]
fn p3_2_render_no_annotation_when_show_types_off() {
    // With `show_types: false`, the type-annotation path is fully
    // skipped — the rendered named-fn must NOT contain `:`.
    use crate::decompile::final_type_table::FinalTypeTable;

    let sc_id = crate::pseudo::var_id::VarId::from_raw(3410);
    let entry_id = crate::pseudo::var_id::VarId::from_raw(3411);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", sc_id)],
        body: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
    };
    let expr = PseudoExpr::Let {
        name: "entry".to_string(),
        id: Some(entry_id),
        value: PBox::new(lambda),
        body: PBox::new(PseudoExpr::var_with_id("entry", entry_id)),
    };

    let mut final_types = FinalTypeTable::new();
    final_types.bind_var(
        sc_id,
        Rc::new(PseudoType::Named("ScriptContext".to_string())),
    );
    final_types.freeze();

    let config = PrettyConfig {
        show_types: false,
        ..Default::default()
    };
    let rendered = PrettyPrinter::with_config(config)
        .with_final_types(Rc::new(final_types))
        .print(&expr);

    assert!(
        rendered.contains("script_context") && !rendered.contains("script_context:"),
        "with show_types=false, param must render without `:` annotation, got:\n{rendered}"
    );
}

#[test]
fn f_ext5_curried_uninformative_function_type_is_uninformative_predicate_true() {
    // Predicate-level test: the curried `fn(_) -> fn(_) -> _` type is
    // uninformative. Rendering-level suppression is gated further at
    // let-binding sites.
    use crate::decompile::render::tests::test_helpers::is_uninformative_for_test;
    let curried = PseudoType::Function {
        params: vec![Rc::new(PseudoType::Unknown)],
        ret: Rc::new(PseudoType::Function {
            params: vec![Rc::new(PseudoType::Unknown)],
            ret: Rc::new(PseudoType::Unknown),
        }),
    };
    assert!(
        is_uninformative_for_test(&curried),
        "curried `fn(_) -> fn(_) -> _` must be uninformative"
    );
}

#[test]
fn f_ext5_curried_function_with_one_concrete_position_is_informative() {
    use crate::decompile::render::tests::test_helpers::is_uninformative_for_test;
    // `fn(_) -> fn(Int) -> _` — one position concrete. Must NOT be
    // treated as uninformative.
    let mixed = PseudoType::Function {
        params: vec![Rc::new(PseudoType::Unknown)],
        ret: Rc::new(PseudoType::Function {
            params: vec![Rc::new(PseudoType::Int)],
            ret: Rc::new(PseudoType::Unknown),
        }),
    };
    assert!(
        !is_uninformative_for_test(&mixed),
        "concrete-position fn type must NOT be uninformative"
    );
}

/// Test-only re-exports so unit tests can exercise crate-private
/// predicates.
pub mod test_helpers {
    use crate::pseudo::ast::PseudoType;

    pub(crate) fn is_uninformative_for_test(ty: &PseudoType) -> bool {
        super::super::is_uninformative_function_type(ty)
    }
}

#[test]
fn bool_annotation_suppressed_when_value_is_unknown_shape_constr() {
    // `helper_6: Bool = Unknown_E_0_1` — a Constr in a user-defined
    // sum, not prelude `True`, so the annotation misleads.
    use crate::decompile::final_type_table::FinalTypeTable;
    use crate::pseudo::constructor::ConstructorShape;

    let var_id = crate::pseudo::var_id::VarId::from_raw(2400);
    let expr = PseudoExpr::Let {
        name: "helper_6".to_string(),
        id: Some(var_id),
        value: PBox::new(PseudoExpr::Constr {
            tag: 1,
            shape: ConstructorShape::unknown_data(1, 0),
            fields: PVec::new(),
            type_hint: None,
        }),
        body: PBox::new(PseudoExpr::var_with_id("helper_6", var_id)),
    };
    let mut final_types = FinalTypeTable::new();
    final_types.bind_var(var_id, Rc::new(PseudoType::Bool));
    final_types.freeze();

    let config = PrettyConfig {
        show_types: true,
        ..Default::default()
    };
    let rendered = PrettyPrinter::with_config(config)
        .with_final_types(Rc::new(final_types))
        .print(&expr);

    assert!(
        !rendered.contains(": Bool"),
        "Bool annotation must be suppressed on Unknown-shape Constr, got:\n{rendered}"
    );
}

#[test]
fn bool_annotation_kept_when_value_is_known_true_constr() {
    // The surface's actual `let x: Bool = True` — Constr has shape
    // `Known(KnownConstructor::True)`. Annotation should stay.
    use crate::decompile::final_type_table::FinalTypeTable;
    use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};

    let var_id = crate::pseudo::var_id::VarId::from_raw(2410);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(var_id),
        value: PBox::new(PseudoExpr::Constr {
            tag: 1,
            shape: ConstructorShape::Known(KnownConstructor::True),
            fields: PVec::new(),
            type_hint: None,
        }),
        body: PBox::new(PseudoExpr::var_with_id("x", var_id)),
    };
    let mut final_types = FinalTypeTable::new();
    final_types.bind_var(var_id, Rc::new(PseudoType::Bool));
    final_types.freeze();

    let config = PrettyConfig {
        show_types: true,
        ..Default::default()
    };
    let rendered = PrettyPrinter::with_config(config)
        .with_final_types(Rc::new(final_types))
        .print(&expr);

    assert!(
        rendered.contains("x: Bool"),
        "Bool annotation must stay on Known(True) Constr, got:\n{rendered}"
    );
}

mod scott_constructor_annotation {
    use super::*;
    use crate::pseudo::ast::Binder;
    use crate::pseudo::var_id::VarId;

    fn binder(name: &str, id: u32) -> Binder {
        Binder::new(name.to_string(), VarId::new(id))
    }

    fn var(name: &str, id: u32) -> PseudoExpr {
        PseudoExpr::var_with_id(name, VarId::new(id))
    }

    /// `λ a b h0 h1 h2 . h1 a b` — variant tag 1 of a 3-variant union
    /// carrying 2 fields.
    fn three_variant_ctor() -> PseudoExpr {
        PseudoExpr::Lambda {
            params: vec![
                binder("a", 1),
                binder("b", 2),
                binder("h0", 3),
                binder("h1", 4),
                binder("h2", 5),
            ],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("h1", 4)),
                args: vec![var("a", 1), var("b", 2)].into(),
            }),
        }
    }

    #[test]
    fn annotates_three_variant_scott_constructor() {
        let lines = scott_constructor_comment(&three_variant_ctor(), &[var("p", 10), var("q", 11)]);
        assert_eq!(
            lines,
            vec![
                "// Scott-encoded tagged union: tag 1 of 3, fields (p, q).".to_string(),
                "// A matcher supplies 3 branch fns; this value invokes the 2nd.".to_string(),
            ]
        );
    }

    /// A church pair `λ a b k . k a b` (one handler) is decoded to
    /// `Pair` elsewhere and must NOT be annotated as a tagged union.
    #[test]
    fn skips_single_variant_pair() {
        let pair = PseudoExpr::Lambda {
            params: vec![binder("a", 1), binder("b", 2), binder("k", 3)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("k", 3)),
                args: vec![var("a", 1), var("b", 2)].into(),
            }),
        };
        assert!(scott_constructor_comment(&pair, &[var("p", 10), var("q", 11)]).is_empty());
    }

    /// A church bool `λ t f . t` (body is a bare Var, not an Apply) is
    /// not a constructor application.
    #[test]
    fn skips_church_bool() {
        let church_true = PseudoExpr::Lambda {
            params: vec![binder("t", 1), binder("f", 2)],
            body: PBox::new(var("t", 1)),
        };
        assert!(scott_constructor_comment(&church_true, &[]).is_empty());
    }

    /// Wrong field order (`k b a`) is not the canonical constructor.
    #[test]
    fn skips_swapped_field_order() {
        let swapped = PseudoExpr::Lambda {
            params: vec![
                binder("a", 1),
                binder("b", 2),
                binder("h0", 3),
                binder("h1", 4),
                binder("h2", 5),
            ],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("h1", 4)),
                args: vec![var("b", 2), var("a", 1)].into(),
            }),
        };
        assert!(scott_constructor_comment(&swapped, &[var("p", 10), var("q", 11)]).is_empty());
    }

    /// Field count falls back to a plain count when a field value is a
    /// compound expression.
    #[test]
    fn falls_back_to_field_count_for_compound_args() {
        let compound = PseudoExpr::Apply {
            function: PBox::new(var("g", 20)),
            args: vec![var("z", 21)].into(),
        };
        let lines = scott_constructor_comment(&three_variant_ctor(), &[compound, var("q", 11)]);
        assert_eq!(
            lines[0],
            "// Scott-encoded tagged union: tag 1 of 3, 2 fields."
        );
    }

    #[test]
    fn ordinal_word_cases() {
        assert_eq!(ordinal_word(1), "1st");
        assert_eq!(ordinal_word(2), "2nd");
        assert_eq!(ordinal_word(3), "3rd");
        assert_eq!(ordinal_word(4), "4th");
        assert_eq!(ordinal_word(11), "11th");
        assert_eq!(ordinal_word(12), "12th");
        assert_eq!(ordinal_word(13), "13th");
        assert_eq!(ordinal_word(21), "21st");
        assert_eq!(ordinal_word(22), "22nd");
        assert_eq!(ordinal_word(23), "23rd");
    }

    #[test]
    fn bool_field_uses_surface_casing() {
        let lines = scott_constructor_comment(
            &three_variant_ctor(),
            &[PseudoExpr::Bool(true), PseudoExpr::Bool(false)],
        );
        assert_eq!(
            lines[0],
            "// Scott-encoded tagged union: tag 1 of 3, fields (True, False)."
        );
    }

    /// A Scott constructor used as a tuple element forces the tuple to
    /// break one-element-per-line, so the `// …` annotation lands on
    /// its own line instead of being crammed after `(x, `.
    #[test]
    fn tuple_with_scott_element_breaks_multiline() {
        let app = PseudoExpr::Apply {
            function: PBox::new(three_variant_ctor()),
            args: vec![var("p", 10), var("q", 11)].into(),
        };
        let tup = PseudoExpr::Tuple((vec![var("x", 20), app, var("y", 21)]).into());
        let rendered = tup.to_pretty();
        for line in rendered.lines() {
            if line.contains("// Scott-encoded") {
                assert_eq!(
                    line.trim_start(),
                    "// Scott-encoded tagged union: tag 1 of 3, fields (p, q).",
                    "annotation must be alone on its line, got: {line:?}"
                );
            }
        }
        assert!(
            rendered.contains("(\n"),
            "tuple should break, got:\n{rendered}"
        );
    }
}

#[test]
fn soft_assert_question_mark_preserves_custom_trace_message() {
    use crate::pseudo::ast::BinaryOp;
    // `cond || trace @"nope": False` must NOT collapse to `cond?` — the `?`
    // operator cannot carry the custom message, so the collapse would drop it.
    let with_msg = PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: PBox::new(PseudoExpr::var("cond")),
        right: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::string("nope")),
            value: PBox::new(PseudoExpr::Bool(false)),
        }),
    };
    let out = with_msg.to_pretty();
    assert!(
        out.contains("nope") && out.contains("trace") && !out.contains('?'),
        "custom-message soft-assert must keep its message (no `?` collapse), got:\n{out}"
    );

    // An empty trace message carries nothing → collapsing to `cond?` is lossless.
    let empty_msg = PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: PBox::new(PseudoExpr::var("cond")),
        right: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::string("")),
            value: PBox::new(PseudoExpr::Bool(false)),
        }),
    };
    let out2 = empty_msg.to_pretty();
    assert!(
        out2.contains('?'),
        "empty-message soft-assert may collapse to `?`, got:\n{out2}"
    );
}

// ===== list-spine + Constr-access surface, gated on the =====
// ===== compilable-data-access toggle (DEFAULT pseudo / OPT-IN builtin.*) =====

/// Render with compilable-data-access ON. `to_pretty` is the OFF default,
/// so the two spellings below are the two modes each test compares.
fn pretty_on(expr: &PseudoExpr) -> String {
    expr.to_pretty_with_config(PrettyConfig {
        render_ctx: crate::decompile::RenderCtx::default().with_compilable_data_access(true),
        ..Default::default()
    })
}

fn list_coll() -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::DataUnList,
        args: vec![PseudoExpr::var("d")].into(),
    }
}

#[test]
fn index_access_on_list_default_keeps_bracket() {
    // DEFAULT (toggle OFF): an IndexAccess renders the `coll[N]` bracket even
    // when the collection is provably a list.
    let idx0 = PseudoExpr::IndexAccess {
        collection: PBox::new(list_coll()),
        index: 0,
    };
    assert_eq!(
        idx0.to_pretty(),
        "builtin.un_list_data(d)[0]",
        "DEFAULT: list index keeps bracket"
    );

    let idx2 = PseudoExpr::IndexAccess {
        collection: PBox::new(list_coll()),
        index: 2,
    };
    let out2 = idx2.to_pretty();
    assert_eq!(out2, "builtin.un_list_data(d)[2]", "DEFAULT: keeps bracket");
    assert!(
        !out2.contains("head_list"),
        "DEFAULT must not emit head_list: {out2}"
    );
}

#[test]
fn index_access_on_list_flag_on_lowers_to_head_tail_list() {
    // GATE A (fail-closed) + toggle ON: an IndexAccess on a PROVABLY
    // list-producing collection (here `builtin.un_list_data(d)`) lowers to
    // `builtin.head_list(builtin.tail_list^N(coll))`.
    let idx0 = PseudoExpr::IndexAccess {
        collection: PBox::new(list_coll()),
        index: 0,
    };
    let out0 = pretty_on(&idx0);
    assert_eq!(
        out0, "builtin.head_list(builtin.un_list_data(d))",
        "ON: index 0 on a provably-list collection → head_list, got: {out0}"
    );

    let idx2 = PseudoExpr::IndexAccess {
        collection: PBox::new(list_coll()),
        index: 2,
    };
    let out2 = pretty_on(&idx2);
    assert_eq!(
        out2, "builtin.head_list(builtin.tail_list(builtin.tail_list(builtin.un_list_data(d))))",
        "ON: index 2 → head_list(tail_list(tail_list(...))), got: {out2}"
    );
    assert!(
        !out2.contains("[2]"),
        "ON: list index must not keep bracket: {out2}"
    );

    // FAIL-CLOSED: even with the toggle ON, a bare `Var` collection is NOT
    // provably a list (could be tuple/pair-typed, type_resolution Unknown), so
    // it KEEPS the bracket render rather than risk `head_list(tuple)`.
    let idx_var = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::var("xs")),
        index: 0,
    };
    let out_var = pretty_on(&idx_var);
    assert_eq!(
        out_var, "xs[0]",
        "ON: a bare Var index must stay bracket (fail-closed), got: {out_var}"
    );
}

#[test]
fn index_access_on_tuple_literal_keeps_bracket_both_modes() {
    // A structural Tuple literal indexed `[N]` must NEVER become head_list
    // (the valid-looking-wrong bug) — keep the bracket render in BOTH modes.
    let idx = || PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::tuple(vec![
            PseudoExpr::int(1),
            PseudoExpr::int(2),
        ])),
        index: 0,
    };
    let out_default = idx().to_pretty();
    assert!(
        out_default.contains("[0]") && !out_default.contains("head_list"),
        "DEFAULT: tuple index must keep bracket, never head_list, got: {out_default}"
    );
    let out_on = pretty_on(&idx());
    assert!(
        out_on.contains("[0]") && !out_on.contains("head_list"),
        "ON: tuple index must keep bracket, never head_list, got: {out_on}"
    );
}

#[test]
fn index_access_on_pair_literal_keeps_bracket_both_modes() {
    // A structural Pair literal indexed must keep the bracket render in both
    // modes (GATE A is fail-closed against Pair indexing).
    let idx = || PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::pair(PseudoExpr::int(1), PseudoExpr::int(2))),
        index: 1,
    };
    let out_default = idx().to_pretty();
    assert!(
        out_default.contains("[1]") && !out_default.contains("head_list"),
        "DEFAULT: pair index must keep bracket, never head_list, got: {out_default}"
    );
    let out_on = pretty_on(&idx());
    assert!(
        out_on.contains("[1]") && !out_on.contains("head_list"),
        "ON: pair index must keep bracket, never head_list, got: {out_on}"
    );
}

#[test]
fn slice_from_default_keeps_bracket() {
    // DEFAULT (OFF): `List.tail(coll)` → readable pseudo `coll[1..]` slice.
    let tail = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::ListTail,
        args: vec![PseudoExpr::var("xs")].into(),
    };
    assert_eq!(tail.to_pretty(), "xs[1..]", "DEFAULT: tail → [1..] slice");
}

#[test]
fn slice_from_flag_on_lowers_to_tail_list() {
    // ON: `List.tail(coll)` → compilable `builtin.tail_list(coll)`.
    let tail = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::ListTail,
        args: vec![PseudoExpr::var("xs")].into(),
    };
    assert_eq!(
        pretty_on(&tail),
        "builtin.tail_list(xs)",
        "ON: tail → tail_list"
    );
}

#[test]
fn head_accessor_default_keeps_dot_head() {
    // DEFAULT (OFF): `FieldSelector::ListHead` renders as `.head`.
    let expr = PseudoExpr::field_access_typed(
        PseudoExpr::var("xs"),
        crate::pseudo::field_selector::FieldSelector::ListHead,
    );
    assert_eq!(
        expr.to_pretty(),
        "xs.head",
        "DEFAULT: .head accessor preserved"
    );
}

#[test]
fn head_accessor_flag_on_lowers_to_head_list_call() {
    // ON: `.head` (FieldSelector::ListHead) → builtin.head_list(record).
    let expr = PseudoExpr::field_access_typed(
        PseudoExpr::var("xs"),
        crate::pseudo::field_selector::FieldSelector::ListHead,
    );
    let out = pretty_on(&expr);
    assert_eq!(out, "builtin.head_list(xs)", "ON: got: {out}");
    assert!(
        !out.contains("xs.head"),
        "ON: must not keep the `.head` accessor: {out}"
    );
}

#[test]
fn constr_unpack_default_keeps_pseudo_name() {
    // DEFAULT (OFF): `Constr.unpack(x)` / `List.is_empty(x)` render the readable
    // pseudo canonical names.
    let unpack = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::ConstrUnpack,
        args: vec![PseudoExpr::var("x")].into(),
    };
    assert_eq!(
        unpack.to_pretty(),
        "Constr.unpack(x)",
        "DEFAULT: Constr.unpack"
    );
    let is_empty = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::ListIsEmpty,
        args: vec![PseudoExpr::var("x")].into(),
    };
    assert_eq!(
        is_empty.to_pretty(),
        "List.is_empty(x)",
        "DEFAULT: List.is_empty"
    );
    let head = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::ListHead,
        args: vec![PseudoExpr::var("x")].into(),
    };
    assert_eq!(head.to_pretty(), "List.head(x)", "DEFAULT: List.head");
}

#[test]
fn constr_unpack_flag_on_renders_builtin_surface() {
    // ON: the four data-access builtins render their compilable `builtin.*`
    // surface.
    let unpack = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::ConstrUnpack,
        args: vec![PseudoExpr::var("x")].into(),
    };
    assert_eq!(
        pretty_on(&unpack),
        "builtin.un_constr_data(x)",
        "ON: un_constr_data"
    );
    let is_empty = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::ListIsEmpty,
        args: vec![PseudoExpr::var("x")].into(),
    };
    assert_eq!(
        pretty_on(&is_empty),
        "builtin.null_list(x)",
        "ON: null_list"
    );
    let head = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::ListHead,
        args: vec![PseudoExpr::var("x")].into(),
    };
    assert_eq!(pretty_on(&head), "builtin.head_list(x)", "ON: head_list");
}

#[test]
fn pair_fst_snd_accessors_keep_ordinal_render() {
    // Guard: the toggle must NOT touch Pair `.1st`/`.2nd` accessors (in either
    // mode).
    let fst = PseudoExpr::field_access_typed(
        PseudoExpr::var("p"),
        crate::pseudo::field_selector::FieldSelector::PairFst,
    );
    assert_eq!(fst.to_pretty(), "p.1st");
    let snd = PseudoExpr::field_access_typed(
        PseudoExpr::var("p"),
        crate::pseudo::field_selector::FieldSelector::PairSnd,
    );
    assert_eq!(snd.to_pretty(), "p.2nd");
    assert_eq!(pretty_on(&fst), "p.1st", "ON must not touch .1st");
    assert_eq!(pretty_on(&snd), "p.2nd", "ON must not touch .2nd");
}
