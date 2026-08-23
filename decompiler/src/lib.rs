//! dehosk: decompile UPLC (Untyped Plutus Core) bytecode into
//! human-readable pseudocode.
//!
//! ```rust,ignore
//! use dehosk::{decompile, DecompileOptions};
//!
//! let uplc_hex = "...";
//! let result = decompile(uplc_hex, DecompileOptions::default())?;
//! println!("{}", result);
//! ```
//!
//! Parse CBOR/Flat into a UPLC AST, recover patterns and types,
//! translate to `PseudoExpr`, then pretty-print. The pipeline
//! inverts compiler encodings (Church/Scott, Cardano context
//! schema) so the surface reads as source, not bytecode.

pub mod builtins;
pub mod cardano;
pub mod debug;
mod debug_env;
pub mod decompile;
pub mod error;
pub mod fixtures;
pub mod pseudo;
mod stack;

pub use builtins::BuiltinId;
pub use debug::{DebugBundle, decompile_program_debug, decompile_program_debug_with_options};
pub use decompile::{
    DecompileOptions, DisplayPolishPasses, OutputLayer, ReadabilityPasses, ScriptVersion,
    SimplifyPasses, StructuralRecoveryPasses, TypePasses, decompile, decompile_program,
};
pub use error::{DecompileError, Result};
use uplc::ast::NamedDeBruijn;

/// Decompile and return both text output and a debug bundle with provenance/source-map.
pub fn decompile_with_debug(
    hex_code: &str,
    options: DecompileOptions,
) -> Result<(String, DebugBundle)> {
    let program: uplc::ast::Program<NamedDeBruijn> = decompile::decode_hex_to_program(hex_code)?;
    let debug_bundle = debug::decompile_program_debug_with_options(&program, options)?;
    let code = debug_bundle.code.clone();
    Ok((code, debug_bundle))
}

/// Decode CBOR-encoded `PlutusData` (e.g. a `--oracle-arg` datum / redeemer /
/// script_context for the polarity-report data-tag oracle). Thin re-export of
/// the `uplc` decoder so callers don't need a direct `uplc` dependency.
pub fn decode_plutus_data(bytes: &[u8]) -> std::result::Result<uplc::PlutusData, String> {
    uplc::plutus_data(bytes).map_err(|e| format!("{e:?}"))
}

/// Run a fallible closure on a dedicated 64 MB stack thread so deep recursive
/// passes don't overflow the default ~8 MB stack.
fn run_on_large_stack<T>(
    label: &'static str,
    work: impl FnOnce() -> Result<T> + Send + 'static,
) -> Result<T>
where
    T: Send + 'static,
{
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || std::panic::catch_unwind(std::panic::AssertUnwindSafe(work)))
        .map_err(|err| {
            DecompileError::internal(format!("failed to spawn {label} thread: {err}"))
        })?;

    match handle.join() {
        Ok(Ok(result)) => result,
        Ok(Err(panic_info)) => {
            let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                (*s).to_string()
            } else if let Some(s) = panic_info.downcast_ref::<String>() {
                s.clone()
            } else {
                "unknown panic".to_string()
            };
            Err(DecompileError::internal(format!(
                "{label} panicked on large-stack thread: {msg}"
            )))
        }
        Err(_) => Err(DecompileError::internal(format!(
            "{label} thread join failed (likely stack overflow)"
        ))),
    }
}

/// Decompile on a dedicated large-stack thread to avoid stack overflows on deep scripts.
///
/// NATIVE ONLY — it spawns a thread, which `wasm32-unknown-unknown` has
/// no support for. In the browser call [`decompile`] directly; the deep
/// walks there grow their own stack through `crate::stack`.
pub fn decompile_with_large_stack(hex_code: &str, options: DecompileOptions) -> Result<String> {
    let hex_owned = hex_code.to_string();
    run_on_large_stack("decompile", move || decompile(&hex_owned, options))
}

/// Decompile on a large-stack thread and return both the text output and the debug bundle.
///
/// Native only — same constraint as [`decompile_with_large_stack`].
pub fn decompile_with_debug_large_stack(
    hex_code: &str,
    options: DecompileOptions,
) -> Result<(String, DebugBundle)> {
    let hex_owned = hex_code.to_string();
    run_on_large_stack("decompile_with_debug", move || {
        decompile_with_debug(&hex_owned, options)
    })
}

#[cfg(test)]
mod proptest_tests;

#[cfg(test)]
mod integration_tests {
    use super::*;
    use crate::pseudo::ast::PBox;
    use crate::pseudo::ast::PseudoExpr;
    use uplc::ast::{FakeNamedDeBruijn, NamedDeBruijn, Program};

    #[test]
    fn test_v2_smoke_decompiles() {
        let hex = crate::decompile::tests::MIR_V2_SMOKE_HEX;

        let bytes = hex::decode(hex).expect("hex decode failed");
        println!("Bytes: {} bytes", bytes.len());

        // CBOR-wrapped Flat — go through `Program::from_cbor`.
        let mut buffer = Vec::new();
        let program: Program<FakeNamedDeBruijn> =
            Program::from_cbor(&bytes, &mut buffer).expect("CBOR/Flat parse failed");

        let program: Program<NamedDeBruijn> = program.into();

        println!("Program version: {:?}", program.version);

        // Decompile via the public API (full MIR pipeline).
        let output = decompile(hex, DecompileOptions::default()).expect("decompile failed");
        println!("\nOutput length: {}", output.len());
        if !output.is_empty() {
            println!("Decompiled output:\n{}", &output[..output.len().min(3000)]);
        }

        assert!(!output.is_empty(), "Output should not be empty");
    }

    #[test]
    fn test_v3_smoke_case_constr() {
        // V1.1.0 Case/Constr terms: `Case(Constr<0>(builtins), [branch])` must
        // constant-fold instead of producing a trivial identity function.
        let hex = crate::decompile::tests::MIR_V3_SMOKE_HEX;

        let mut opts = DecompileOptions::default();
        opts.script_version = Some(ScriptVersion::PlutusV3);
        let output = decompile(hex, opts).expect("decompile should succeed");
        assert!(
            output.len() > 100,
            "V3 Case/Constr script should decompile to substantial output, got {} chars",
            output.len()
        );
        assert!(
            output.contains("script_context"),
            "Should contain script_context"
        );
        assert!(
            output.contains("script_context.redeemer") || output.contains("let redeemer"),
            "Should contain V3 redeemer naming"
        );
        assert!(
            output.contains("script_context.script_info") || output.contains("let script_info"),
            "Should contain V3 script_info naming"
        );
        assert!(
            !output.contains("when field_2: Data is") && !output.contains("when field_1: Data is"),
            "regression: context-derived values should not render as `when field_N: Data is ...`. Output:\n{output}"
        );
    }

    #[test]
    fn test_mir_pipeline_end_to_end() {
        let hex = "46010000200101"; // identity function
        let output = decompile(hex, DecompileOptions::default()).expect("decompile should succeed");
        assert!(!output.is_empty(), "pipeline should produce output");
        println!("identity output: {}", output);
    }

    #[test]
    fn test_mir_pipeline_v3_script() {
        let hex = crate::decompile::tests::MIR_V3_SMOKE_HEX;
        let mut opts = DecompileOptions::default();
        opts.script_version = Some(ScriptVersion::PlutusV3);
        let output = decompile(hex, opts).expect("V3 decompile should succeed");
        assert!(
            output.len() > 1000,
            "V3 output should be >1000 chars, got {} chars",
            output.len()
        );
        println!(
            "V3 output ({} chars):\n{}...",
            output.len(),
            &output[..output.len().min(1000)]
        );
    }

    #[test]
    fn test_mir_pipeline_v2_script() {
        // Same script as `test_v2_smoke_decompiles`, with the V2 script version.
        let hex = crate::decompile::tests::MIR_V2_SMOKE_HEX;
        let mut opts = DecompileOptions::default();
        opts.script_version = Some(ScriptVersion::PlutusV2);
        let output = decompile(hex, opts).expect("V2 decompile should succeed");
        assert!(
            output.len() > 500,
            "V2 output should be >500 chars, got {} chars",
            output.len()
        );
        println!("V2 output ({} chars)", output.len());
    }

    #[test]
    fn test_mid_translate_identity() {
        use crate::decompile::mid::translate::MidTranslator;
        use crate::pseudo::mid::expr::MidExpr;

        // (lam x . x) in CBOR-wrapped Flat
        let hex = "46010000200101";
        let bytes = hex::decode(hex).unwrap();
        let mut buf = Vec::new();
        let program: Program<FakeNamedDeBruijn> = Program::from_cbor(&bytes, &mut buf).unwrap();
        let program: Program<NamedDeBruijn> = program.into();

        let mut translator = MidTranslator::new();
        let mid = translator.translate(&program.term);

        match &mid {
            MidExpr::Closure { params, body, .. } => {
                assert_eq!(params.len(), 1);
                assert!(matches!(body.as_ref(), MidExpr::Var { .. }));
            }
            other => panic!("Expected Closure, got {:?}", other),
        }

        // Provenance should link to UPLC
        assert!(translator.provenance.node_count() >= 2);
        // VarRegistry should have the parameter
        assert!(!translator.var_registry.is_empty());
    }

    #[test]
    fn test_mid_translate_v3_smoke() {
        use crate::decompile::mid::translate::MidTranslator;

        // Use the V3 script from above
        let hex = crate::decompile::tests::MIR_V3_SMOKE_HEX;

        let bytes = hex::decode(hex).unwrap();
        let mut buf = Vec::new();
        let program: Program<FakeNamedDeBruijn> = Program::from_cbor(&bytes, &mut buf).unwrap();
        let program: Program<NamedDeBruijn> = program.into();

        let mut translator = MidTranslator::new();
        let mid = translator.translate(&program.term);

        let count = mid.node_count();
        assert!(count > 50, "V3 smoke should have >50 nodes, got {}", count);

        assert!(
            translator.var_registry.len() > 10,
            "V3 smoke should have >10 variables, got {}",
            translator.var_registry.len()
        );

        assert!(
            translator.provenance.node_count() > 50,
            "V3 smoke should have >50 provenance entries, got {}",
            translator.provenance.node_count()
        );

        println!(
            "MIR translation: {} nodes, {} vars, {} provenance entries",
            count,
            translator.var_registry.len(),
            translator.provenance.node_count()
        );
    }

    #[test]
    fn test_mir_batch_random_scripts() {
        let Ok(csv_path) = std::env::var("DEHOSK_CORPUS_CSV") else {
            println!("Skipping batch test: DEHOSK_CORPUS_CSV is unset");
            return;
        };
        if csv_path.is_empty() {
            println!("Skipping batch test: DEHOSK_CORPUS_CSV is empty");
            return;
        }
        let csv = match std::fs::read_to_string(&csv_path) {
            Ok(c) => c,
            Err(e) => {
                println!("Skipping batch test: CSV not found at {csv_path}: {e}");
                return;
            }
        };
        let lines: Vec<&str> = csv.lines().collect();

        let line_numbers: &[usize] = &[
            100, 500, 1000, 2000, 3000, 5000, 7000, 10000, 15000, 20000, 25000, 30000, 35000,
            40000, 45000, 50000, 55000, 60000, 65000, 70000, 75000, 80000, 85000, 90000, 95000,
            100000, 105000, 110000, 115000, 120000, 125000, 130000, 135000,
        ];
        let mut successes = 0;
        let mut failures = 0;
        let mut panics = 0;
        let mut failure_details: Vec<String> = Vec::new();
        let mut panic_details: Vec<String> = Vec::new();

        for &line_no in line_numbers {
            if line_no >= lines.len() {
                println!(
                    "Line {}: SKIPPED (beyond file end {})",
                    line_no,
                    lines.len()
                );
                continue;
            }
            let line = lines[line_no];
            let fields: Vec<&str> = line.splitn(8, ',').collect();
            if fields.len() < 7 {
                println!(
                    "Line {}: SKIPPED (not enough fields: {})",
                    line_no,
                    fields.len()
                );
                continue;
            }

            let script_type = fields[4];
            let hex_raw = fields[6];
            let hex = hex_raw.strip_prefix("0x").unwrap_or(hex_raw);

            let version = match script_type {
                "plutusV1" => Some(ScriptVersion::PlutusV1),
                "plutusV2" => Some(ScriptVersion::PlutusV2),
                "plutusV3" => Some(ScriptVersion::PlutusV3),
                _ => None,
            };

            let mut opts = DecompileOptions::default();
            opts.script_version = version;

            let opts_clone = opts.clone();
            let hex_owned = hex.to_string();
            let script_type_owned = script_type.to_string();

            // Use a thread with a large stack to avoid stack overflows on deeply nested scripts
            let handle = std::thread::Builder::new()
                .stack_size(64 * 1024 * 1024)
                .spawn(move || std::panic::catch_unwind(move || decompile(&hex_owned, opts_clone)))
                .expect("failed to spawn thread");

            match handle.join() {
                Ok(Ok(Ok(output))) => {
                    successes += 1;
                    println!(
                        "Line {}: OK ({} chars, {})",
                        line_no,
                        output.len(),
                        script_type
                    );
                }
                Ok(Ok(Err(e))) => {
                    failures += 1;
                    let detail =
                        format!("Line {}: ERROR ({}): {:?}", line_no, script_type_owned, e);
                    println!("{}", detail);
                    failure_details.push(detail);
                }
                Ok(Err(panic_info)) => {
                    panics += 1;
                    let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                        s.to_string()
                    } else if let Some(s) = panic_info.downcast_ref::<String>() {
                        s.clone()
                    } else {
                        "unknown panic".to_string()
                    };
                    let detail =
                        format!("Line {}: PANIC ({}): {}", line_no, script_type_owned, msg);
                    println!("{}", detail);
                    panic_details.push(detail);
                }
                Err(_) => {
                    panics += 1;
                    let detail = format!(
                        "Line {}: THREAD_CRASH ({}): thread join failed (likely stack overflow)",
                        line_no, script_type_owned
                    );
                    println!("{}", detail);
                    panic_details.push(detail);
                }
            }
        }

        println!(
            "\n=== Batch results: {} success, {} failures, {} panics ===",
            successes, failures, panics
        );
        if !failure_details.is_empty() {
            println!("\nFailure details:");
            for d in &failure_details {
                println!("  {}", d);
            }
        }
        if !panic_details.is_empty() {
            println!("\nPanic details:");
            for d in &panic_details {
                println!("  {}", d);
            }
        }
        assert!(
            panics == 0,
            "{} panics occurred - see details above",
            panics
        );
    }

    // ==================== Simplifier deep-recursion tests ====================
    // Each exercises one recursive path in the simplifier for stack safety
    // and correct output.

    #[test]
    fn test_simplify_deep_let_chain() {
        use crate::decompile::simplify as do_simplify;

        // Build: let x_0 = 0; let x_1 = x_0; let x_2 = x_1; ... let x_{N-1} = x_{N-2}; x_{N-1}
        let depth = 200;
        let mut expr = PseudoExpr::var(format!("x_{}", depth - 1));
        for i in (0..depth).rev() {
            let value = if i == 0 {
                PseudoExpr::int(0)
            } else {
                PseudoExpr::var(format!("x_{}", i - 1))
            };
            expr = PseudoExpr::Let {
                name: format!("x_{}", i),
                id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                value: PBox::new(value),
                body: PBox::new(expr),
            };
        }

        let result = do_simplify(expr);
        let output = result.to_pretty();
        assert!(!output.is_empty(), "Deep let chain should produce output");
    }

    #[test]
    fn test_simplify_deep_apply_chain() {
        use crate::decompile::simplify as do_simplify;

        // f_99(f_98(...f_0(base)...)) — deeply nested Apply in argument position
        let depth = 100;
        let mut expr = PseudoExpr::var("base");
        for i in 0..depth {
            expr = PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var(format!("f_{}", i))),
                args: vec![expr].into(),
            };
        }

        let result = do_simplify(expr);
        let output = result.to_pretty();
        assert!(!output.is_empty(), "Deep apply chain should produce output");
    }

    #[test]
    fn test_simplify_deep_if_chain() {
        use crate::decompile::simplify as do_simplify;

        // if c_0 { if c_1 { if c_2 { ... deep_value ... } else { e_2 } } else { e_1 } } else { e_0 }
        let depth = 100;
        let mut expr = PseudoExpr::var("deep_value");
        for i in (0..depth).rev() {
            expr = PseudoExpr::If {
                condition: PBox::new(PseudoExpr::var(format!("c_{}", i))),
                then_branch: PBox::new(expr),
                else_branch: PBox::new(PseudoExpr::var(format!("e_{}", i))),
            };
        }

        let result = do_simplify(expr);
        let output = result.to_pretty();
        assert!(!output.is_empty(), "Deep if chain should produce output");
    }

    #[test]
    fn test_simplify_deep_when_chain() {
        use crate::decompile::simplify as do_simplify;
        use crate::pseudo::ast::WhenClause;
        use crate::pseudo::ast::WhenPattern;

        // When s_0 is { _ -> when s_1 is { _ -> when s_2 is { ... deep_value ... } } }
        let depth = 50;
        let mut expr = PseudoExpr::var("deep_value");
        for i in (0..depth).rev() {
            expr = PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var(format!("s_{}", i))),
                subject_name: None,
                clauses: vec![WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: None,
                    body: expr,
                }],
            };
        }

        let result = do_simplify(expr);
        let output = result.to_pretty();
        assert!(!output.is_empty(), "Deep when chain should produce output");
    }

    #[test]
    fn test_simplify_deep_lambda_apply() {
        use crate::decompile::simplify as do_simplify;

        // (fn(p_0) { (fn(p_1) { (fn(p_2) { ... inner ... }) (a_2) }) (a_1) }) (a_0)
        // Each Apply(Lambda(...), args) should be simplified to a Let binding.
        let depth = 50;
        let mut expr = PseudoExpr::var("inner");
        for i in (0..depth).rev() {
            let param = format!("p_{}", i);
            expr = PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Lambda {
                    params: vec![param.clone().into()],
                    body: PBox::new(expr),
                }),
                args: vec![PseudoExpr::var(format!("a_{}", i))].into(),
            };
        }

        let result = do_simplify(expr);
        let output = result.to_pretty();
        assert!(
            !output.is_empty(),
            "Deep lambda-apply chain should produce output"
        );
    }

    #[test]
    fn test_simplify_deep_force_delay() {
        use crate::decompile::simplify as do_simplify;

        // Force(delay(force(delay(... value ...)))) — each pair should cancel out
        let depth = 100;
        let mut expr = PseudoExpr::var("value");
        for _ in 0..depth {
            expr = PseudoExpr::Delay(PBox::new(expr));
            expr = PseudoExpr::Force(PBox::new(expr));
        }

        let result = do_simplify(expr);
        let output = result.to_pretty();
        assert_eq!(
            output.trim(),
            "value",
            "Force(Delay(x)) pairs should cancel to x"
        );
    }

    #[test]
    fn test_simplify_mixed_deep_nesting() {
        use crate::decompile::simplify as do_simplify;

        // Realistic mix: Let → If → Let → If → ... → result
        let depth = 30;
        let mut body = PseudoExpr::var("result");
        for i in (0..depth).rev() {
            body = PseudoExpr::Let {
                name: format!("inner_{}", i),
                id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::int(i as i64)),
                body: PBox::new(PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::Bool(true)),
                    then_branch: PBox::new(body),
                    else_branch: PBox::new(PseudoExpr::var("fallback")),
                }),
            };
        }

        let result = do_simplify(body);
        let output = result.to_pretty();
        assert!(
            !output.is_empty(),
            "Mixed deep nesting should produce output"
        );
    }
}
