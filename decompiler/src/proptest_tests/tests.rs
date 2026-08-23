#[allow(unused_imports)]
use super::*;
use proptest::prelude::*;
use std::rc::Rc;

use crate::decompile::DecompileOptions;
use crate::decompile::mid::lower::decompile_via_mir;
use crate::pseudo::ast::PseudoExpr;

use uplc::ast::{Constant, DeBruijn, NamedDeBruijn, Program, Term};
use uplc::builtins::DefaultFunction;

/// Generate leaf UPLC terms (no recursion).
fn arb_leaf_term() -> impl Strategy<Value = Term<NamedDeBruijn>> {
    prop_oneof![
        any::<i64>().prop_map(|n| Term::Constant {
            value: Rc::new(Constant::Integer(n.into())),
            uniq_id: 0,
        }),
        Just(Term::Constant {
            value: Rc::new(Constant::Bool(true)),
            uniq_id: 0,
        }),
        Just(Term::Constant {
            value: Rc::new(Constant::Bool(false)),
            uniq_id: 0,
        }),
        Just(Term::Constant {
            value: Rc::new(Constant::Unit),
            uniq_id: 0,
        }),
        Just(Term::Error { uniq_id: 0 }),
        // Fully-applied builtins
        (any::<i64>(), any::<i64>()).prop_map(|(a, b)| {
            Term::Apply {
                function: Rc::new(Term::Apply {
                    function: Rc::new(Term::Builtin {
                        fun: DefaultFunction::AddInteger,
                        uniq_id: 0,
                    }),
                    argument: Rc::new(Term::Constant {
                        value: Rc::new(Constant::Integer(a.into())),
                        uniq_id: 0,
                    }),
                    uniq_id: 0,
                }),
                argument: Rc::new(Term::Constant {
                    value: Rc::new(Constant::Integer(b.into())),
                    uniq_id: 0,
                }),
                uniq_id: 0,
            }
        }),
    ]
}

/// Generate UPLC terms up to the given nesting depth.
fn arb_term(depth: u32) -> impl Strategy<Value = Term<NamedDeBruijn>> {
    if depth == 0 {
        return arb_leaf_term().boxed();
    }

    prop_oneof![
        3 => arb_leaf_term(),
        2 => arb_term(depth - 1).prop_map(|body| {
            Term::Lambda {
                parameter_name: Rc::new(NamedDeBruijn {
                    text: "x".to_string(),
                    index: DeBruijn::new(0),
                }),
                body: Rc::new(body),
                uniq_id: 0,
            }
        }),
        2 => (arb_term(depth - 1), arb_term(depth - 1)).prop_map(|(f, arg)| {
            Term::Apply {
                function: Rc::new(f),
                argument: Rc::new(arg),
                uniq_id: 0,
            }
        }),
        // Let pattern: Apply(Lambda(v, body), value)
        2 => (arb_term(depth - 1), arb_term(depth - 1)).prop_map(|(value, body)| {
            Term::Apply {
                function: Rc::new(Term::Lambda {
                    parameter_name: Rc::new(NamedDeBruijn {
                        text: "v".to_string(),
                        index: DeBruijn::new(0),
                    }),
                    body: Rc::new(body),
                    uniq_id: 0,
                }),
                argument: Rc::new(value),
                uniq_id: 0,
            }
        }),
        1 => arb_term(depth - 1).prop_map(|inner| {
            Term::Force {
                body: Rc::new(Term::Delay {
                    body: Rc::new(inner),
                    uniq_id: 0,
                }),
                uniq_id: 0,
            }
        }),
        1 => arb_term(depth - 1).prop_map(|inner| {
            Term::Delay {
                body: Rc::new(inner),
                uniq_id: 0,
            }
        }),
        // Constr (V3)
        1 => (0..4usize, proptest::collection::vec(arb_term(depth - 1), 0..3))
            .prop_map(|(tag, fields)| {
                Term::Constr { tag, fields, uniq_id: 0 }
            }),
    ]
    .boxed()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// Decompiling any simple term must not panic.
    /// Returning an error is acceptable; panicking is not.
    #[test]
    fn decompile_never_panics(term in arb_term(3)) {
        let program = Program { version: (1, 1, 0), term };
        let result = crate::decompile::decompile_program(&program, DecompileOptions::default());
        let _ = result;
    }

    /// Decompiling the same program twice must yield identical output.
    #[test]
    fn simplify_is_idempotent(term in arb_term(3)) {
        let program = Program { version: (1, 1, 0), term };
        let opts = DecompileOptions::default();
        if let Ok(result1) = crate::decompile::decompile_program(&program, opts.clone()) {
            if let Ok(result2) = crate::decompile::decompile_program(&program, opts) {
                prop_assert_eq!(result1, result2);
            }
        }
    }

    /// The MIR pipeline must not panic on any simple term.
    #[test]
    fn mir_never_panics(term in arb_term(3)) {
        let program = Program { version: (1, 1, 0), term };
        if let Ok((pseudo, _sm, _vr)) = decompile_via_mir(&program, None) {
            let output = pseudo.to_pretty();
            let is_error = matches!(pseudo, PseudoExpr::Error { .. });
            prop_assert!(!output.is_empty() || is_error);
        }
    }

    /// When decompilation succeeds the pretty-printed output must be non-empty.
    #[test]
    fn pretty_print_produces_output(term in arb_term(3)) {
        let program = Program { version: (1, 1, 0), term };
        if let Ok(output) = crate::decompile::decompile_program(&program, DecompileOptions::default()) {
            prop_assert!(!output.is_empty());
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Nested terms must not cause panics in any pipeline.
    #[test]
    fn nested_terms_dont_panic(term in arb_term(3)) {
        let program = Program { version: (1, 1, 0), term };
        let _ = crate::decompile::decompile_program(&program, DecompileOptions::default());
        if let Ok((pseudo, _, _)) = decompile_via_mir(&program, None) {
            let _ = pseudo.to_pretty();
        }
    }
}
