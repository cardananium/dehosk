use crate::builtins::BuiltinId;
use crate::decompile::constructor_data::normalize_constructor_data_expr;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::fold::ExprFolder;

/// Hoist Let/RecFn bindings out of expect! conditions:
/// `expect!(let name = RecFn { ... } in inner_condition)`
/// becomes `let name = RecFn { ... } in expect!(inner_condition)`,
/// avoiding an `expect! rec fn foo(...)` rendering.
pub(crate) fn hoist_let_from_expect(expr: PseudoExpr) -> PseudoExpr {
    struct HoistExpectLet;

    impl ExprFolder for HoistExpectLet {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
            if matches!(&function, PseudoExpr::Var { name, .. } if name == "expect!")
                && !args.is_empty()
                && let PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } = &args[0]
                && matches!(
                    value.as_ref(),
                    PseudoExpr::RecFn { .. } | PseudoExpr::Lambda { .. }
                )
            {
                let mut new_expect_args = vec![body.as_ref().clone()];
                new_expect_args.extend(args[1..].iter().cloned());
                return PseudoExpr::Let {
                    name: name.clone(),
                    id: *id,
                    value: value.clone(),
                    body: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(function),
                        args: new_expect_args.into(),
                    }),
                };
            }

            PseudoExpr::Apply {
                function: PBox::new(function),
                args: args.into(),
            }
        }
    }

    HoistExpectLet.fold(expr)
}

/// Normalize `BuiltinCall("Data.Constr", [Int(N), List([f1, f2, ...])])` -> `Constr<N>(f1, f2, ...)`.
/// Runs as a late pass after all simplification is done.
pub(crate) fn normalize_data_constr_calls(expr: PseudoExpr) -> PseudoExpr {
    struct DataConstrNorm;

    impl ExprFolder for DataConstrNorm {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_builtin_call(&mut self, name: BuiltinId, args: Vec<PseudoExpr>) -> PseudoExpr {
            if *name == crate::BuiltinId::DataConstr && args.len() == 2 {
                return normalize_constructor_data_expr(args[0].clone(), args[1].clone());
            }
            PseudoExpr::BuiltinCall {
                name,
                args: args.into(),
            }
        }
    }

    DataConstrNorm.fold(expr)
}
