use std::collections::HashSet;

use super::super::Simplifier;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::decompile::simplify) struct CallArgObservation {
    pub first_var_args: Vec<Option<(String, Option<VarId>)>>,
    pub delayed_args: Vec<bool>,
}

impl Simplifier {
    /// Peel an apply chain to find the root function and all args (in order).
    /// `Apply(Apply(Apply(f, [a1]), [a2]), [a3])` -> `(f, [a1, a2, a3])`
    fn peel_apply_chain(expr: &PseudoExpr) -> (&PseudoExpr, Vec<&PseudoExpr>) {
        let mut current = expr;
        let mut chunks: Vec<&[PseudoExpr]> = Vec::new();

        while let PseudoExpr::Apply { function, args } = current {
            chunks.push(args.as_slice());
            current = function.as_ref();
        }

        let mut collected = Vec::new();
        for chunk in chunks.into_iter().rev() {
            for arg in chunk {
                collected.push(arg);
            }
        }

        (current, collected)
    }

    /// Flatten curried lambda params:
    /// `fn(a) { fn(b) { fn(c) { body } } }` -> `["a", "b", "c"]`
    pub(in crate::decompile::simplify) fn flatten_curried_params(expr: &PseudoExpr) -> Vec<String> {
        let mut result = Vec::new();
        let mut current = expr;

        while let PseudoExpr::Lambda { params, body } = current {
            result.extend(params.iter().map(ToString::to_string));
            current = body.as_ref();
        }

        result
    }

    pub(in crate::decompile::simplify) fn flatten_curried_param_binders(
        expr: &PseudoExpr,
    ) -> Vec<Binder> {
        let mut result = Vec::new();
        let mut current = expr;

        while let PseudoExpr::Lambda { params, body } = current {
            result.extend(params.iter().cloned());
            current = body.as_ref();
        }

        result
    }

    pub(in crate::decompile::simplify) fn collect_call_arg_observations(
        expr: &PseudoExpr,
        fn_name: &str,
        fn_id: Option<VarId>,
    ) -> Vec<CallArgObservation> {
        fn mark_nested_apply_chain_nodes(expr: &PseudoExpr, skipped: &mut HashSet<usize>) {
            let mut current = expr;
            while let PseudoExpr::Apply { function, .. } = current {
                let next = function.as_ref();
                if matches!(next, PseudoExpr::Apply { .. }) {
                    skipped.insert(next as *const PseudoExpr as usize);
                }
                current = next;
            }
        }

        struct CallArgObservationCollector<'a> {
            fn_name: &'a str,
            fn_id: Option<VarId>,
            results: Vec<CallArgObservation>,
            skipped_nested_apply_nodes: HashSet<usize>,
        }

        impl ExprVisitor for CallArgObservationCollector<'_> {
            fn visit_apply(
                &mut self,
                expr: &PseudoExpr,
                _function: &PseudoExpr,
                _args: &[PseudoExpr],
            ) {
                let expr_id = expr as *const PseudoExpr as usize;
                if self.skipped_nested_apply_nodes.remove(&expr_id) {
                    return;
                }
                let (root, all_args) = Simplifier::peel_apply_chain(expr);
                if let PseudoExpr::Var { name, id, .. } = root
                    && Simplifier::ref_matches_var_id(name, *id, self.fn_name, self.fn_id)
                    && !all_args.is_empty()
                {
                    let first_var_args = all_args
                        .iter()
                        .map(|arg| {
                            let inner = Simplifier::unwrap_delay_ref(arg);
                            if let PseudoExpr::Var { name, id, .. } = inner {
                                Some((name.clone(), *id))
                            } else {
                                None
                            }
                        })
                        .collect();
                    let delayed_args = all_args
                        .iter()
                        .map(|arg| matches!(arg, PseudoExpr::Delay(_)))
                        .collect();
                    self.results.push(CallArgObservation {
                        first_var_args,
                        delayed_args,
                    });
                    mark_nested_apply_chain_nodes(expr, &mut self.skipped_nested_apply_nodes);
                }
            }
        }

        let mut collector = CallArgObservationCollector {
            fn_name,
            fn_id,
            results: Vec::new(),
            skipped_nested_apply_nodes: HashSet::new(),
        };
        collector.walk(expr);
        collector.results
    }
}
