//! Function application simplification methods for Simplifier.

use super::Simplifier;
use crate::decompile::constructor_data::{
    rewrite_constr_exposer_wrapper, rewrite_constr_unpack_pair_projection,
};
use crate::decompile::list_traversal::list_subject_and_tail_depth_owned;
use crate::decompile::simplify::state::DelayRestoreList;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

mod builtin_names;
mod hoist;
mod lambda;

/// Action returned by `simplify_apply_match` for the CPS task loop.
pub(super) enum ApplyAction {
    /// Simplification complete; push result to results stack.
    Done(PseudoExpr),
    /// Re-enter the Apply loop with new (unsimplified) function and args.
    /// The task loop will push `Enter` tasks for each + `ApplyAfterSimplify`.
    ContinueLoop {
        function: PseudoExpr,
        args: Vec<PseudoExpr>,
        /// Delay depth entries to restore after the next simplification round.
        delay_restore: Option<DelayRestoreList>,
    },
    /// Re-simplify the expression through the full CPS pipeline.
    Resimplify(PseudoExpr),
}

impl Simplifier {
    /// Constructs an Apply node and simplifies it via the canonical `Walker`
    /// hook pipeline (`pre_expr` + `post_apply`).
    pub(super) fn simplify_apply(
        &mut self,
        function: PseudoExpr,
        args: Vec<PseudoExpr>,
    ) -> PseudoExpr {
        self.simplify(PseudoExpr::Apply {
            function: PBox::new(function),
            args: args.into(),
        })
    }

    /// Pattern-matching core of Apply simplification.
    ///
    /// Called from the CPS task loop after `func` and `args` are already
    /// simplified.
    pub(super) fn simplify_apply_match(
        &mut self,
        func: PseudoExpr,
        args: Vec<PseudoExpr>,
    ) -> ApplyAction {
        // Flatten nested Apply chains: Apply(Apply(f, [a1]), [a2]) → Apply(f, [a1, a2])
        // This ensures all args to a function are visible for pattern matching (e.g., 3-arg if).
        let (func, args) = {
            let mut f = func;
            let mut a = args;
            while let PseudoExpr::Apply {
                function: inner_fn,
                args: inner_args,
            } = f
            {
                let mut combined = inner_args;
                combined.extend(a);
                a = combined.into_vec();
                f = inner_fn.into_inner();
            }
            (f, a)
        };

        // Canonical form: no-arg application is just the function itself.
        if args.is_empty() {
            return ApplyAction::Done(func);
        }

        // A literal constant in function position is ill-typed UPLC: it can
        // only arise from a constant handler / chooseList nil-default
        // (`\_. c`, or a bare default in handler position) over-applied to
        // its discarded payload during eliminator/lookup recovery, rendering
        // as `0(x)`. Drop the payload application only when no arg carries
        // a strict failpoint, so a real failure is never erased.
        //
        // `Bool` is excluded: recovering `False(payload)` -> `False` is
        // correct here, but a downstream option-recovery pass relabels an
        // un-witnessed `False` as `None`, turning it into a wrong value.
        if matches!(
            func,
            PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Unit
                | PseudoExpr::Data(_)
        ) && args.iter().all(|a| !Self::contains_strict_failpoint(a))
        {
            return ApplyAction::Done(func);
        }

        // Interprocedural CPS dethunking: strip delay() from args when the
        // function is known to always force that parameter.
        let args = if !self.safe_mode {
            if let PseudoExpr::Var { ref name, ref id } = func {
                if let Some(dethunk_indices) =
                    self.tracked_var(&self.dethunk.dethunk_params, name, id.get())
                {
                    args.into_iter()
                        .enumerate()
                        .map(|(i, arg)| {
                            if dethunk_indices.contains(&i) {
                                if let PseudoExpr::Delay(inner) = arg {
                                    inner.into_inner()
                                } else {
                                    arg
                                }
                            } else {
                                arg
                            }
                        })
                        .collect()
                } else {
                    args
                }
            } else {
                args
            }
        } else {
            args
        };

        // Known selector inlining: a Var tracked as a pure selector
        // (fn(params) { param_i }) returns its i-th arg: choose_fst(a, b) → a.
        if !self.safe_mode
            && let PseudoExpr::Var {
                ref name, ref id, ..
            } = func
        {
            for (&(param_count, selected_idx), selector) in self.selectors.selector_vars.iter() {
                if self.selector_binding_matches_ref(selector, name, *id)
                    && param_count == args.len()
                    && selected_idx < args.len()
                {
                    let selected_arg = args
                        .into_iter()
                        .nth(selected_idx)
                        .expect("selected_idx checked against args.len()");
                    return ApplyAction::Done(selected_arg);
                }
            }
        }

        // Resolve a Var to its builtin alias by VarId, not by name, before
        // pattern matching: a typed variable named `fst` must not be confused
        // with a builtin aliased to `fst`.
        if let PseudoExpr::Var {
            ref name, ref id, ..
        } = func
            && let Some(builtin_name) = self.builtin_alias_for_var(name, id.get())
        {
            return ApplyAction::ContinueLoop {
                function: PseudoExpr::BuiltinCall {
                    name: builtin_name,
                    args: vec![].into(),
                },
                args,
                delay_restore: None,
            };
        }

        // Collapse redundant outer force in field-accessed Scott calls:
        // Force(force(v).#k(a1, ...))(b1, ...) -> force(v).#k(a1, ..., b1, ...)
        if !self.safe_mode
            && matches!(
                &func,
                PseudoExpr::Force(inner_force)
                    if matches!(
                        inner_force.as_ref(),
                        PseudoExpr::Apply { function, .. }
                            if matches!(
                                function.as_ref(),
                                PseudoExpr::FieldAccess { record, .. }
                                    if matches!(record.as_ref(), PseudoExpr::Force(_))
                            )
                    )
            )
        {
            let PseudoExpr::Force(inner_force) = func else {
                unreachable!("outer force field-access shape checked above");
            };
            let PseudoExpr::Apply {
                function: inner_fn,
                args: inner_args,
            } = inner_force.into_inner()
            else {
                unreachable!("inner Scott apply shape checked above");
            };
            let PseudoExpr::FieldAccess { record, selector } = inner_fn.into_inner() else {
                unreachable!("inner Scott field access checked above");
            };
            return ApplyAction::ContinueLoop {
                function: PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::field_access_typed(
                        record.into_inner(),
                        selector,
                    )),
                    args: inner_args,
                },
                args,
                delay_restore: None,
            };
        }

        let recursive_call_target = matches!(
            &func,
            PseudoExpr::Var { name, id, .. }
                if self.tracked_binding(&self.recursion.rec_vars, name, id.get())
        ) || matches!(&func, PseudoExpr::RecFn { .. });

        if !self.safe_mode && !recursive_call_target {
            if let Some(hoisted) = self.hoist_let_from_apply_args(func.clone(), args.clone()) {
                return ApplyAction::Done(hoisted);
            }
            if let Some(hoisted_literals) =
                self.hoist_large_data_literals_from_apply_args(func.clone(), args.clone())
            {
                return ApplyAction::Done(hoisted_literals);
            }
        }

        // Identity continuation: f(fn(x) { x }) → f — a CPS-wrapped value applied
        // to the identity continuation is the value itself.
        if args.len() == 1
            && let PseudoExpr::Lambda {
                ref params,
                ref body,
            } = args[0]
            && params.len() == 1
            && let PseudoExpr::Var { name: var_name, .. } = body.as_ref()
            && params[0] == *var_name
        {
            return ApplyAction::Done(func);
        }

        // CPS Option unwrap: f(args..., fn(x) { x }, fail) → expect! f(args...)
        // Identity success + fail continuation mark a Scott-encoded Option.
        if !self.safe_mode && args.len() >= 3 {
            let last = &args[args.len() - 1];
            let second_last = &args[args.len() - 2];
            let is_identity = matches!(
                second_last,
                PseudoExpr::Lambda { params, body }
                    if params.len() == 1
                        && matches!(body.as_ref(), PseudoExpr::Var { name, .. } if params[0] == name.as_str())
            );
            let is_fail = Self::is_fail(last);
            if is_identity && is_fail {
                let mut core_args = args;
                core_args.truncate(core_args.len() - 2);
                let inner_call = PseudoExpr::Apply {
                    function: PBox::new(func),
                    args: core_args.into(),
                };
                return ApplyAction::Done(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::expect_helper()),
                    args: vec![inner_call].into(),
                });
            }
        }

        // Fail(anything) -> fail (applying error to anything is still error)
        if Self::is_fail(&func) {
            return ApplyAction::Done(func);
        }

        // Force(if(cond, delay(body)))(else_arg) → simplify_if(cond, body, else_arg)
        // Handles partially-applied if_then_else where force consumes the delay
        if matches!(
            &func,
            PseudoExpr::Force(inner)
                if matches!(
                    inner.as_ref(),
                    PseudoExpr::BuiltinCall { name, args: builtin_args }
                        if (name == "if" || name == "if_then_else")
                            && builtin_args.len() == 2
                            && !args.is_empty()
                )
        ) {
            let PseudoExpr::Force(inner) = func else {
                unreachable!("partial forced-if shape checked above");
            };
            let PseudoExpr::BuiltinCall {
                args: builtin_args, ..
            } = inner.into_inner()
            else {
                unreachable!("partial forced-if builtin shape checked above");
            };
            let mut builtin_args = builtin_args.into_iter();
            let cond = builtin_args
                .next()
                .expect("partial forced-if condition arg");
            let then_branch = Self::unwrap_delay_owned(
                builtin_args
                    .next()
                    .expect("partial forced-if then branch arg"),
            );
            let mut args = args;
            let residual_args = args.split_off(1);
            let else_branch =
                Self::unwrap_delay_owned(args.pop().expect("partial forced-if else branch arg"));
            let if_result = self.simplify_if(cond, then_branch, else_branch);
            if residual_args.is_empty() {
                return ApplyAction::Done(if_result);
            }
            // More args beyond the 3rd: apply the rest to the if result
            return ApplyAction::ContinueLoop {
                function: if_result,
                args: residual_args,
                delay_restore: None,
            };
        }

        // Convert expect!(x.tag == N, value) or expect!(m == N, value) to
        // when x is { Constr<N> -> value; _ -> fail }
        if (args.len() == 2 || args.len() == 1)
            && let PseudoExpr::Var {
                name: ref fn_name, ..
            } = func
            && fn_name == "expect!"
            && let Some(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left,
                right,
            }) = args.first()
            && let Some((subject, tag_value)) = self.extract_tag_comparison(left, right)
        {
            let value = args
                .into_iter()
                .nth(1)
                .map(Self::unwrap_delay_owned)
                .unwrap_or(PseudoExpr::Unit);
            let clauses = vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(tag_value, 0), vec![]),
                    value,
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::error()),
            ];
            return ApplyAction::Done(self.simplify_when(subject, None, clauses));
        }

        // Expect!(cond, delay(value), ..msg) -> expect!(cond, value, ..msg)
        if (args.len() == 2 || args.len() == 3)
            && matches!(&args[1], PseudoExpr::Delay(_))
            && matches!(&func, PseudoExpr::Var { name, .. } if name == "expect!")
        {
            let original_len = args.len();
            let mut args = args.into_iter();
            let cond = args.next().expect("expect! condition arg");
            let value = args.next().expect("expect! delayed value arg");
            let mut new_args = Vec::with_capacity(original_len);
            new_args.push(cond);
            new_args.push(Self::unwrap_delay_owned(value));
            if let Some(message) = args.next() {
                new_args.push(message);
            }
            return ApplyAction::Done(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::expect_helper()),
                args: new_args.into(),
            });
        }

        // Direct Y-combinator application:
        // (Y-like)(fn(self, args...) { ... }, arg1, ...)
        // > __y_comb_direct(fn(self, args...) { ... }, arg1, ...)
        if !args.is_empty()
            && Self::is_y_combinator(&func)
            && matches!(args.first(), Some(PseudoExpr::Lambda { .. }))
        {
            return ApplyAction::ContinueLoop {
                function: PseudoExpr::helper_symbol("__y_comb_direct"),
                args,
                delay_restore: None,
            };
        }

        // Compiler helper wrappers around unconstr_data:
        // __constr_index_exposer(x) -> Data.constr_index(x)
        // __constr_fields_exposer(x) -> Data.constr_fields(x)
        if args.len() == 1
            && matches!(
                &func,
                PseudoExpr::Var { name, .. }
                    if name == "__constr_index_exposer" || name == "__constr_fields_exposer"
            )
            && let PseudoExpr::Var { name, .. } = func
        {
            let expr = rewrite_constr_exposer_wrapper(&name, args)
                .expect("constr exposer wrapper name checked above");
            return ApplyAction::Done(expr);
        }

        // A Constr in function position IS a Scott-encoded selector: tag N picks
        // the Nth continuation arg and applies the fields to it.
        // Constr<N>(fields)(arg0, arg1, ...) → arg_N(fields) (if N < args.len())
        // Constr<N>()(arg0, arg1, ...) → arg_N (if fields empty)
        if matches!(&func, PseudoExpr::Constr { tag, .. } if *tag < args.len()) {
            let PseudoExpr::Constr { tag, fields, .. } = func else {
                unreachable!("Constr Scott reversal shape checked above");
            };
            let selected = args
                .into_iter()
                .nth(tag)
                .expect("tag checked against args.len()");
            if fields.is_empty() {
                return ApplyAction::ContinueLoop {
                    function: selected,
                    args: Vec::new(),
                    delay_restore: None,
                };
            }
            return ApplyAction::ContinueLoop {
                function: selected,
                args: fields.into_vec(),
                delay_restore: None,
            };
        }

        // Scott-encoded list emptiness check:
        // Expr(fn(_) { Bool(b1) }, Bool(b2)) where b1 != b2
        // → when expr is { [] -> b1; _ -> b2 }
        // Nil selects the first arg, cons applies the second to (head, tail).
        if !self.safe_mode && args.len() == 2 {
            let is_bool_emptiness = matches!(
                args.as_slice(),
                [
                    PseudoExpr::Lambda { params, body },
                    PseudoExpr::Bool(cons_bool),
                ] if params.len() == 1
                    && (params[0] == "_" || !Self::is_var_used(body, &params[0]))
                    && matches!(body.as_ref(), PseudoExpr::Bool(nil_bool) if nil_bool != cons_bool)
            );
            if is_bool_emptiness {
                let mut args = args;
                let cons_val = args.pop().expect("list emptiness cons branch");
                let nil_arg = args.pop().expect("list emptiness nil branch");
                let PseudoExpr::Lambda { body, .. } = nil_arg else {
                    unreachable!("list emptiness lambda shape checked above");
                };
                return ApplyAction::Done(PseudoExpr::When {
                    subject: PBox::new(func),
                    subject_name: None,
                    clauses: vec![
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec![],
                                tail: None,
                            },
                            body.into_inner(),
                        ),
                        WhenClause::new(WhenPattern::Wildcard, cons_val),
                    ],
                });
            }
        }

        // Reversed Scott-encoded boolean pattern:
        // Expr(Bool(b1), fn(_) { Bool(b2) }) where b1 != b2
        // → when expr is { Constr<0> -> b1; Constr<1>(_) -> b2 }
        // In this encoding: Constr<0> (no fields) selects the first (bare) arg,
        // Constr<1> (1 field) applies the second (lambda) arg.
        if !self.safe_mode
            && args.len() == 2
            && let PseudoExpr::Bool(b1) = &args[0]
            && let PseudoExpr::Lambda { params, body } = &args[1]
            && params.len() == 1
            && (params[0] == "_" || !Self::is_var_used(body, &params[0]))
            && let PseudoExpr::Bool(b2) = body.as_ref()
            && b1 != b2
        {
            return ApplyAction::Done(PseudoExpr::When {
                subject: PBox::new(func),
                subject_name: None,
                clauses: vec![
                    WhenClause::new(
                        WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                        PseudoExpr::Bool(*b1),
                    ),
                    WhenClause::new(
                        WhenPattern::constructor(
                            ConstructorShape::unknown_data(1, 1),
                            vec![self.fresh_synthetic_binder("_")],
                        ),
                        PseudoExpr::Bool(*b2),
                    ),
                ],
            });
        }

        // Scott-encoded N-ary selector pattern:
        // expr(fn(a, _) { a }) → expr.fst, expr(fn(_, b) { b }) → expr.snd
        // expr(fn(_, b, _) { b }) → expr.1 — 3+ params take the 0-based index
        // `.fst`/`.snd` here are field accesses, not the UPLC builtins
        // Pair.first/Pair.second.
        if args.len() == 1 {
            let selector_sig = match &args[0] {
                PseudoExpr::Lambda { params, body } if params.len() >= 2 => {
                    if let PseudoExpr::Var { name, id } = body.as_ref() {
                        let used_idx = params.iter().position(|p| {
                            crate::decompile::var_match::ref_matches_binder(name, id.get(), p)
                        });
                        let unused_count = params.iter().filter(|p| *p == "_").count();
                        if unused_count == params.len() - 1 {
                            used_idx.map(|idx| (params.len(), idx))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
                PseudoExpr::Var { name, id } => self.selectors.selector_vars.iter().find_map(
                    |(&(param_count, selected_idx), selector)| {
                        if self.selector_binding_matches_ref(selector, name, *id)
                            && param_count >= 2
                        {
                            Some((param_count, selected_idx))
                        } else {
                            None
                        }
                    },
                ),
                _ => None,
            };

            if let Some((param_count, idx)) = selector_sig {
                let field_name = if param_count == 2 {
                    if idx == 0 {
                        "fst".to_string()
                    } else {
                        "snd".to_string()
                    }
                } else {
                    // Emit the 0-based index here; the late render_prep pass
                    // `normalize_tuple_field_ordinals` rewrites it to the
                    // idiomatic ordinal (`.1st`, `.2nd`, …) — a bare
                    // `.0`/`.7` is not valid surface syntax tuple-access syntax.
                    idx.to_string()
                };
                // Pair.new(a, b).fst → a, Pair.new(a, b).snd → b
                if matches!(
                    &func,
                    PseudoExpr::BuiltinCall { name, args }
                        if (name == "Pair.new" || name == "new_pair")
                            && args.len() == 2
                            && (field_name == "fst" || field_name == "snd")
                ) {
                    let PseudoExpr::BuiltinCall { args, .. } = func else {
                        unreachable!("Pair.new selector shape checked above");
                    };
                    let mut args = args.into_iter();
                    let fst = args.next().expect("Pair.new fst arg should exist");
                    let snd = args.next().expect("Pair.new snd arg should exist");
                    if field_name == "fst" {
                        return ApplyAction::Done(fst);
                    }
                    return ApplyAction::Done(snd);
                }
                return ApplyAction::Done(PseudoExpr::field_access(func, field_name));
            }
        }

        // Single-force Scott destructuring (single-delay encoding):
        // Force(x)(fn(a, b, ...) { body }) → when x is { Constr<0>(a, b, ...) -> body }
        // Requires >= 2 Lambda params (1-param is too ambiguous with CPS callbacks).
        // The selector case (fn(a, _) { a } → .fst) was already handled above.
        if !self.safe_mode
            && args.len() == 1
            && matches!(
                (&func, args.as_slice()),
                (
                    PseudoExpr::Force(_),
                    [PseudoExpr::Lambda { params, .. }]
                ) if params.len() >= 2
            )
        {
            let PseudoExpr::Force(subject) = func else {
                unreachable!("single-force Scott subject checked above");
            };
            let mut args = args;
            let PseudoExpr::Lambda { params, body } =
                args.pop().expect("single-force Scott lambda arg")
            else {
                unreachable!("single-force Scott lambda checked above");
            };
            let arity = params.len();
            return ApplyAction::Done(PseudoExpr::When {
                subject,
                subject_name: None,
                clauses: vec![WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::scott_positional(0, arity), params),
                    body.into_inner(),
                )],
            });
        }

        // Immediate lambda application: fn(x, y) { body }(arg1, arg2) -> let x = arg1; let y = arg2; body
        if let Some((params, _)) = Self::immediate_lambda_parts(&func)
            && params.len() == args.len()
            && !params.is_empty()
        {
            if Self::args_capture_bound_params(&args, params) {
                return ApplyAction::Done(PseudoExpr::Apply {
                    function: PBox::new(func),
                    args: args.into(),
                });
            }
            let (params, body) = match Self::into_immediate_lambda_parts(func) {
                Some(parts) => parts,
                None => unreachable!("checked immediate lambda above"),
            };
            let param_ids = Self::existing_binding_ref_ids(&body, &params);

            // Temporarily propagate known delay depth of call arguments into
            // parameter bindings while simplifying the desugared let-chain body.
            let mut saved_delay_depths: Vec<(String, Option<VarId>, Option<u8>)> = Vec::new();
            for ((param, param_id), arg) in params.iter().zip(param_ids.iter()).zip(args.iter()) {
                let depth = Self::delay_depth(arg);
                if depth > 0 {
                    saved_delay_depths.push((
                        param.to_string(),
                        *param_id,
                        self.tracked_var(&self.delays.delayed_value_depths, param, *param_id),
                    ));
                    self.delays.delayed_value_depths.insert_binding(
                        param.clone(),
                        *param_id,
                        depth,
                    );
                }
            }
            // Pre-track delayed fst/snd selector args:
            // fn(b1) { ... }(delay(fn(_, x) { x })) makes b1 a fail
            // continuation, so force(b1) is the fail path.
            for ((param, param_id), arg) in params.iter().zip(param_ids.iter()).zip(args.iter()) {
                if Self::is_single_delayed_snd_selector(arg) {
                    self.selectors
                        .single_delayed_snd_params
                        .insert_binding(param.clone(), *param_id);
                }
                if Self::is_single_delayed_fst_selector(arg) {
                    self.selectors
                        .single_delayed_fst_params
                        .insert_binding(param.clone(), *param_id);
                }
                if Self::is_delayed_snd_selector(arg).is_some() {
                    self.selectors
                        .delayed_snd_selectors
                        .insert_binding(param.clone(), *param_id);
                }
                if Self::is_delayed_fst_selector(arg).is_some() {
                    self.selectors
                        .delayed_fst_selectors
                        .insert_binding(param.clone(), *param_id);
                }
            }

            // Create nested let bindings for each parameter (in reverse order)
            let mut result: PseudoExpr = body;
            let result_param_ids = Self::existing_binding_ref_ids(&result, &params);
            for ((param, param_id), arg) in params
                .iter()
                .zip(result_param_ids.iter().copied())
                .zip(args)
                .rev()
            {
                result = PseudoExpr::Let {
                    name: param.to_string(),
                    id: Some(param_id.unwrap_or(param.id)),
                    value: PBox::new(arg),
                    body: PBox::new(result),
                };
            }
            let delay_restore = if saved_delay_depths.is_empty() {
                None
            } else {
                Some(saved_delay_depths)
            };
            return ApplyAction::ContinueLoop {
                function: result,
                args: vec![],
                delay_restore,
            };
        }

        // Over-application: fn(x) { body }(a, b, c) -> let x = a; body(b, c)
        // Handles curried IIFE patterns where the lambda returns another function/when.
        if let Some((params, _)) = Self::immediate_lambda_parts(&func)
            && args.len() > params.len()
            && !params.is_empty()
        {
            let bound_args = &args[..params.len()];
            if Self::args_capture_bound_params(bound_args, params) {
                return ApplyAction::Done(PseudoExpr::Apply {
                    function: PBox::new(func),
                    args: args.into(),
                });
            }

            let (params, body) = match Self::into_immediate_lambda_parts(func) {
                Some(parts) => parts,
                None => unreachable!("lambda parts checked above"),
            };
            let mut args = args;
            let remaining_args = args.split_off(params.len());

            // Create nested let bindings, wrapping body in Apply with remaining args
            let mut result: PseudoExpr = PseudoExpr::Apply {
                function: PBox::new(body),
                args: remaining_args.into(),
            };
            let result_param_ids = Self::existing_binding_ref_ids(&result, &params);
            for ((param, param_id), arg) in params.into_iter().zip(result_param_ids).zip(args).rev()
            {
                result = PseudoExpr::Let {
                    name: param.to_string(),
                    id: Some(param_id.unwrap_or(param.id)),
                    value: PBox::new(arg),
                    body: PBox::new(result),
                };
            }
            return ApplyAction::ContinueLoop {
                function: result,
                args: Vec::new(),
                delay_restore: None,
            };
        }

        // Under-application: fn(x, y, z) { body }(a) -> let x = a; fn(y, z) { body }
        // Handles parameterized validators where config is partially applied.
        if let Some((params, _)) = Self::immediate_lambda_parts(&func)
            && !args.is_empty()
            && args.len() < params.len()
        {
            let bound_params = &params[..args.len()];
            if Self::args_capture_bound_params(&args, bound_params) {
                return ApplyAction::Done(PseudoExpr::Apply {
                    function: PBox::new(func),
                    args: args.into(),
                });
            }

            let (mut params, body) = match Self::into_immediate_lambda_parts(func) {
                Some(parts) => parts,
                None => unreachable!("lambda parts checked above"),
            };
            let remaining_params = params.split_off(args.len());
            let bound_params = params;
            let inner = PseudoExpr::Lambda {
                params: remaining_params,
                body: PBox::new(body),
            };
            let mut result = inner;
            let result_param_ids = Self::existing_binding_ref_ids(&result, &bound_params);
            for ((param, param_id), arg) in bound_params
                .into_iter()
                .zip(result_param_ids)
                .zip(args)
                .rev()
            {
                result = PseudoExpr::Let {
                    name: param.to_string(),
                    id: Some(param_id.unwrap_or(param.id)),
                    value: PBox::new(arg),
                    body: PBox::new(result),
                };
            }
            return ApplyAction::ContinueLoop {
                function: result,
                args: Vec::new(),
                delay_restore: None,
            };
        }

        // CPS selector inlining:
        // When all args are Delay(body), and ALL when clause bodies are pure Nth selectors
        // (or fail), inline the delayed args directly into the when clauses.
        //
        //   When x is {
        //     Constr<0> -> fn(a, _) { a } // selects arg[0]
        //     Constr<1> -> fn(_, b) { b } // selects arg[1]
        //   }(delay(val0), delay(val1))
        //
        //   → when x is { Constr<0> -> val0; Constr<1> -> val1 }
        if let PseudoExpr::When { clauses, .. } = &func
            && !args.is_empty()
        {
            let all_args_delayed = args.iter().all(|a| matches!(a, PseudoExpr::Delay(_)));

            if all_args_delayed {
                let arity = args.len();
                let selector_indices: Vec<_> = clauses
                    .iter()
                    .map(|c| Self::is_nth_selector(&c.body, arity))
                    .collect();
                let all_selectors = clauses
                    .iter()
                    .zip(selector_indices.iter())
                    .all(|(c, idx)| idx.is_some() || Self::is_fail(&c.body));

                if all_selectors {
                    let mut remaining_uses = vec![0usize; arity];
                    for idx in selector_indices.iter().flatten() {
                        remaining_uses[*idx] += 1;
                    }

                    let PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } = func
                    else {
                        unreachable!("CPS selector inlining when shape checked above");
                    };
                    let mut delay_bodies: Vec<_> = args
                        .into_iter()
                        .map(|arg| {
                            let PseudoExpr::Delay(body) = arg else {
                                unreachable!("CPS selector inlining delay arg checked above");
                            };
                            Some(body.into_inner())
                        })
                        .collect();
                    let new_clauses: Vec<_> = clauses
                        .into_iter()
                        .zip(selector_indices)
                        .map(|(c, selected_idx)| {
                            if let Some(idx) = selected_idx {
                                let body = if remaining_uses[idx] == 1 {
                                    delay_bodies[idx]
                                        .take()
                                        .expect("last CPS selector delayed body use")
                                } else {
                                    self.clone_with_fresh_ids(
                                        delay_bodies[idx]
                                            .as_ref()
                                            .expect("repeated CPS selector delayed body use"),
                                    )
                                };
                                remaining_uses[idx] = remaining_uses[idx].saturating_sub(1);

                                WhenClause {
                                    pattern: c.pattern,
                                    guard: c.guard,
                                    body,
                                }
                            } else {
                                c // fail stays as-is
                            }
                        })
                        .collect();
                    return ApplyAction::Done(self.simplify_when(
                        subject.into_inner(),
                        subject_name,
                        new_clauses,
                    ));
                }
            }
        }

        // Push application into when/if/let branches. Cheap args (Vars,
        // literals, lambdas, delays) are always distributed; costlier args
        // duplicate into every branch, so only non-safe mode distributes them.
        // A let never duplicates.
        let args_are_cheap = !args.is_empty()
            && args.iter().all(|a| match a {
                PseudoExpr::Var { .. }
                | PseudoExpr::Int(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::Unit
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Lambda { .. } => true,
                // Delay(...) is cheap only when the delayed payload is also cheap.
                // Avoid duplicating heavyweight delayed when/if trees across branches.
                PseudoExpr::Delay(inner) => matches!(
                    inner.as_ref(),
                    PseudoExpr::Var { .. }
                        | PseudoExpr::Int(_)
                        | PseudoExpr::Bool(_)
                        | PseudoExpr::Unit
                        | PseudoExpr::ByteArray(_)
                        | PseudoExpr::String(_)
                        | PseudoExpr::Lambda { .. }
                        | PseudoExpr::Error { .. }
                ),
                _ => false,
            });
        match &func {
            PseudoExpr::When { .. } if args_are_cheap => {
                return ApplyAction::Done(
                    self.distribute_apply_with_shared_args(func.clone(), args),
                );
            }
            PseudoExpr::When { .. } if !self.safe_mode && !args.is_empty() => {
                return ApplyAction::Done(
                    self.distribute_apply_with_shared_args(func.clone(), args),
                );
            }
            PseudoExpr::If { .. } if args_are_cheap => {
                return ApplyAction::Done(
                    self.distribute_apply_with_shared_args(func.clone(), args),
                );
            }
            PseudoExpr::If { .. } if !self.safe_mode && !args.is_empty() => {
                return ApplyAction::Done(
                    self.distribute_apply_with_shared_args(func.clone(), args),
                );
            }
            PseudoExpr::Let { .. } if !args.is_empty() => {
                // Hoist Let chain out of Apply function position:
                // Apply(Let(a, v1, Let(b, v2, f)), args)
                // → Let(a, v1, Let(b, v2, Apply(f, args)))
                let mut lets: Vec<(String, Option<VarId>, PseudoExpr)> = Vec::new();
                let mut inner = func;
                while let PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } = inner
                {
                    lets.push((name, id, value.into_inner()));
                    inner = body.into_inner();
                }
                let mut result = PseudoExpr::Apply {
                    function: PBox::new(inner),
                    args: args.into(),
                };
                // Wrap lets in reverse order (innermost first)
                for (name, id, value) in lets.into_iter().rev() {
                    result = PseudoExpr::Let {
                        name,
                        id,
                        value: PBox::new(value),
                        body: PBox::new(result),
                    };
                }
                return ApplyAction::Resimplify(result);
            }
            _ => {}
        }

        // Direct recursive function application:
        // Rec fn f(x, y) { body }(a, b)
        //   > let f = rec fn ... in let x = a; let y = b; body
        //
        // Applies only when every `_` parameter's argument is a non-thunk value
        // or a delay with no explicit error, so no effect is suppressed.
        if let PseudoExpr::RecFn {
            name: rec_name,
            params,
            body,
        } = &func
            && params.len() == args.len()
            && !params.is_empty()
            && params.iter().zip(args.iter()).all(|(p, a)| {
                p != "_"
                    || ((Self::is_non_thunk_value(a) || Self::is_delay(a))
                        && !Self::contains_explicit_error(a))
            })
        {
            let mut applied_body: PseudoExpr = (**body).clone();
            for (param, arg) in params.iter().zip(args.iter()).rev() {
                if param == "_" {
                    continue;
                }
                applied_body = self.bind_name_in_body(param, arg.clone(), applied_body);
            }

            let retained_func = self.clone_with_fresh_ids(&func);
            let applied_expr = self.bind_name_in_body(rec_name, retained_func, applied_body);
            return ApplyAction::Done(self.simplify(applied_expr));
        }

        // Check for __y_comb_X(fn(self, params...) { body }) -> anonymous RecFn
        if matches!(
            &func,
            PseudoExpr::Var { name, .. } if name.starts_with("__y_comb_")
        ) && matches!(
            args.first(),
            Some(PseudoExpr::Lambda { params, .. }) if !params.is_empty()
        ) {
            let mut args = args.into_iter();
            let PseudoExpr::Lambda { params, body } =
                args.next().expect("__y_comb_ lambda arg checked above")
            else {
                unreachable!("__y_comb_ lambda arg checked above");
            };
            let call_args: Vec<PseudoExpr> = args.collect();
            let mut params = params.into_iter();
            let self_name = params.next().expect("__y_comb_ self param checked above");
            // preserve real-param binders with VarIds intact.
            let real_params: Vec<crate::pseudo::ast::Binder> = params.collect();

            // Use self_name as function name (will be renamed by let if needed)
            let fn_name = self_name.to_string();
            let renamed_body = Self::rename_var(body.as_ref(), self_name.as_str(), &fn_name);
            // Strip self-arg from recursive calls: f(f, a, b) -> f(a, b)
            let stripped_body = Self::strip_rec_self_arg(&renamed_body, &fn_name);
            // Strip thunked self-calls: f() → f
            let stripped_body = if !real_params.is_empty() {
                Self::strip_thunked_self_calls(&stripped_body, &fn_name)
            } else {
                stripped_body
            };

            // If there are additional args, it's a call to the rec fn
            if !call_args.is_empty() {
                // rec(fn(self, x) { ... }, arg1, arg2) -> let fn_name = rec fn ... in fn_name(arg1, arg2)
                // Keep self_name's VarId on both the RecFn name binder and the let binder,
                // so the body's self-refs — which still carry self_name's original id
                // after `rename_var` — resolve against the RecFn's self-name.
                let binder = crate::pseudo::ast::Binder::new(fn_name, self_name.var_id());
                let rec_fn = PseudoExpr::RecFn {
                    name: binder.clone(),
                    params: real_params,
                    body: PBox::new(stripped_body),
                };
                return ApplyAction::Done(self.make_let_for_binder(
                    binder.clone(),
                    rec_fn,
                    PseudoExpr::Apply {
                        function: PBox::new(self.make_var_for_binder(&binder)),
                        args: call_args.into(),
                    },
                ));
            }
            // Just rec(fn(...)) without additional args
            // preserve self_name's VarId
            // on the RecFn name binder.
            return ApplyAction::Done(PseudoExpr::RecFn {
                name: crate::pseudo::ast::Binder::new(fn_name, self_name.var_id()),
                params: real_params,
                body: PBox::new(stripped_body),
            });
        }

        // Check for partial application call: c(x) where c = fn(y) { y == 1 }
        // or c(x) where c = Int.sub(0) (curried builtin)
        if let PseudoExpr::Var {
            ref name, ref id, ..
        } = func
            && let Some((op, operand, curried_is_left)) =
                self.tracked_var(&self.delays.partial_apps, name, id.get())
            && args.len() == 1
        {
            let mut args = args;
            let arg = args.pop().expect("partial application checked single arg");
            let (left, right) = if curried_is_left {
                // Builtin partial app: Int.sub(0)(x) → 0 - x
                (operand, arg)
            } else {
                // Lambda partial app: fn(x) { x == 1 } (x) → x == 1
                (arg, operand)
            };
            return ApplyAction::Done(PseudoExpr::BinOp {
                op,
                left: PBox::new(left),
                right: PBox::new(right),
            });
        }

        // Check for Constr.pack partial application: c(fields) where c = Constr.pack(N)
        // Convert to Data.Constr(N, fields)
        if let PseudoExpr::Var {
            ref name, ref id, ..
        } = func
            && let Some(tag_expr) =
                self.tracked_var(&self.constructors.constr_pack_tags, name, id.get())
            && !args.is_empty()
        {
            let mut args = args;
            let fields = args.remove(0);
            let result = Self::normalize_constructor_data_expr(tag_expr, fields);
            if args.is_empty() {
                return ApplyAction::Done(result);
            }
            // Extra args beyond fields: apply them to the result
            return ApplyAction::ContinueLoop {
                function: result,
                args,
                delay_restore: None,
            };
        }

        // Also handle direct BuiltinCall("Constr.pack", [tag])(fields)
        // This can occur when let-inlining exposes the BuiltinCall directly
        if matches!(
            &func,
            PseudoExpr::BuiltinCall {
                name: bname,
                args: builtin_args,
            } if (*bname == crate::BuiltinId::ConstrPack)
                && builtin_args.len() == 1
                && !args.is_empty()
        ) {
            let mut builtin_args = match func {
                PseudoExpr::BuiltinCall { args, .. } => args,
                _ => unreachable!("Constr.pack apply shape checked above"),
            };
            let tag_expr = builtin_args
                .pop()
                .expect("Constr.pack apply shape checked one tag arg");
            let mut args = args;
            let fields = args.remove(0);
            let result = Self::normalize_constructor_data_expr(tag_expr, fields);
            if args.is_empty() {
                return ApplyAction::Done(result);
            }
            return ApplyAction::ContinueLoop {
                function: result,
                args,
                delay_restore: None,
            };
        }

        // Check for if-continuation pattern: if(cond, fn(_) { then }, fn(_) { else }, Void)
        // This is CPS-style if where the last argument triggers the continuation
        let is_if_func = match &func {
            PseudoExpr::Var { name, .. } => name == "if" || name == "f" || name == "if_then_else",
            PseudoExpr::BuiltinCall {
                name,
                args: builtin_args,
            } => (name == "if" || name == "if_then_else") && builtin_args.is_empty(),
            _ => false,
        };

        // Direct 3-arg if in Apply form: Apply(BuiltinCall("if",[]), [cond, then, else])
        // Only match BuiltinCall("if"), not Var("f") which could be any function.
        if args.len() == 3 {
            let is_strict_if = match &func {
                PseudoExpr::BuiltinCall {
                    name,
                    args: builtin_args,
                } => (name == "if" || name == "if_then_else") && builtin_args.is_empty(),
                _ => false,
            };
            if is_strict_if {
                let mut args = args.into_iter();
                let cond = args.next().expect("if condition arg");
                let then_branch =
                    Self::unwrap_delay_owned(args.next().expect("if then-branch arg"));
                let else_branch =
                    Self::unwrap_delay_owned(args.next().expect("if else-branch arg"));
                return ApplyAction::Done(self.simplify_if(cond, then_branch, else_branch));
            }
        }

        // Partially-applied if in Apply form: BuiltinCall("if", [cond, ...]) applied to remaining args:
        //   Apply(BuiltinCall("if", [cond]), [then, else]) — 1 builtin arg + 2 apply args
        //   Apply(BuiltinCall("if", [cond, then]), [else]) — 2 builtin args + 1 apply arg
        //   Apply(BuiltinCall("if", [cond]), [then, else, trigger]) — 1 builtin arg + 3 apply args (CPS)
        //   Apply(BuiltinCall("if", [cond, then]), [else, trigger]) — 2 builtin args + 2 apply args (CPS)
        if matches!(
            &func,
            PseudoExpr::BuiltinCall {
                name: bname,
                args: builtin_args,
            } if (bname == "if" || bname == "if_then_else")
                && !builtin_args.is_empty()
                && builtin_args.len() + args.len() >= 3
        ) {
            let (bname, mut all_args) = match func {
                PseudoExpr::BuiltinCall { name, args } => (name, args),
                _ => unreachable!("partial Apply-form if shape checked above"),
            };
            all_args.extend(args);
            let total = all_args.len();

            if total == 3 {
                // Standard 3-arg if: if(cond, then, else)
                let mut all_args = all_args.into_iter();
                let cond = all_args.next().expect("partial if condition arg");
                let then_branch =
                    Self::unwrap_delay_owned(all_args.next().expect("partial if then arg"));
                let else_branch =
                    Self::unwrap_delay_owned(all_args.next().expect("partial if else arg"));
                return ApplyAction::Done(self.simplify_if(cond, then_branch, else_branch));
            }

            if !self.safe_mode && total == 4 {
                // 4-arg CPS if: if(cond, then_fn, else_fn, trigger)
                let is_trigger = Self::is_void(&all_args[3])
                    || matches!(&all_args[3], PseudoExpr::Unit)
                    || matches!(&all_args[3], PseudoExpr::Var { .. });
                if is_trigger {
                    let continuation_bodies = Self::extract_continuation_body_ref(&all_args[1])
                        .is_some()
                        && Self::extract_continuation_body_ref(&all_args[2]).is_some();
                    let mut all_args = all_args.into_iter();
                    let cond = all_args.next().expect("partial CPS if condition arg");
                    let then_fn = all_args.next().expect("partial CPS if then function");
                    let else_fn = all_args.next().expect("partial CPS if else function");
                    let trigger = all_args.next().expect("partial CPS if trigger");

                    if continuation_bodies {
                        let then_br = Self::extract_continuation_body_owned(then_fn)
                            .expect("partial CPS if then continuation checked above");
                        let else_br = Self::extract_continuation_body_owned(else_fn)
                            .expect("partial CPS if else continuation checked above");
                        return ApplyAction::Done(self.simplify_if(cond, then_br, else_br));
                    }

                    // Fallback: unwrap delay and apply trigger
                    let then_fn = Self::unwrap_delay_owned(then_fn);
                    let else_fn = Self::unwrap_delay_owned(else_fn);
                    let then_applied = self.simplify(PseudoExpr::Apply {
                        function: PBox::new(then_fn),
                        args: vec![trigger.clone()].into(),
                    });
                    let else_applied = self.simplify(PseudoExpr::Apply {
                        function: PBox::new(else_fn),
                        args: vec![trigger].into(),
                    });
                    return ApplyAction::Done(self.simplify_if(cond, then_applied, else_applied));
                }
            }

            if total >= 4 {
                // Over-applied: merge all into BuiltinCall and let simplify_builtin_call handle it
                return ApplyAction::Done(self.simplify_builtin_call(bname, all_args.into_vec()));
            }

            unreachable!("partial Apply-form if shape checked at least three args");
        }

        if !self.safe_mode && is_if_func && args.len() == 4 {
            // The trigger is the last arg: Unit, a Void `Constr`, or any Var.
            let is_trigger = Self::is_void(&args[3])
                || matches!(&args[3], PseudoExpr::Unit)
                || matches!(&args[3], PseudoExpr::Var { .. });

            if is_trigger {
                // Extract bodies from continuation lambdas
                let then_body = Self::extract_continuation_body_ref(&args[1]);
                let else_body = Self::extract_continuation_body_ref(&args[2]);

                if let (Some(then_br), Some(else_br)) = (then_body, else_body) {
                    let cond = &args[0];

                    // Check for && pattern: if(cond1, fn(_) { cond2 }, fn(_) { False }, Void)
                    if Self::can_short_circuit_with_boolean(cond)
                        && Self::can_short_circuit_with_boolean(then_br)
                        && self.is_false(else_br)
                        && !Self::is_fail(then_br)
                    {
                        let mut args = args.into_iter();
                        let cond = args.next().expect("4-arg CPS if condition arg");
                        let then_fn = args.next().expect("4-arg CPS if then function");
                        let _else_fn = args.next().expect("4-arg CPS if else function");
                        let _trigger = args.next().expect("4-arg CPS if trigger");
                        let then_br = Self::extract_continuation_body_owned(then_fn)
                            .expect("4-arg CPS if then continuation checked above");
                        return ApplyAction::Done(PseudoExpr::BinOp {
                            op: BinaryOp::And,
                            left: PBox::new(cond),
                            right: PBox::new(then_br),
                        });
                    }

                    // Check for || pattern: if(cond1, fn(_) { True }, fn(_) { cond2 }, Void)
                    if Self::can_short_circuit_with_boolean(cond)
                        && Self::can_short_circuit_with_boolean(else_br)
                        && self.is_true(then_br)
                    {
                        let mut args = args.into_iter();
                        let cond = args.next().expect("4-arg CPS if condition arg");
                        let _then_fn = args.next().expect("4-arg CPS if then function");
                        let else_fn = args.next().expect("4-arg CPS if else function");
                        let _trigger = args.next().expect("4-arg CPS if trigger");
                        let else_br = Self::extract_continuation_body_owned(else_fn)
                            .expect("4-arg CPS if else continuation checked above");
                        return ApplyAction::Done(PseudoExpr::BinOp {
                            op: BinaryOp::Or,
                            left: PBox::new(cond),
                            right: PBox::new(else_br),
                        });
                    }

                    // Check for expect! pattern: if(cond, fn(_) { value }, fn(_) { fail }, Void)
                    // The fail message carries through into the 3-arg expect! form. Skip the
                    // wrap when cond is already `when X is { ... _ -> fail }`: the when
                    // encodes the fail, so falling through to simplify_if lets the if-when
                    // merge collapse it to a bare `when`.
                    if Self::is_fail(else_br)
                        && !Self::is_fail(then_br)
                        && !Self::when_has_guardless_wildcard_fail(cond)
                    {
                        let message = Self::fail_message(else_br).map(ToString::to_string);
                        let mut cps_args = args.into_iter();
                        let cond = cps_args.next().expect("4-arg CPS if condition arg");
                        let then_fn = cps_args.next().expect("4-arg CPS if then function");
                        let _else_fn = cps_args.next().expect("4-arg CPS if else function");
                        let _trigger = cps_args.next().expect("4-arg CPS if trigger");
                        let then_br = Self::extract_continuation_body_owned(then_fn)
                            .expect("4-arg CPS if then continuation checked above");
                        let mut args = vec![cond, then_br];
                        if let Some(msg) = message {
                            args.push(PseudoExpr::String(msg));
                        }
                        return ApplyAction::Done(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::expect_helper()),
                            args: args.into(),
                        });
                    }

                    // Check for inverted expect!: if(cond, fn(_) { fail }, fn(_) { value }, Void)
                    // Same as above: carry the fail message, and skip the wrap when cond
                    // already has a guardless wildcard-fail clause.
                    if Self::is_fail(then_br)
                        && !Self::is_fail(else_br)
                        && !Self::when_has_guardless_wildcard_fail(cond)
                    {
                        let msg = Self::fail_message(then_br).map(|m| m.to_string());
                        let mut args = args.into_iter();
                        let cond = args.next().expect("4-arg CPS if condition arg");
                        let _then_fn = args.next().expect("4-arg CPS if then function");
                        let else_fn = args.next().expect("4-arg CPS if else function");
                        let _trigger = args.next().expect("4-arg CPS if trigger");
                        let else_br = Self::extract_continuation_body_owned(else_fn)
                            .expect("4-arg CPS if else continuation checked above");
                        let mut args = vec![
                            PseudoExpr::UnOp {
                                op: UnaryOp::Not,
                                operand: PBox::new(cond),
                            },
                            else_br,
                        ];
                        if let Some(msg) = msg {
                            args.push(PseudoExpr::String(msg));
                        }
                        return ApplyAction::Done(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::expect_helper()),
                            args: args.into(),
                        });
                    }

                    // Regular if expression
                    let mut args = args.into_iter();
                    let cond = args.next().expect("4-arg CPS if condition arg");
                    let then_fn = args.next().expect("4-arg CPS if then function");
                    let else_fn = args.next().expect("4-arg CPS if else function");
                    let _trigger = args.next().expect("4-arg CPS if trigger");
                    let then_br = Self::extract_continuation_body_owned(then_fn)
                        .expect("4-arg CPS if then continuation checked above");
                    let else_br = Self::extract_continuation_body_owned(else_fn)
                        .expect("4-arg CPS if else continuation checked above");
                    return ApplyAction::Done(self.simplify_if(cond, then_br, else_br));
                }

                // Fallback: branches are delay-wrapped or have used parameters.
                // Apply trigger to each branch: if(cond, then_fn, else_fn, trigger)
                // → if cond { then_fn(trigger) } else { else_fn(trigger) }
                let mut args = args.into_iter();
                let cond = args.next().expect("4-arg CPS if condition arg");
                let then_fn =
                    Self::unwrap_delay_owned(args.next().expect("4-arg CPS if then function"));
                let else_fn =
                    Self::unwrap_delay_owned(args.next().expect("4-arg CPS if else function"));
                let trigger = args.next().expect("4-arg CPS if trigger");
                let then_applied = self.simplify(PseudoExpr::Apply {
                    function: PBox::new(then_fn),
                    args: vec![trigger.clone()].into(),
                });
                let else_applied = self.simplify(PseudoExpr::Apply {
                    function: PBox::new(else_fn),
                    args: vec![trigger].into(),
                });
                return ApplyAction::Done(self.simplify_if(cond, then_applied, else_applied));
            }
        }

        // 5-arg CPS-if in Apply form: if(cond, fst_sel, snd_sel, then, else)
        if !self.safe_mode
            && is_if_func
            && args.len() == 5
            && self.is_known_fst_selector(&args[1])
            && self.is_known_snd_selector(&args[2])
        {
            let mut args = args.into_iter();
            let cond = args.next().expect("5-arg CPS if condition arg");
            let _fst_selector = args.next().expect("5-arg CPS if fst selector");
            let _snd_selector = args.next().expect("5-arg CPS if snd selector");
            let then_branch = Self::unwrap_delay_owned(args.next().expect("5-arg CPS if then arg"));
            let else_branch = Self::unwrap_delay_owned(args.next().expect("5-arg CPS if else arg"));
            return ApplyAction::Done(self.simplify_if(cond, then_branch, else_branch));
        }

        // Generic over-application fallback for if-like calls:
        // if(cond, then, else, a, b, ...) -> if(cond, then, else)(a, b, ...)
        if !self.safe_mode && is_if_func && args.len() > 3 {
            let mut args = args;
            let residual_args = args.split_off(3);
            let mut core_args = args.into_iter();
            let cond = core_args.next().expect("generic if condition arg");
            let then_branch =
                Self::unwrap_delay_owned(core_args.next().expect("generic if then arg"));
            let else_branch =
                Self::unwrap_delay_owned(core_args.next().expect("generic if else arg"));
            return ApplyAction::ContinueLoop {
                function: self.simplify_if(cond, then_branch, else_branch),
                args: residual_args,
                delay_restore: None,
            };
        }

        // Lazy choose_list/caseList wrapper pattern:
        // choose_list(list, fn(_) { nil }, fn(head, tail, _) { cons }, Unit)
        // > when list is { [] -> nil; [head, ..tail] -> cons }
        let is_choose_list_func = match &func {
            PseudoExpr::Var { name, .. } => *name == "choose_list" || *name == "List.fold",
            PseudoExpr::BuiltinCall {
                name,
                args: builtin_args,
            } => (*name == crate::BuiltinId::ListFold) && builtin_args.is_empty(),
            _ => false,
        };
        if is_choose_list_func && args.len() == 4 {
            let is_trigger = Self::is_void(&args[3])
                || matches!(&args[3], PseudoExpr::Unit)
                || matches!(&args[3], PseudoExpr::Var { .. });
            if is_trigger {
                let has_empty_case = Self::extract_continuation_body_ref(&args[1]).is_some();
                let has_non_empty_case = Self::is_list_cons_continuation(&args[2]);
                if has_empty_case && has_non_empty_case {
                    let mut args = args;
                    let _trigger = args.pop().expect("choose_list trigger arg");
                    let non_empty_arg = args.pop().expect("choose_list cons continuation arg");
                    let empty_arg = args.pop().expect("choose_list empty continuation arg");
                    let subject = args.pop().expect("choose_list subject arg");
                    let empty_body = Self::extract_continuation_body_owned(empty_arg)
                        .expect("choose_list empty continuation checked above");
                    let (head, tail, cons_body) =
                        Self::extract_list_cons_continuation_owned(non_empty_arg)
                            .expect("choose_list cons continuation checked above");
                    return ApplyAction::Done(PseudoExpr::When {
                        subject: PBox::new(subject),
                        subject_name: None,
                        clauses: vec![
                            WhenClause::new(
                                WhenPattern::List {
                                    elements: vec![],
                                    tail: None,
                                },
                                empty_body,
                            ),
                            WhenClause::new(
                                WhenPattern::List {
                                    elements: vec![head],
                                    tail: Some(tail),
                                },
                                cons_body,
                            ),
                        ],
                    });
                }
            }
        }

        if let PseudoExpr::Var {
            ref name, ref id, ..
        } = func
        {
            // Check for and_fn(cond1, delay(cond2)) -> cond1 && cond2
            if self.is_and_var(name, *id) && args.len() == 2 {
                let mut args = args;
                let right = Self::unwrap_delay_owned(args.pop().expect("and_fn rhs arg"));
                let left = Self::unwrap_delay_owned(args.pop().expect("and_fn lhs arg"));
                return ApplyAction::Done(PseudoExpr::BinOp {
                    op: BinaryOp::And,
                    left: PBox::new(left),
                    right: PBox::new(right),
                });
            }

            // Check for or_fn(cond1, delay(cond2)) -> cond1 || cond2
            if self.is_or_var(name, *id) && args.len() == 2 {
                let mut args = args;
                let right = Self::unwrap_delay_owned(args.pop().expect("or_fn rhs arg"));
                let left = Self::unwrap_delay_owned(args.pop().expect("or_fn lhs arg"));
                return ApplyAction::Done(PseudoExpr::BinOp {
                    op: BinaryOp::Or,
                    left: PBox::new(left),
                    right: PBox::new(right),
                });
            }

            // Direct if call: f(cond, then, else) where f = if
            if name == "f" && args.len() == 3 {
                // Check if this looks like if(cond, delay(then), delay(else))
                if Self::is_delay(&args[1]) || Self::is_delay(&args[2]) {
                    let mut args = args.into_iter();
                    let cond = args.next().expect("direct f-if condition arg");
                    let then_branch =
                        Self::unwrap_delay_owned(args.next().expect("direct f-if then arg"));
                    let else_branch =
                        Self::unwrap_delay_owned(args.next().expect("direct f-if else arg"));

                    // Check for && pattern: if(cond1, delay(cond2), delay(False))
                    if Self::can_short_circuit_with_boolean(&cond)
                        && Self::can_short_circuit_with_boolean(&then_branch)
                        && self.is_false(&else_branch)
                    {
                        return ApplyAction::Done(PseudoExpr::BinOp {
                            op: BinaryOp::And,
                            left: PBox::new(cond),
                            right: PBox::new(then_branch),
                        });
                    }

                    // Check for || pattern: if(cond1, delay(True), delay(cond2))
                    if Self::can_short_circuit_with_boolean(&cond)
                        && Self::can_short_circuit_with_boolean(&else_branch)
                        && self.is_true(&then_branch)
                    {
                        return ApplyAction::Done(PseudoExpr::BinOp {
                            op: BinaryOp::Or,
                            left: PBox::new(cond),
                            right: PBox::new(else_branch),
                        });
                    }

                    return ApplyAction::Done(self.simplify_if(cond, then_branch, else_branch));
                }
            }
        }

        // Reconstitute trace(msg, body) -> Trace { message, value }
        // This can happen when a builtin alias (e.g., debug_7 -> trace) is applied to args.
        if let PseudoExpr::BuiltinCall {
            name: ref bname,
            args: ref builtin_args,
        } = func
            && builtin_args.is_empty()
            && args.len() == 2
            && (bname == "trace" || bname == "debug")
        {
            let mut args = args;
            let value = args.pop().expect("trace value argument");
            let message = args.pop().expect("trace message argument");
            return ApplyAction::Done(PseudoExpr::Trace {
                message: PBox::new(message),
                value: PBox::new(value),
            });
        }

        // Check for partial application: BuiltinCall(arg) -> (op arg) or fn(x) { x op arg }
        if let PseudoExpr::BuiltinCall {
            name,
            args: builtin_args,
        } = &func
            && builtin_args.is_empty()
            && args.len() == 1
        {
            // Partial application of comparison: Int.eq(1) -> (== 1)
            if let Some(op) = Self::partial_builtin_comparison_op(name.as_str()) {
                let mut args = args;
                let arg = args
                    .pop()
                    .expect("builtin partial application checked single arg");
                let binder = self.fresh_synthetic_binder("x");
                return ApplyAction::Done(PseudoExpr::Lambda {
                    params: vec![binder.clone()],
                    body: PBox::new(PseudoExpr::BinOp {
                        op,
                        left: PBox::new(self.make_var_for_binder(&binder)),
                        right: PBox::new(arg),
                    }),
                });
            }
        }

        // Alternative Scott encoding (double-delayed value):
        // Force(force(subject))(branch0, branch1, ...) — Scott case analysis.
        // The value is delay(delay(fn(c0,...) { ci(fields...) })), so double-force
        // yields the selector and the branches apply directly, undelayed.
        // Lambda(params, body) → constructor with fields; other expr → 0-field.
        //
        // 2+ branches is unambiguously Scott encoding (regular thunked functions
        // use single delay, not double); a single branch also requires a Lambda
        // to distinguish it from a thunked function call.
        if !self.safe_mode {
            let has_lambda_branch = args.iter().any(|a| matches!(a, PseudoExpr::Lambda { .. }));
            if (has_lambda_branch || args.len() >= 2)
                && matches!(
                    &func,
                    PseudoExpr::Force(inner) if matches!(inner.as_ref(), PseudoExpr::Force(_))
                )
            {
                let PseudoExpr::Force(inner) = func else {
                    unreachable!("double-delayed Scott outer force checked above");
                };
                let PseudoExpr::Force(subject) = inner.into_inner() else {
                    unreachable!("double-delayed Scott inner force checked above");
                };
                let clauses: Vec<_> = args
                    .into_iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        let (binders, body) = match arg {
                            PseudoExpr::Lambda { params, body } => (params, body.into_inner()),
                            other => (vec![], other),
                        };
                        let arity = binders.len();
                        WhenClause::new(
                            WhenPattern::constructor(
                                ConstructorShape::scott_positional(i, arity),
                                binders,
                            ),
                            body,
                        )
                    })
                    .collect();

                return ApplyAction::Done(PseudoExpr::When {
                    subject,
                    subject_name: None,
                    clauses,
                });
            }
        }

        // Apply(BuiltinCall(comparison/arithmetic, ...), ...) -> BinOp, two cases:
        //   1. Apply(BuiltinCall(name, [a]), [b]) — 1 builtin arg + 1 apply arg
        //   2. Apply(BuiltinCall(name, []), [a, b]) — 0 builtin args + 2 apply args
        let apply_form_binop_op = Self::apply_form_binop_op(&func, args.len());
        if let Some(op) = apply_form_binop_op {
            let mut all_args = match func {
                PseudoExpr::BuiltinCall { args, .. } => args,
                _ => unreachable!("Apply-form BinOp shape checked above"),
            };
            all_args.extend(args);
            let mut all_args = all_args.into_iter();
            let left = all_args.next().expect("Apply-form BinOp left arg");
            let right = all_args.next().expect("Apply-form BinOp right arg");
            let (left, right) = Self::canonicalize_commutative_binop(op, left, right);
            return ApplyAction::Done(PseudoExpr::BinOp {
                op,
                left: PBox::new(left),
                right: PBox::new(right),
            });
        }

        // Handle Apply(BuiltinCall("Pair.first"|"Pair.second", []), [arg])
        // This pattern occurs when force(force(fst_pair)) creates a 0-arg BuiltinCall
        // and the arg is applied separately.
        if let PseudoExpr::BuiltinCall {
            name: ref bname,
            args: ref builtin_args,
        } = func
            && builtin_args.is_empty()
            && args.len() == 1
            && let Some((is_fst, projection, field)) =
                Self::apply_form_pair_selector((*bname).as_str())
        {
            let tracked_subject = if let PseudoExpr::Var {
                name: var_name, id, ..
            } = &args[0]
            {
                self.tracked_var(
                    &self.constructors.constr_unpack_subjects,
                    var_name,
                    id.get(),
                )
            } else {
                None
            };
            if let Some(expr) =
                rewrite_constr_unpack_pair_projection(&args[0], tracked_subject, projection)
            {
                return ApplyAction::Done(expr);
            }
            let mut args = args;
            let record = args.pop().expect("Pair selector checked single arg");
            // Pair.first(Pair.new(a, b)) -> a, Pair.second(Pair.new(a, b)) -> b
            if matches!(
                &record,
                PseudoExpr::BuiltinCall { name, args }
                    if name == "Pair.new" && args.len() == 2
            ) {
                let PseudoExpr::BuiltinCall { args, .. } = record else {
                    unreachable!("Pair.new projection shape checked above");
                };
                let mut args = args.into_iter();
                let fst = args.next().expect("Pair.new fst arg should exist");
                let snd = args.next().expect("Pair.new snd arg should exist");
                if is_fst {
                    return ApplyAction::Done(fst);
                }
                return ApplyAction::Done(snd);
            }
            // General: Pair.first(x) -> x.fst, Pair.second(x) -> x.snd
            return ApplyAction::Done(PseudoExpr::field_access(record, field.to_string()));
        }

        // Data pack/unpack round-trip elimination — Apply form:
        // Apply(BuiltinCall("Data.ByteArray", []), [BuiltinCall("Data.un_bytearray", [x])]) → x
        // Apply(BuiltinCall("ByteArray.to_data", []), [BuiltinCall("Data.to_bytes", [x])]) → x
        if let PseudoExpr::BuiltinCall {
            name: ref bname,
            args: ref builtin_args,
        } = func
            && builtin_args.is_empty()
            && args.len() == 1
            && let Some(inverse_names) = Self::data_round_trip_inverse_names(bname.as_str())
        {
            // Check BuiltinCall form: Apply(outer, [BuiltinCall(inner, [x])])
            let direct_round_trip = matches!(
                &args[0],
                PseudoExpr::BuiltinCall {
                    name: inner_name,
                    args: inner_args,
                } if inverse_names.iter().any(|n| n == inner_name) && inner_args.len() == 1
            );
            if direct_round_trip {
                let mut args = args;
                let arg = args.pop().expect("single round-trip argument");
                let PseudoExpr::BuiltinCall {
                    args: mut inner_args,
                    ..
                } = arg
                else {
                    unreachable!("direct round-trip shape checked above");
                };
                return ApplyAction::Done(
                    inner_args.pop().expect("single inner round-trip argument"),
                );
            }
            // Check Apply form: Apply(outer, [Apply(BuiltinCall(inner, []), [x])])
            let apply_round_trip = matches!(
                &args[0],
                PseudoExpr::Apply {
                    function: inner_fn,
                    args: apply_args,
                } if apply_args.len() == 1
                    && matches!(
                        inner_fn.as_ref(),
                        PseudoExpr::BuiltinCall {
                            name: inner_name,
                            args: inner_builtin_args,
                        } if inverse_names.iter().any(|n| n == inner_name)
                            && inner_builtin_args.is_empty()
                    )
            );
            if apply_round_trip {
                let mut args = args;
                let arg = args.pop().expect("single round-trip apply argument");
                let PseudoExpr::Apply {
                    args: mut apply_args,
                    ..
                } = arg
                else {
                    unreachable!("apply round-trip shape checked above");
                };
                return ApplyAction::Done(
                    apply_args.pop().expect("single apply round-trip argument"),
                );
            }
        }

        // List.head(List.tail^N(x)) → x[N] — Apply form: the BuiltinCall
        // has 0 args and the argument sits in the Apply's args list.
        if let PseudoExpr::BuiltinCall {
            name: ref bname,
            args: ref builtin_args,
        } = func
            && Self::is_apply_form_list_head_builtin(bname.as_str())
            && builtin_args.is_empty()
            && args.len() == 1
        {
            let mut args = args;
            let arg = args.pop().expect("List.head checked single arg");
            let (collection, depth) = list_subject_and_tail_depth_owned(arg);
            return ApplyAction::Done(PseudoExpr::IndexAccess {
                collection: PBox::new(collection),
                index: depth,
            });
        }

        // List.prepend(elem, list) → [elem, ..list] — Apply form:
        // both args sit in the Apply, none in the BuiltinCall.
        if let PseudoExpr::BuiltinCall {
            name: ref bname,
            args: ref builtin_args,
        } = func
            && Self::is_apply_form_list_prepend_builtin(bname.as_str())
            && builtin_args.is_empty()
            && args.len() == 2
            && matches!(&args[1], PseudoExpr::List { .. })
        {
            let mut args = args;
            let list_expr = args.pop().expect("list prepend tail argument should exist");
            let elem = args.pop().expect("list prepend head argument should exist");
            let PseudoExpr::List { mut elements, tail } = list_expr else {
                unreachable!("list-prepend shape checked above");
            };
            elements.insert(0, elem);
            return ApplyAction::Done(PseudoExpr::List { elements, tail });
        }

        ApplyAction::Done(PseudoExpr::Apply {
            function: PBox::new(func),
            args: args.into(),
        })
    }
}

#[cfg(test)]
mod tests;
