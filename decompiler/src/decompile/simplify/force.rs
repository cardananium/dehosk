//! Force/delay simplification methods for Simplifier.

use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

use super::Simplifier;

impl Simplifier {
    fn selector_passthrough_lambda(&mut self, kept_name: &str, keep_first: bool) -> PseudoExpr {
        let kept = self.fresh_synthetic_binder(kept_name);
        let dropped = self.fresh_synthetic_binder("_");
        let params = if keep_first {
            vec![kept.clone(), dropped]
        } else {
            vec![dropped, kept.clone()]
        };

        PseudoExpr::Lambda {
            params,
            body: PBox::new(self.make_var_for_binder(&kept)),
        }
    }

    pub(super) fn simplify_force(&mut self, inner: PseudoExpr) -> PseudoExpr {
        // force(and_fn/or_fn(a, delay(b))). Must run before inner is simplified:
        // simplify_apply rewrites the Apply into a BinOp and hides the pattern from
        // the post-simplification check.
        if let PseudoExpr::Apply { function, args } = &inner
            && let PseudoExpr::Var { name, id, .. } = function.as_ref()
        {
            let is_and = args.len() == 2 && self.is_and_var(name, *id);
            let is_or = args.len() == 2 && self.is_or_var(name, *id);
            if !self.safe_mode && (is_and || is_or) {
                let PseudoExpr::Apply { mut args, .. } = inner else {
                    unreachable!("force and/or Apply shape checked above");
                };
                let left_arg = args.remove(0);
                let right_arg = args.remove(0);
                let left = Self::unwrap_delay(&self.simplify(left_arg));
                let right = Self::unwrap_delay(&self.simplify(right_arg));
                return PseudoExpr::BinOp {
                    op: if is_and { BinaryOp::And } else { BinaryOp::Or },
                    left: PBox::new(left),
                    right: PBox::new(right),
                };
            }
        }

        let mut inner = self.simplify(inner);

        // force(v) where v is a tracked selector binder: delay(fn(_, x) { x })
        // is the CPS fail path — the second (error) continuation.
        if let PseudoExpr::Var { name, id, .. } = &inner {
            if self.tracked_binding(&self.selectors.non_thunk_vars, name, id.get()) {
                return inner;
            }
            if self.tracked_binding(&self.selectors.single_delayed_snd_params, name, id.get()) {
                return self.selector_passthrough_lambda("err", false);
            }
            if self.tracked_binding(&self.selectors.single_delayed_fst_params, name, id.get()) {
                return self.selector_passthrough_lambda("ok", true);
            }

            // Double-delay snd/fst selector from tracked let bindings.
            if self.tracked_binding(&self.selectors.delayed_snd_selectors, name, id.get()) {
                return self.selector_passthrough_lambda("err", false);
            }
            if self.tracked_binding(&self.selectors.delayed_fst_selectors, name, id.get()) {
                return self.selector_passthrough_lambda("ok", true);
            }

            // General force/delay cancellation handled in post-pass (cancel_force_delay_vars)
        }

        // force(force(f)) where f = delay(delay(fn(x, _) { x })) unwraps to the bare
        // selector fn(x, _) { x }.
        if let PseudoExpr::Force(inner_force) = &inner
            && let PseudoExpr::Var { name, id, .. } = inner_force.as_ref()
        {
            // fst selector: Ok/Some
            if self.tracked_binding(&self.selectors.delayed_fst_selectors, name, id.get()) {
                return self.selector_passthrough_lambda("x", true);
            }
            // snd selector: Err/None
            if self.tracked_binding(&self.selectors.delayed_snd_selectors, name, id.get()) {
                return self.selector_passthrough_lambda("y", false);
            }
            if let Some((delay_count, delayed_expr)) =
                self.tracked_var(&self.recursion.delayed_rec_vars, name, id.get())
                && delay_count >= 2
            {
                // Safe unwrap for variables proven to be delay^n(Y-combinator):
                // Force(force(v)) = delay^(n-2)(Y).
                let mut unwrapped = self.clone_with_fresh_ids(&delayed_expr);
                let mut to_strip = 2u8;
                while to_strip > 0 {
                    if let PseudoExpr::Delay(inner_delay) = unwrapped {
                        unwrapped = inner_delay.into_inner();
                        to_strip -= 1;
                    } else {
                        break;
                    }
                }
                if delay_count > 2 {
                    unwrapped = Self::build_delay_chain(unwrapped, delay_count - 2);
                }
                return self.simplify(unwrapped);
            }
        }

        // Force(force(selector_var)(...)) with a known selector: rewrite to a
        // direct lambda application and keep simplifying under the outer force.
        loop {
            if let PseudoExpr::Apply { function, args } = &inner
                && let PseudoExpr::Force(inner_force) = function.as_ref()
                && let PseudoExpr::Var { name, id, .. } = inner_force.as_ref()
            {
                let selector = if self.tracked_binding(
                    &self.selectors.single_delayed_snd_params,
                    name,
                    id.get(),
                ) {
                    Some(self.selector_passthrough_lambda("err", false))
                } else if self.tracked_binding(
                    &self.selectors.single_delayed_fst_params,
                    name,
                    id.get(),
                ) {
                    Some(self.selector_passthrough_lambda("ok", true))
                } else if self.tracked_binding(
                    &self.selectors.delayed_snd_selectors,
                    name,
                    id.get(),
                ) {
                    Some(self.selector_passthrough_lambda("err", false))
                } else if self.tracked_binding(
                    &self.selectors.delayed_fst_selectors,
                    name,
                    id.get(),
                ) {
                    Some(self.selector_passthrough_lambda("ok", true))
                } else {
                    None
                };

                if let Some(selector_lambda) = selector {
                    let applied = PseudoExpr::Apply {
                        function: PBox::new(selector_lambda),
                        args: args.clone(),
                    };
                    inner = self.simplify(applied);
                    continue;
                }
            }
            break;
        }

        // Collapse the redundant outer force on a field-accessed Scott call:
        // Force(force(v).#k(a1, ...)) -> force(v).#k(a1, ...)
        if !self.safe_mode
            && let PseudoExpr::Apply { function, args } = &inner
            && let PseudoExpr::FieldAccess {
                record, selector, ..
            } = function.as_ref()
            && matches!(record.as_ref(), PseudoExpr::Force(_))
        {
            return self.simplify_apply(
                PseudoExpr::field_access_typed((**record).clone(), selector.clone()),
                (args.clone()).into_vec(),
            );
        }

        // Force(force(partial_if)(then, else)) where partial_if = force(if_alias)(cond)
        // or inline: force(force(force(if_alias)(cond))(then, else))
        // > if cond then then else else
        if let PseudoExpr::Apply { function, args } = &inner
            && args.len() == 2
            && let Some(cond) = self.partial_if_cond_from_forced_function(function)
        {
            let then_branch = Self::unwrap_delay(&args[0]);
            let else_branch = Self::unwrap_delay(&args[1]);

            if !self.safe_mode
                && Self::can_short_circuit_with_boolean(&cond)
                && Self::can_short_circuit_with_boolean(&then_branch)
                && self.is_false(&else_branch)
            {
                return PseudoExpr::BinOp {
                    op: BinaryOp::And,
                    left: PBox::new(cond),
                    right: PBox::new(then_branch),
                };
            }
            if !self.safe_mode
                && Self::can_short_circuit_with_boolean(&cond)
                && Self::can_short_circuit_with_boolean(&else_branch)
                && self.is_true(&then_branch)
            {
                return PseudoExpr::BinOp {
                    op: BinaryOp::Or,
                    left: PBox::new(cond),
                    right: PBox::new(else_branch),
                };
            }
            if let Some(expect_expr) =
                self.maybe_emit_expect(cond.clone(), then_branch.clone(), else_branch.clone())
            {
                return expect_expr;
            }

            return self.simplify_if(cond, then_branch, else_branch);
        }

        // Force(force(partial_choose_list)(empty, non_empty))
        // where partial_choose_list = force(choose_list_alias)(list),
        // or inline: force(force(force(choose_list_alias)(list))(empty, non_empty))
        // > when list is { [] -> empty, _ -> non_empty }
        if let PseudoExpr::Apply { function, args } = &inner
            && args.len() == 2
            && let Some(list) = self.partial_choose_list_subject_from_forced_function(function)
        {
            let empty_case = Self::unwrap_delay(&args[0]);
            let non_empty_case = Self::unwrap_delay(&args[1]);

            if !self.safe_mode && Self::is_fail(&empty_case) {
                let cond = PseudoExpr::UnOp {
                    op: UnaryOp::Not,
                    operand: PBox::new(PseudoExpr::builtin_id(
                        crate::builtins::BuiltinId::ListIsEmpty,
                        vec![list],
                    )),
                };
                if let Some(expect_expr) =
                    self.maybe_emit_expect(cond.clone(), non_empty_case.clone(), empty_case)
                {
                    return expect_expr;
                }
                return PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::expect_helper()),
                    args: vec![cond, non_empty_case].into(),
                };
            }

            return PseudoExpr::When {
                subject: PBox::new(list),
                subject_name: None,
                clauses: vec![
                    WhenClause::new(
                        WhenPattern::List {
                            elements: vec![],
                            tail: None,
                        },
                        empty_case,
                    ),
                    WhenClause::new(WhenPattern::Wildcard, non_empty_case),
                ],
            };
        }

        // Scott-encoded N-constructor case analysis:
        // Force(force(z)(branch0, branch1, ...)) where branches have delay/lambda shapes
        // → when z is { Constr<0>(...) -> body0; Constr<1>(...) -> body1; ... }
        if let PseudoExpr::Apply { function, args } = &inner
            && !self.safe_mode
            && !args.is_empty()
            && let PseudoExpr::Force(inner_force) = function.as_ref()
        {
            let has_explicit_scott_branch = args.iter().any(|arg| {
                matches!(arg, PseudoExpr::Delay(_) | PseudoExpr::Lambda { .. })
                    || Self::is_fail(arg)
            });
            let branches: Vec<_> = args
                .iter()
                .map(|arg| {
                    Self::extract_scott_branch(arg)
                        .or_else(|| self.extract_scott_branch_from_delayed(arg))
                        .or_else(|| {
                            if has_explicit_scott_branch {
                                if let PseudoExpr::Var { .. } = arg {
                                    Some((vec![], arg.clone()))
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        })
                })
                .collect();

            if branches.iter().all(|b| b.is_some()) {
                let subject = self.simplify(inner_force.as_ref().clone());

                let clauses: Vec<_> = branches
                    .into_iter()
                    .enumerate()
                    .map(|(i, b)| {
                        let (params, body) = b.unwrap();
                        let arity = params.len();
                        WhenClause::new(
                            WhenPattern::constructor(
                                ConstructorShape::scott_positional(i, arity),
                                params,
                            ),
                            self.simplify(body),
                        )
                    })
                    .collect();

                return PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name: None,
                    clauses,
                };
            }
        }

        // force(g(list, delay(empty), delay(non_empty))): the list-fold shape,
        // whether g is an alias or List.fold itself.
        if let PseudoExpr::Apply { function, args } = &inner {
            let is_list_fold = match function.as_ref() {
                PseudoExpr::Var { name, id, .. } => {
                    name == "g"
                        || name == "choose_list"
                        || name == "List.fold"
                        || self
                            .builtin_alias_for_var(name, id.get())
                            .is_some_and(|v| v == crate::builtins::BuiltinId::ListFold)
                }
                PseudoExpr::Force(inner_force) => {
                    if let PseudoExpr::Var { name, id, .. } = inner_force.as_ref() {
                        self.builtin_alias_for_var(name, id.get())
                            .is_some_and(|v| v == crate::builtins::BuiltinId::ListFold)
                    } else if let PseudoExpr::BuiltinCall {
                        name,
                        args: builtin_args,
                    } = inner_force.as_ref()
                    {
                        (*name == crate::BuiltinId::ListFold) && builtin_args.is_empty()
                    } else {
                        false
                    }
                }
                PseudoExpr::BuiltinCall {
                    name,
                    args: builtin_args,
                } => (*name == crate::BuiltinId::ListFold) && builtin_args.is_empty(),
                _ => false,
            };

            if !self.safe_mode && is_list_fold && args.len() == 3 {
                let list = args[0].clone();
                let empty_case = Self::unwrap_delay(&args[1]);
                let non_empty_case = Self::unwrap_delay(&args[2]);

                // Empty case fails: the fold is really an assertion that list is non-empty.
                if Self::is_fail(&empty_case) {
                    return PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::expect_helper()),
                        args: vec![
                            PseudoExpr::UnOp {
                                op: UnaryOp::Not,
                                operand: PBox::new(PseudoExpr::builtin_id(
                                    crate::builtins::BuiltinId::ListIsEmpty,
                                    vec![list],
                                )),
                            },
                            non_empty_case,
                        ]
                        .into(),
                    };
                }

                // General when on list
                return PseudoExpr::When {
                    subject: PBox::new(list),
                    subject_name: None,
                    clauses: vec![
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec![],
                                tail: None,
                            },
                            empty_case,
                        ),
                        WhenClause::new(WhenPattern::Wildcard, non_empty_case),
                    ],
                };
            }
        }

        // force(and_fn(a, delay(b))) -> a && b; or_fn likewise -> a || b
        if let PseudoExpr::Apply { function, args } = &inner
            && let PseudoExpr::Var { name, id, .. } = function.as_ref()
        {
            if !self.safe_mode && self.is_and_var(name, *id) && args.len() == 2 {
                let left = Self::unwrap_delay(&args[0]);
                let right = Self::unwrap_delay(&args[1]);
                return PseudoExpr::BinOp {
                    op: BinaryOp::And,
                    left: PBox::new(left),
                    right: PBox::new(right),
                };
            }

            if !self.safe_mode && self.is_or_var(name, *id) && args.len() == 2 {
                let left = Self::unwrap_delay(&args[0]);
                let right = Self::unwrap_delay(&args[1]);
                return PseudoExpr::BinOp {
                    op: BinaryOp::Or,
                    left: PBox::new(left),
                    right: PBox::new(right),
                };
            }

            // Expand partial-if lambda: fn(x) { if(x, then_val) } called with 2 args
            // force(f(a, delay(b))) → if(a, then_val, b) → simplify_if handles && / ||
            if !self.safe_mode
                && args.len() == 2
                && let Some(then_val) =
                    self.tracked_var(&self.booleans.partial_if_then_vals, name, id.get())
            {
                let cond = args[0].clone();
                let then_branch = Self::unwrap_delay(&then_val);
                let else_branch = Self::unwrap_delay(&args[1]);
                return self.simplify_if(cond, then_branch, else_branch);
            }

            // f is usually bound to if_then_else
            if !self.safe_mode && name == "f" && args.len() == 3 {
                let cond = args[0].clone();
                let then_branch = Self::unwrap_delay(&args[1]);
                let else_branch = Self::unwrap_delay(&args[2]);

                // if(cond, False, True) -> !cond
                if self.is_false(&then_branch)
                    && self.is_true(&else_branch)
                    && Self::can_short_circuit_with_boolean(&cond)
                {
                    return PseudoExpr::UnOp {
                        op: UnaryOp::Not,
                        operand: PBox::new(cond),
                    };
                }

                // if(cond1, delay(cond2), delay(False)) -> cond1 && cond2
                if self.is_false(&else_branch)
                    && Self::can_short_circuit_with_boolean(&cond)
                    && Self::can_short_circuit_with_boolean(&then_branch)
                {
                    return PseudoExpr::BinOp {
                        op: BinaryOp::And,
                        left: PBox::new(cond),
                        right: PBox::new(then_branch),
                    };
                }

                // if(cond1, delay(True), delay(cond2)) -> cond1 || cond2
                if self.is_true(&then_branch)
                    && Self::can_short_circuit_with_boolean(&cond)
                    && Self::can_short_circuit_with_boolean(&else_branch)
                {
                    return PseudoExpr::BinOp {
                        op: BinaryOp::Or,
                        left: PBox::new(cond),
                        right: PBox::new(else_branch),
                    };
                }

                return self.simplify_if(cond, then_branch, else_branch);
            }
        }

        // force(force(builtin))
        if let PseudoExpr::Force(inner2) = &inner {
            if let PseudoExpr::Var { name, id, .. } = inner2.as_ref()
                && let Some(builtin_name) = self.builtin_alias_for_var(name, id.get())
                && Self::is_force2_builtin(builtin_name)
            {
                return PseudoExpr::BuiltinCall {
                    name: Self::nice_builtin_name(builtin_name),
                    args: vec![].into(),
                };
            }
            if let PseudoExpr::BuiltinCall { name, args } = inner2.as_ref()
                && args.is_empty()
                && Self::is_force2_builtin(*name)
            {
                return PseudoExpr::BuiltinCall {
                    name: Self::nice_builtin_name(*name),
                    args: vec![].into(),
                };
            }
        }

        // force(builtin)
        if let PseudoExpr::BuiltinCall { name, args } = &inner
            && args.is_empty()
            && Self::is_force1_builtin(*name)
        {
            return PseudoExpr::BuiltinCall {
                name: Self::nice_builtin_name(*name),
                args: vec![].into(),
            };
        }

        // Force(BuiltinCall("if", [cond, delay(then), delay(else)])) -> simplify_if(cond, then, else)
        // The force consumes the delay wrapping around the selected branch.
        if let PseudoExpr::BuiltinCall { ref name, ref args } = inner
            && (name == "if" || name == "if_then_else")
            && args.len() == 3
        {
            let cond = args[0].clone();
            let then_branch = Self::unwrap_delay(&args[1]);
            let else_branch = Self::unwrap_delay(&args[2]);
            return self.simplify_if(cond, then_branch, else_branch);
        }

        // force(delay(x)) -> x
        if let PseudoExpr::Delay(inner2) = inner {
            return inner2.into_inner();
        }

        // Push force through leading let/trace wrappers iteratively:
        // Force(let x = v in b) -> let x = v in force(b)
        // force(trace(m, v)) -> trace(m, force(v))
        if matches!(&inner, PseudoExpr::Let { .. } | PseudoExpr::Trace { .. }) {
            return self.simplify_force_through_wrappers(inner);
        }

        // force(binop) -> binop; an operator result is never a thunk
        if matches!(inner, PseudoExpr::BinOp { .. } | PseudoExpr::UnOp { .. }) {
            return inner;
        }

        // force(simple_value) -> simple_value; the delay is already stripped
        if Self::is_non_thunk_value(&inner) {
            return inner;
        }

        // force(if cond { ... } else { ... })
        if let PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } = &inner
        {
            // force(if cond { False } else { True }) -> !cond
            if !self.safe_mode && self.is_false(then_branch) && self.is_true(else_branch) {
                return PseudoExpr::UnOp {
                    op: UnaryOp::Not,
                    operand: condition.clone(),
                };
            }
            // force(if cond { True } else { False }) -> just cond (identity)
            if !self.safe_mode && self.is_true(then_branch) && self.is_false(else_branch) {
                return (**condition).clone();
            }
            // force(if cond { value } else { fail }) -> expect!(cond, value)
            //
            // If cond is itself a `when` with a guardless wildcard-fail
            // clause it already encodes the fail, and wrapping it would give
            // the non-idiomatic `expect! when X is { ... _ -> fail }`, so
            // return the `when` directly.
            if !self.safe_mode && Self::is_fail(else_branch) && !Self::is_fail(then_branch) {
                if Self::when_has_guardless_wildcard_fail(condition.as_ref()) {
                    if Self::is_void(then_branch) {
                        return (**condition).clone();
                    }
                    // Non-Void then_branch: fall through to the generic
                    // handling below.
                } else {
                    // Lift a `fail @"msg"` message into the 3-arg
                    // `expect!(cond, value, msg)` form, which pretty-prints
                    // as `expect! cond, @"msg"`. Strip any leftover delay
                    // around the value so the body is not `delay(value)`.
                    let mut args = vec![(**condition).clone(), Self::unwrap_delay(then_branch)];
                    if let Some(msg) = Self::fail_message(else_branch) {
                        args.push(PseudoExpr::String(msg.to_string()));
                    }
                    return PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::expect_helper()),
                        args: args.into(),
                    };
                }
            }
            // force(if cond { fail } else { value }) -> expect!(!cond, value)
            // with any fail message lifted into the 3-arg form.
            if !self.safe_mode && Self::is_fail(then_branch) && !Self::is_fail(else_branch) {
                let msg = Self::fail_message(then_branch).map(|m| m.to_string());
                let mut args = vec![
                    PseudoExpr::UnOp {
                        op: UnaryOp::Not,
                        operand: condition.clone(),
                    },
                    Self::unwrap_delay(else_branch),
                ];
                if let Some(msg) = msg {
                    args.push(PseudoExpr::String(msg));
                }
                return PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::expect_helper()),
                    args: args.into(),
                };
            }
            // force(if cond { then } else { else }) where neither is fail
            return self.simplify_if(
                (**condition).clone(),
                Self::unwrap_delay(then_branch),
                Self::unwrap_delay(else_branch),
            );
        }

        // Force(when ...) -> when ... with branch delays unwrapped
        if let PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } = &inner
        {
            let clauses = clauses
                .iter()
                .map(|c| WhenClause {
                    pattern: c.pattern.clone(),
                    guard: c.guard.clone(),
                    body: Self::unwrap_delay(&c.body),
                })
                .collect();
            return PseudoExpr::When {
                subject: subject.clone(),
                subject_name: subject_name.clone(),
                clauses,
            };
        }

        // force(and(a, delay(b))) -> a && b
        if let PseudoExpr::Apply { function, args } = &inner
            && let PseudoExpr::Var { name, .. } = function.as_ref()
            && !self.safe_mode
            && name == "and"
            && args.len() == 2
        {
            let left = Self::unwrap_delay(&args[0]);
            let right = Self::unwrap_delay(&args[1]);
            return PseudoExpr::BinOp {
                op: BinaryOp::And,
                left: PBox::new(left),
                right: PBox::new(right),
            };
        }

        // force(f(cond, delay(then), delay(else))) where f is if_then_else
        // reached through a variable, an alias, or a 0-arg BuiltinCall.
        if let PseudoExpr::Apply { function, args } = &inner {
            let is_if_call = match function.as_ref() {
                PseudoExpr::Var { name, id, .. } => {
                    name == "f"
                        || name == "if"
                        || name == "if_then_else"
                        || self
                            .builtin_alias_for_var(name, id.get())
                            .is_some_and(|v| v == crate::builtins::BuiltinId::IfThenElse)
                }
                PseudoExpr::Force(inner_force) => {
                    if let PseudoExpr::Var { name, id, .. } = inner_force.as_ref() {
                        self.builtin_alias_for_var(name, id.get())
                            .is_some_and(|v| v == crate::builtins::BuiltinId::IfThenElse)
                    } else {
                        false
                    }
                }
                PseudoExpr::BuiltinCall {
                    name,
                    args: builtin_args,
                } => (name == "if" || name == "if_then_else") && builtin_args.is_empty(),
                _ => false,
            };

            if is_if_call && args.len() == 3 {
                let cond = args[0].clone();
                let then_branch = Self::unwrap_delay(&args[1]);
                let else_branch = Self::unwrap_delay(&args[2]);

                // if(cond1, delay(cond2), delay(False)) -> cond1 && cond2
                if !self.safe_mode
                    && Self::can_short_circuit_with_boolean(&cond)
                    && Self::can_short_circuit_with_boolean(&then_branch)
                    && self.is_false(&else_branch)
                {
                    return PseudoExpr::BinOp {
                        op: BinaryOp::And,
                        left: PBox::new(cond),
                        right: PBox::new(then_branch),
                    };
                }

                // if(cond1, delay(True), delay(cond2)) -> cond1 || cond2
                if !self.safe_mode
                    && Self::can_short_circuit_with_boolean(&cond)
                    && Self::can_short_circuit_with_boolean(&else_branch)
                    && self.is_true(&then_branch)
                {
                    return PseudoExpr::BinOp {
                        op: BinaryOp::Or,
                        left: PBox::new(cond),
                        right: PBox::new(else_branch),
                    };
                }

                // if(cond, delay(value), delay(fail)) -> expect!, with any fail
                // message carried into the 3-arg form.
                if !self.safe_mode && Self::is_fail(&else_branch) && !Self::is_fail(&then_branch) {
                    let mut args = vec![cond, then_branch];
                    if let Some(msg) = Self::fail_message(&else_branch) {
                        args.push(PseudoExpr::String(msg.to_string()));
                    }
                    return PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::expect_helper()),
                        args: args.into(),
                    };
                }

                // if(cond, delay(fail), delay(value)) -> expect!(!cond, value),
                // with any fail message carried into the 3-arg form.
                if !self.safe_mode && Self::is_fail(&then_branch) && !Self::is_fail(&else_branch) {
                    let msg = Self::fail_message(&then_branch).map(|m| m.to_string());
                    let mut args = vec![
                        PseudoExpr::UnOp {
                            op: UnaryOp::Not,
                            operand: PBox::new(cond),
                        },
                        else_branch,
                    ];
                    if let Some(msg) = msg {
                        args.push(PseudoExpr::String(msg));
                    }
                    return PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::expect_helper()),
                        args: args.into(),
                    };
                }

                // Regular if
                return self.simplify_if(cond, then_branch, else_branch);
            }
        }

        if let PseudoExpr::Force(inner2) = &inner {
            // Inner force already reduced to an operator: drop both.
            if matches!(
                inner2.as_ref(),
                PseudoExpr::BinOp { .. } | PseudoExpr::UnOp { .. }
            ) {
                return (**inner2).clone();
            }
        }

        // A fully-evaluated inner (If, BinOp, When, ...) makes the force a no-op —
        // simplify_apply turns Apply(BuiltinCall("if",[]), args) into If first.
        if matches!(
            &inner,
            PseudoExpr::If { .. }
                | PseudoExpr::BinOp { .. }
                | PseudoExpr::When { .. }
                | PseudoExpr::Bool(_)
                | PseudoExpr::Int(_)
                | PseudoExpr::Unit
                | PseudoExpr::Constr { .. }
                | PseudoExpr::Trace { .. }
                | PseudoExpr::Error { .. }
        ) {
            return inner;
        }
        // Also strip force from expect!(...) calls
        if let PseudoExpr::Apply { ref function, .. } = inner
            && let PseudoExpr::Var { name, .. } = function.as_ref()
            && name == "expect!"
        {
            return inner;
        }

        PseudoExpr::Force(PBox::new(inner))
    }

    fn simplify_force_through_wrappers(&mut self, expr: PseudoExpr) -> PseudoExpr {
        enum ForceWrapper {
            Let {
                name: String,
                id: Option<VarId>,
                value: PBox,
            },
            Trace {
                message: PBox,
            },
        }

        let mut wrappers = Vec::new();
        let mut current = expr;

        loop {
            match current {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    wrappers.push(ForceWrapper::Let { name, id, value });
                    current = body.into_inner();
                }
                PseudoExpr::Trace { message, value } => {
                    wrappers.push(ForceWrapper::Trace { message });
                    current = value.into_inner();
                }
                _ => break,
            }
        }

        let mut forced = self.simplify_force(current);
        while let Some(wrapper) = wrappers.pop() {
            forced = match wrapper {
                ForceWrapper::Let { name, id, value } => PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body: PBox::new(forced),
                },
                ForceWrapper::Trace { message } => PseudoExpr::Trace {
                    message,
                    value: PBox::new(forced),
                },
            };
        }
        forced
    }
}
