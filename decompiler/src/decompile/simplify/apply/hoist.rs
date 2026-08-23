use super::Simplifier;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, WhenClause};
use crate::pseudo::var_id::OptionVarIdGet;

impl Simplifier {
    /// Distribute application args into branches of a when/if expression.
    ///
    /// `(when x is { A -> f; B -> g })(args)` becomes
    /// `when x is { A -> f(args); B -> g(args) }`
    pub(super) fn distribute_apply_with_shared_args(
        &mut self,
        func: PseudoExpr,
        args: Vec<PseudoExpr>,
    ) -> PseudoExpr {
        match func {
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                // Each clause needs a hygienic clone of `args` so
                // binders inside them get distinct VarIds; plain
                // `.clone()` would duplicate the ids and strand
                // cross-clause refs after downstream moves.
                let mut clauses_vec: Vec<_> = clauses.into_iter().collect();
                let last_idx = clauses_vec.len().saturating_sub(1);
                let mut original_args = Some(args);
                let new_clauses = clauses_vec
                    .drain(..)
                    .enumerate()
                    .map(|(i, c)| {
                        let clause_args: Vec<PseudoExpr> = if i == last_idx {
                            // Takes the original args uncloned; the other
                            // clauses cloned fresh sets, so the original
                            // ids stay referenced exactly once.
                            original_args
                                .take()
                                .expect("last distributed when clause should own original args")
                        } else {
                            original_args
                                .as_ref()
                                .expect("original args should be available before the last clause")
                                .iter()
                                .map(|a| self.clone_with_fresh_ids(a))
                                .collect()
                        };
                        WhenClause {
                            pattern: c.pattern,
                            guard: c.guard,
                            body: PseudoExpr::Apply {
                                function: PBox::new(c.body),
                                args: clause_args.into(),
                            },
                        }
                    })
                    .collect();
                self.simplify_when(subject.into_inner(), subject_name, new_clauses)
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                // then/else need distinct arg copies: one branch
                // gets a hygienic clone, the other the original.
                let then_args: Vec<PseudoExpr> =
                    args.iter().map(|a| self.clone_with_fresh_ids(a)).collect();
                let then_applied = PseudoExpr::Apply {
                    function: then_branch,
                    args: then_args.into(),
                };
                let else_applied = PseudoExpr::Apply {
                    function: else_branch,
                    args: args.into(),
                };
                self.simplify_if(condition.into_inner(), then_applied, else_applied)
            }
            _ => PseudoExpr::Apply {
                function: PBox::new(func),
                args: args.into(),
            },
        }
    }

    /// Hoist let bindings from apply args to outer scope.
    ///
    /// `f(let x = v in body)` → `let x = v in f(body)`
    pub(super) fn hoist_let_from_apply_args(
        &mut self,
        func: PseudoExpr,
        args: Vec<PseudoExpr>,
    ) -> Option<PseudoExpr> {
        fn contains_nested_function(expr: &PseudoExpr) -> bool {
            let mut pending: Vec<&PseudoExpr> = vec![expr];
            while let Some(cur) = pending.pop() {
                match cur {
                    PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. } => return true,
                    PseudoExpr::Let { value, body, .. } => {
                        pending.push(body);
                        pending.push(value);
                    }
                    PseudoExpr::Apply { function, args } => {
                        for arg in args.iter().rev() {
                            pending.push(arg);
                        }
                        pending.push(function);
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        pending.push(else_branch);
                        pending.push(then_branch);
                        pending.push(condition);
                    }
                    PseudoExpr::When {
                        subject, clauses, ..
                    } => {
                        for clause in clauses.iter().rev() {
                            pending.push(&clause.body);
                            if let Some(guard) = &clause.guard {
                                pending.push(guard);
                            }
                        }
                        pending.push(subject);
                    }
                    PseudoExpr::List { elements, tail } => {
                        if let Some(tail) = tail {
                            pending.push(tail);
                        }
                        for element in elements.iter().rev() {
                            pending.push(element);
                        }
                    }
                    PseudoExpr::Tuple(elements) => {
                        for element in elements.iter().rev() {
                            pending.push(element);
                        }
                    }
                    PseudoExpr::Pair(left, right) | PseudoExpr::BinOp { left, right, .. } => {
                        pending.push(right);
                        pending.push(left);
                    }
                    PseudoExpr::UnOp { operand, .. }
                    | PseudoExpr::FieldAccess {
                        record: operand, ..
                    }
                    | PseudoExpr::IndexAccess {
                        collection: operand,
                        ..
                    }
                    | PseudoExpr::Delay(operand)
                    | PseudoExpr::Force(operand) => pending.push(operand),
                    PseudoExpr::BuiltinCall { args, .. }
                    | PseudoExpr::Constr { fields: args, .. } => {
                        for arg in args.iter().rev() {
                            pending.push(arg);
                        }
                    }
                    PseudoExpr::Trace { message, value } => {
                        pending.push(value);
                        pending.push(message);
                    }
                    PseudoExpr::Var { .. }
                    | PseudoExpr::Int(_)
                    | PseudoExpr::ByteArray(_)
                    | PseudoExpr::String(_)
                    | PseudoExpr::Bool(_)
                    | PseudoExpr::Unit
                    | PseudoExpr::Error { .. }
                    | PseudoExpr::Raw { .. }
                    | PseudoExpr::Data(_)
                    | PseudoExpr::HelperSymbol(_) => {}
                }
            }
            false
        }

        let i = args.iter().enumerate().find_map(|(i, arg)| {
            if let PseudoExpr::Let {
                name, value, body, ..
            } = arg
            {
                // Keep helper-carrying let chains attached to the argument.
                // Hoisting them across the call can strand captured values and
                // turn explicit local bindings into free vars inside nested rec fns.
                if contains_nested_function(body) {
                    return None;
                }
                let name_used_elsewhere = Self::is_var_used(&func, name)
                    || args
                        .iter()
                        .enumerate()
                        .any(|(j, a)| j != i && Self::is_var_used(a, name));
                if name_used_elsewhere {
                    return None;
                }
                // Guard: ensure free vars in the hoisted value don't collide
                // with vars used in the function or other args.
                let mut value_free_vars = Vec::new();
                Self::collect_referenced_vars(value, &mut value_free_vars);
                let has_capture_conflict = value_free_vars.iter().any(|v| {
                    Self::is_var_used(&func, v)
                        || args
                            .iter()
                            .enumerate()
                            .any(|(j, a)| j != i && Self::is_var_used(a, v))
                });
                if has_capture_conflict {
                    return None;
                }
                return Some(i);
            }
            None
        })?;

        let mut new_args = args;
        let selected_arg = std::mem::replace(&mut new_args[i], PseudoExpr::Unit);
        let PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } = selected_arg
        else {
            unreachable!("selected apply arg should be a let binding");
        };
        new_args[i] = body.into_inner();
        let inner = PseudoExpr::Apply {
            function: PBox::new(func),
            args: new_args.into(),
        };
        Some(match id.get() {
            Some(let_id) => self.simplify_let(name, let_id, value.into_inner(), inner),
            None => self.simplify_compat_let(name, value.into_inner(), inner),
        })
    }

    /// Hoist large data literals from apply args into let bindings.
    ///
    /// `f(#"aabbcc...very long...")` → `let data_literal = #"aabbcc..."; f(data_literal)`
    ///
    /// Mint site: the new `data_literal_N` binder is tagged
    /// `VarKind::DataLiteralHoist` in `var_kinds.kind_annotations`.
    pub(super) fn hoist_large_data_literals_from_apply_args(
        &mut self,
        func: PseudoExpr,
        args: Vec<PseudoExpr>,
    ) -> Option<PseudoExpr> {
        let i = args.iter().position(|arg| {
            Self::static_data_expr_node_count(arg).is_some_and(|count| count > 8)
        })?;
        let lit_name = format!("data_literal_{}", i);
        let binder = self.fresh_synthetic_binder(&lit_name);
        self.var_kinds.kind_annotations.insert(
            binder.id,
            crate::pseudo::nameless::VarKind::DataLiteralHoist,
        );
        let mut new_args = args;
        let lifted = std::mem::replace(&mut new_args[i], self.make_var_for_binder(&binder));
        let inner = PseudoExpr::Apply {
            function: PBox::new(func),
            args: new_args.into(),
        };
        Some(self.make_let_for_binder(binder, lifted, inner))
    }
}
