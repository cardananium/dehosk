use crate::pseudo::ast::PBox;
use std::collections::HashSet;

mod body;
mod calls;
mod dependencies;
mod display_names;
mod let_chain;
mod references;

use self::body::{
    canonicalize_inverted_recfn_let, is_helper_binding_value, try_hoist_helper_from_body,
};
#[cfg(test)]
use self::calls::{append_helper_call_args, helper_is_direct_call_only};
#[cfg(test)]
pub(crate) use self::dependencies::analyze_dependencies;
pub(crate) use self::dependencies::rollback_unsafe_lifts;
use self::dependencies::{
    binding_references_any, binding_references_any_names, helper_value_is_closed,
};
use self::display_names::{collect_display_names, fresh_reserved_display_name};
pub(crate) use self::let_chain::{LiftedLet, peel_leading_lets, wrap_lifted_lets};
pub(crate) use self::references::{
    BindingTarget, pattern_binds_var, var_is_referenced, var_is_referenced_id_aware,
};
use self::references::{expr_has_shadowing_binder, rename_target_var_display_name};

use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, WhenClause};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

pub(crate) fn hoist_local_helpers(expr: PseudoExpr) -> PseudoExpr {
    run_hoist_local_helpers_fixed_point(expr).0
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HoistFixedPointOutcome {
    Converged { rounds: usize },
    CycleDetected { rounds: usize },
}

fn run_hoist_local_helpers_fixed_point(expr: PseudoExpr) -> (PseudoExpr, HoistFixedPointOutcome) {
    let mut current = expr;
    let mut seen = vec![current.clone()];
    let mut rounds = 0usize;

    loop {
        let mut hoister = HelperValueHoister::new(&current);
        let folded = hoister.fold(current.clone());
        let next = hoist_entry_lambda_helpers(folded, &mut hoister.reserved_display_names);
        rounds += 1;

        if next.structural_eq(&current) {
            return (next, HoistFixedPointOutcome::Converged { rounds });
        }

        if let Some(cycle_index) = seen.iter().position(|prior| prior.structural_eq(&next)) {
            debug_assert!(
                false,
                "hoist_local_helpers entered a structural cycle after {rounds} rounds (cycle starts at step {cycle_index})\ncurrent:\n{current:#?}\nnext:\n{next:#?}"
            );
            return (next, HoistFixedPointOutcome::CycleDetected { rounds });
        }

        seen.push(next.clone());
        current = next;
    }
}

fn wrap_lifted_lets_avoiding_shadowed_refs(
    lifted: Vec<LiftedLet>,
    mut body: PseudoExpr,
    reserved_display_names: &mut HashSet<String>,
) -> PseudoExpr {
    for binding in &lifted {
        reserved_display_names.insert(binding.name.clone());
    }

    for mut binding in lifted.into_iter().rev() {
        let binding_id_concrete = binding
            .id
            .get()
            .unwrap_or_else(VarId::fresh_compat_placeholder);
        // Hoisting widens a helper's scope; freshen only that helper display
        // name when the widened body would otherwise shadow its existing refs.
        if expr_has_shadowing_binder(&body, &binding.name, binding_id_concrete)
            && var_is_referenced_id_aware(&body, binding_id_concrete, &binding.name)
        {
            let fresh_name = fresh_reserved_display_name(
                binding.name.as_str(),
                binding_id_concrete,
                reserved_display_names,
            );
            body = rename_target_var_display_name(
                body,
                binding.name.as_str(),
                binding_id_concrete,
                fresh_name.as_str(),
            );
            // Display-side only. Structural recognizers read
            // `semantic_name`, so they still see the original mint
            // name (`field_2`) and keep producing friendly names
            // like `payload`.
            binding.name = fresh_name;
        }

        reserved_display_names.insert(binding.name.clone());
        body = PseudoExpr::Let {
            name: binding.name,
            id: binding.id,
            value: PBox::new(binding.value),
            body: PBox::new(body),
        };
    }

    body
}

struct HelperValueHoister {
    reserved_display_names: HashSet<String>,
}

impl HelperValueHoister {
    fn new(expr: &PseudoExpr) -> Self {
        let mut reserved_display_names = HashSet::new();
        collect_display_names(expr, &mut reserved_display_names);
        Self {
            reserved_display_names,
        }
    }

    fn wrap_lifted_lets(&mut self, lifted: Vec<LiftedLet>, body: PseudoExpr) -> PseudoExpr {
        wrap_lifted_lets_avoiding_shadowed_refs(lifted, body, &mut self.reserved_display_names)
    }
}

/// One pending step of [`hoist_entry_lambda_helpers`]'s explicit stack.
/// This walk only follows the Let/Lambda/RecFn spine — every other node
/// kind is a leaf.
enum EntrySpineStep {
    Enter(PseudoExpr),
    Post(EntrySpinePost),
}

enum EntrySpinePost {
    LetBody { name: String, id: Option<VarId> },
    Lambda { params: Vec<Binder> },
    RecFn { name: Binder, params: Vec<Binder> },
}

fn hoist_entry_lambda_helpers(
    expr: PseudoExpr,
    reserved_display_names: &mut HashSet<String>,
) -> PseudoExpr {
    let mut steps = vec![EntrySpineStep::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            EntrySpineStep::Enter(expr) => match expr {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(EntrySpineStep::Post(EntrySpinePost::LetBody { name, id }));
                    steps.push(EntrySpineStep::Enter(body.into_inner()));
                    steps.push(EntrySpineStep::Enter(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(EntrySpineStep::Post(EntrySpinePost::Lambda { params }));
                    steps.push(EntrySpineStep::Enter(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(EntrySpineStep::Post(EntrySpinePost::RecFn { name, params }));
                    steps.push(EntrySpineStep::Enter(body.into_inner()));
                }
                other => done.push(other),
            },
            EntrySpineStep::Post(post) => match post {
                EntrySpinePost::LetBody { name, id } => {
                    let body = done.pop().expect("let body");
                    let value = done.pop().expect("let value");
                    done.push(PseudoExpr::Let {
                        name,
                        id,
                        value: PBox::new(value),
                        body: PBox::new(body),
                    });
                }
                EntrySpinePost::Lambda { params } => {
                    let body = done.pop().expect("lambda body");
                    let forbidden: Vec<BindingTarget> =
                        params.iter().map(BindingTarget::from).collect();
                    let (lifted, body) = split_entry_lambda_helper_chain(body, &forbidden);

                    let (safe_lifted, rolled_back) = rollback_unsafe_lifts(lifted, &forbidden);
                    let body = wrap_lifted_lets(rolled_back, body);

                    done.push(wrap_lifted_lets_avoiding_shadowed_refs(
                        safe_lifted,
                        PseudoExpr::Lambda {
                            params,
                            body: PBox::new(body),
                        },
                        reserved_display_names,
                    ));
                }
                EntrySpinePost::RecFn { name, params } => {
                    let body = done.pop().expect("recfn body");
                    let mut forbidden: Vec<BindingTarget> = vec![BindingTarget::from(&name)];
                    forbidden.extend(params.iter().map(BindingTarget::from));
                    let (lifted, body) = split_entry_lambda_helper_chain(body, &forbidden);

                    let (safe_lifted, rolled_back) = rollback_unsafe_lifts(lifted, &forbidden);
                    let body = wrap_lifted_lets(rolled_back, body);

                    done.push(wrap_lifted_lets_avoiding_shadowed_refs(
                        safe_lifted,
                        PseudoExpr::RecFn {
                            name,
                            params,
                            body: PBox::new(body),
                        },
                        reserved_display_names,
                    ));
                }
            },
        }
    }

    debug_assert_eq!(
        done.len(),
        1,
        "hoist_entry_lambda_helpers must leave one result"
    );
    done.pop().expect("hoist_entry_lambda_helpers result")
}

fn split_entry_lambda_helper_chain(
    mut expr: PseudoExpr,
    forbidden: &[BindingTarget],
) -> (Vec<LiftedLet>, PseudoExpr) {
    let mut lifted = Vec::<LiftedLet>::new();
    let mut kept = Vec::<LiftedLet>::new();
    // Track the kept (not-lifted) bindings already passed: lifting a later
    // helper that references one past the enclosing lambda would leave the
    // reference dangling. The same holds for `forbidden` — the binders of
    // the enclosing Lambda/RecFn (params plus the recfn's own name).
    //
    // Capture is checked by id and by name: earlier passes can rename a
    // binder without retargeting the Var use, so a use can carry an
    // authoritative VarId that no longer matches its binding while the
    // reference is still textually present. `var_is_referenced` (via
    // `binding_references_any_names`) handles shadowing, so inner binders
    // of the same name don't false-trip.
    //
    // A capturing binding is kept in place, adjacent to its captor, rather
    // than left to `rollback_unsafe_lifts` — that one reinserts rolled-back
    // bindings at the top of the body and loses their original position. It
    // still runs at the caller as a safety net for transitive in-chain
    // captures.
    let forbidden_names: Vec<String> = forbidden.iter().map(|t| t.name.clone()).collect();
    let mut kept_targets = Vec::<BindingTarget>::new();
    let mut kept_names = Vec::<String>::new();

    loop {
        match expr {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                let binding = LiftedLet {
                    name,
                    id,
                    value: value.into_inner(),
                };

                let can_lift = is_helper_binding_value(&binding.value)
                    && !binding_references_any(&binding, &kept_targets)
                    && !binding_references_any_names(&binding, &kept_names)
                    && !binding_references_any(&binding, forbidden)
                    && !binding_references_any_names(&binding, &forbidden_names);

                if can_lift {
                    lifted.push(binding);
                } else {
                    kept_names.push(binding.name.clone());
                    kept_targets.push(BindingTarget::from(&binding));
                    kept.push(binding);
                }

                expr = body.into_inner();
            }
            other => {
                return (lifted, wrap_lifted_lets(kept, other));
            }
        }
    }
}

impl ExprFolder for HelperValueHoister {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn post_binop(&mut self, op: BinaryOp, left: PseudoExpr, right: PseudoExpr) -> PseudoExpr {
        let (mut lifted, left) = peel_leading_lets(left, |binding, kept_targets| {
            is_helper_binding_value(&binding.value)
                && !binding_references_any(binding, kept_targets)
        });
        let (right_lifted, right) = peel_leading_lets(right, |binding, kept_targets| {
            is_helper_binding_value(&binding.value)
                && !binding_references_any(binding, kept_targets)
        });
        lifted.extend(right_lifted);

        self.wrap_lifted_lets(
            lifted,
            PseudoExpr::BinOp {
                op,
                left: PBox::new(left),
                right: PBox::new(right),
            },
        )
    }

    fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
        let (mut lifted, function) = peel_leading_lets(function, |binding, kept_targets| {
            is_helper_binding_value(&binding.value)
                && !binding_references_any(binding, kept_targets)
        });

        let mut args_out = Vec::with_capacity(args.len());
        for arg in args {
            let (arg_lifted, arg) = peel_leading_lets(arg, |binding, kept_targets| {
                is_helper_binding_value(&binding.value)
                    && !binding_references_any(binding, kept_targets)
            });
            lifted.extend(arg_lifted);
            args_out.push(arg);
        }

        self.wrap_lifted_lets(
            lifted,
            PseudoExpr::Apply {
                function: PBox::new(function),
                args: args_out.into(),
            },
        )
    }

    fn post_if(
        &mut self,
        condition: PseudoExpr,
        then_branch: PseudoExpr,
        else_branch: PseudoExpr,
    ) -> PseudoExpr {
        let (mut lifted, then_branch) = peel_leading_lets(then_branch, |binding, kept_targets| {
            is_helper_binding_value(&binding.value)
                && !binding_references_any(binding, kept_targets)
        });
        let (else_lifted, else_branch) = peel_leading_lets(else_branch, |binding, kept_targets| {
            is_helper_binding_value(&binding.value)
                && !binding_references_any(binding, kept_targets)
        });
        lifted.extend(else_lifted);

        self.wrap_lifted_lets(
            lifted,
            PseudoExpr::If {
                condition: PBox::new(condition),
                then_branch: PBox::new(then_branch),
                else_branch: PBox::new(else_branch),
            },
        )
    }

    fn post_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        let mut lifted = Vec::new();
        let mut clauses_out = Vec::with_capacity(clauses.len());

        for clause in clauses {
            let mut blocked_names = clause.pattern.bound_names();
            if let Some(subject_name) = subject_name.as_ref() {
                blocked_names.push(subject_name.to_string());
            }

            let (clause_lifted, body) = peel_leading_lets(clause.body, |binding, kept_targets| {
                is_helper_binding_value(&binding.value)
                    && !binding_references_any(binding, kept_targets)
                    && !binding_references_any_names(binding, blocked_names.as_slice())
            });
            lifted.extend(clause_lifted);
            clauses_out.push(WhenClause {
                pattern: clause.pattern,
                guard: clause.guard,
                body,
            });
        }

        self.wrap_lifted_lets(
            lifted,
            PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses: clauses_out,
            },
        )
    }

    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        if let Some(canonical) = canonicalize_inverted_recfn_let(name.clone(), id, &value, &body) {
            return canonical;
        }

        if let Some(lifted) =
            try_hoist_helper_from_body(name.clone(), id, value.clone(), body.clone())
        {
            return lifted;
        }

        let id_concrete = id.unwrap_or_else(VarId::fresh_compat_placeholder);
        let (lifted_from_value, value) = peel_leading_lets(value, |binding, kept_targets| {
            is_helper_binding_value(&binding.value)
                && !binding_references_any(binding, kept_targets)
                && !var_is_referenced_id_aware(&binding.value, id_concrete, &name)
        });

        if !lifted_from_value.is_empty() {
            return self.wrap_lifted_lets(
                lifted_from_value,
                PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(body),
                },
            );
        }

        let should_hoist = if let PseudoExpr::Let {
            name: ref inner_name,
            id: Some(inner_id),
            value: ref inner_value,
            body: ref inner_body,
            ..
        } = value
        {
            is_helper_binding_value(inner_value.as_ref())
                && helper_value_is_closed(inner_value.as_ref())
                && !var_is_referenced_id_aware(&body, inner_id, inner_name)
                && !var_is_referenced_id_aware(inner_value.as_ref(), id_concrete, &name)
                && !var_is_referenced_id_aware(inner_body.as_ref(), id_concrete, &name)
        } else {
            false
        };

        if should_hoist
            && let PseudoExpr::Let {
                name: inner_name,
                id: Some(inner_id),
                value: inner_value,
                body: inner_body,
            } = value
        {
            return PseudoExpr::Let {
                name: inner_name,
                id: Some(inner_id),
                value: inner_value,
                body: PBox::new(PseudoExpr::Let {
                    name,
                    id,
                    value: inner_body,
                    body: PBox::new(body),
                }),
            };
        }

        PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }
}

#[cfg(test)]
mod tests;
