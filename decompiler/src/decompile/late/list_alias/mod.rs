use crate::BuiltinId;
use crate::decompile::helper::hoist::var_is_referenced_id_aware;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

/// Recognise a list-cons builtin. `BuiltinId::from_name` folds
/// `"cons_list"`, `"mk_cons"` and `"List.prepend"` into `ListPrepend`, and
/// `"List.cons"` into `ListCons`; no name maps to `"MkCons"`, so there is
/// no arm for it.
fn is_list_cons_builtin(id: BuiltinId) -> bool {
    matches!(id, BuiltinId::ListPrepend | BuiltinId::ListCons)
}

pub(crate) fn extract_nullary_list_prepend_alias_value(expr: &PseudoExpr) -> Option<BuiltinId> {
    match expr {
        PseudoExpr::BuiltinCall { name, args }
            if args.is_empty() && is_list_cons_builtin(*name) =>
        {
            Some(*name)
        }
        PseudoExpr::Apply { function, args }
            if args.is_empty()
                && matches!(
                    function.as_ref(),
                    PseudoExpr::BuiltinCall { name, args: builtin_args }
                        if builtin_args.is_empty() && is_list_cons_builtin(*name)
                ) =>
        {
            match function.as_ref() {
                PseudoExpr::BuiltinCall { name, .. } => Some(*name),
                _ => None,
            }
        }
        _ => None,
    }
}

pub(crate) fn repair_list_prepend_alias_lets(expr: PseudoExpr) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;

    struct Repair;

    impl ExprFolder for Repair {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_let(
            &mut self,
            name: String,
            id: Option<VarId>,
            value: PseudoExpr,
            body: PseudoExpr,
        ) -> PseudoExpr {
            if extract_nullary_list_prepend_alias_value(&value).is_some()
                && let Some(alias_id) = id
            {
                let rewritten_body = rewrite_list_prepend_alias_uses(body, &name, alias_id);
                if !var_is_referenced_id_aware(&rewritten_body, alias_id, &name) {
                    return rewritten_body;
                }

                return PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(rewritten_body),
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

    Repair.fold(expr)
}

fn binder_shadows_alias_name_fallback(
    binder_name: &str,
    binder_id: VarId,
    alias_name: &str,
    alias_id: VarId,
) -> bool {
    binder_id != alias_id && binder_name == alias_name
}

fn pattern_shadows_alias_name_fallback(
    pattern: &WhenPattern,
    alias_name: &str,
    alias_id: VarId,
) -> bool {
    match pattern {
        WhenPattern::Constructor { fields, .. } => fields.iter().any(|field| {
            binder_shadows_alias_name_fallback(field.as_str(), field.id, alias_name, alias_id)
        }),
        WhenPattern::List { elements, tail } => {
            elements.iter().any(|element| {
                binder_shadows_alias_name_fallback(
                    element.as_str(),
                    element.id,
                    alias_name,
                    alias_id,
                )
            }) || tail.as_ref().is_some_and(|tail| {
                binder_shadows_alias_name_fallback(tail.as_str(), tail.id, alias_name, alias_id)
            })
        }
        WhenPattern::Tuple(fields) => fields.iter().any(|field| {
            binder_shadows_alias_name_fallback(field.as_str(), field.id, alias_name, alias_id)
        }),
        WhenPattern::Pair(a, b) => {
            binder_shadows_alias_name_fallback(a.as_str(), a.id, alias_name, alias_id)
                || binder_shadows_alias_name_fallback(b.as_str(), b.id, alias_name, alias_id)
        }
        WhenPattern::Var(v) => {
            binder_shadows_alias_name_fallback(v.as_str(), v.id, alias_name, alias_id)
        }
        WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
    }
}

fn matches_alias_var(
    expr: &PseudoExpr,
    alias_name: &str,
    alias_id: VarId,
    fallback_shadowed: bool,
) -> bool {
    matches!(
        expr,
        PseudoExpr::Var { name, id, .. }
            if *id == Some(alias_id)
                || (!fallback_shadowed && id.get().is_none() && name == alias_name)
    )
}

/// Split a node into a SHELL — every immediate child replaced by a `Unit`
/// placeholder — plus those children in `map_children` order. The shell is
/// refilled by [`join_children`], which re-walks the same slots in the same
/// order, so the placeholders are never observed.
fn split_children(expr: PseudoExpr) -> (PseudoExpr, Vec<PseudoExpr>) {
    let mut kids: Vec<PseudoExpr> = Vec::new();
    let shell = crate::decompile::render_prep::scope_recurse::map_children(expr, |c| {
        kids.push(c);
        PseudoExpr::Unit
    });
    (shell, kids)
}

/// Put rewritten children back into a shell from [`split_children`].
fn join_children(shell: PseudoExpr, kids: Vec<PseudoExpr>) -> PseudoExpr {
    let mut kids = kids.into_iter();
    crate::decompile::render_prep::scope_recurse::map_children(shell, |_| {
        kids.next().expect("split_children left one child per slot")
    })
}

/// Takes the last `n` items off `done` — the children of the node being
/// reassembled, left there in source order by the walk.
fn take_done(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
    let at = done.len() - n;
    done.split_off(at)
}

/// A job on [`rewrite_list_prepend_alias_uses`]'s stack. The scope is the
/// `fallback_shadowed` flag, carried on the job instead of on a call frame.
enum AliasStep {
    Visit(PseudoExpr, bool),
    LetBody {
        name: String,
        id: Option<VarId>,
        body: PseudoExpr,
        fallback_shadowed: bool,
    },
    Post(AliasPost),
}

/// Everything about a node that is NOT one of its child expressions, held
/// while those children are being rewritten.
enum AliasPost {
    Let {
        name: String,
        id: Option<VarId>,
    },
    /// The `Apply` arm inspects its rewritten callee before deciding whether
    /// to fold the call into a `List`, so it is its own step.
    Apply {
        arg_count: usize,
        fallback_shadowed: bool,
    },
    When {
        subject_name: Option<crate::pseudo::ast::Binder>,
        /// Per clause: its pattern (never descended into) and whether it had
        /// a guard.
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    /// A node with no post-decision: its `split_children` shell plus its
    /// child count.
    Plain(PseudoExpr, usize),
}

/// The scope is the `fallback_shadowed` flag: a binder that shadows the
/// alias NAME (without being the alias) turns off the name-only fallback
/// match for its own subtree. `Lambda`, `RecFn` and each `When` clause
/// compute it before descending, so they can be plain shells; `Let` cannot,
/// because it mints a `fresh_compat_placeholder` for an id-less binder and
/// that mint must stay between the value walk and the body walk — hence the
/// separate `LetBody` step. Children are pushed in REVERSE so they pop in
/// source order and are popped off `done` in that same order.
pub(crate) fn rewrite_list_prepend_alias_uses(
    expr: PseudoExpr,
    alias_name: &str,
    alias_id: VarId,
) -> PseudoExpr {
    let mut steps: Vec<AliasStep> = vec![AliasStep::Visit(expr, false)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            AliasStep::Visit(expr, fallback_shadowed) => match expr {
                PseudoExpr::Var { .. }
                | PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::Unit
                | PseudoExpr::Raw { .. }
                | PseudoExpr::Data(_)
                | PseudoExpr::HelperSymbol(_)
                | PseudoExpr::Error { .. } => done.push(expr),
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(AliasStep::LetBody {
                        name,
                        id,
                        body: body.into_inner(),
                        fallback_shadowed,
                    });
                    steps.push(AliasStep::Visit(value.into_inner(), fallback_shadowed));
                }
                PseudoExpr::Lambda { params, body } => {
                    let body_shadowed = fallback_shadowed
                        || params.iter().any(|param| {
                            binder_shadows_alias_name_fallback(
                                param.as_str(),
                                param.id,
                                alias_name,
                                alias_id,
                            )
                        });
                    steps.push(AliasStep::Post(AliasPost::Plain(
                        PseudoExpr::Lambda {
                            params,
                            body: PBox::new(PseudoExpr::Unit),
                        },
                        1,
                    )));
                    steps.push(AliasStep::Visit(body.into_inner(), body_shadowed));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    let body_shadowed = fallback_shadowed
                        || binder_shadows_alias_name_fallback(
                            name.as_str(),
                            name.id,
                            alias_name,
                            alias_id,
                        )
                        || params.iter().any(|param| {
                            binder_shadows_alias_name_fallback(
                                param.as_str(),
                                param.id,
                                alias_name,
                                alias_id,
                            )
                        });
                    steps.push(AliasStep::Post(AliasPost::Plain(
                        PseudoExpr::RecFn {
                            name,
                            params,
                            body: PBox::new(PseudoExpr::Unit),
                        },
                        1,
                    )));
                    steps.push(AliasStep::Visit(body.into_inner(), body_shadowed));
                }
                PseudoExpr::Apply { function, args } => {
                    let arg_count = args.len();
                    steps.push(AliasStep::Post(AliasPost::Apply {
                        arg_count,
                        fallback_shadowed,
                    }));
                    for arg in args.into_vec().into_iter().rev() {
                        steps.push(AliasStep::Visit(arg, fallback_shadowed));
                    }
                    steps.push(AliasStep::Visit(function.into_inner(), fallback_shadowed));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let subject_name_binds_alias = subject_name.as_ref().is_some_and(|binder| {
                        binder_shadows_alias_name_fallback(
                            binder.as_str(),
                            binder.id,
                            alias_name,
                            alias_id,
                        )
                    });
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    // Built in source order, then drained onto `steps` in
                    // reverse so the jobs pop in source order.
                    let mut jobs: Vec<AliasStep> = Vec::new();
                    for clause in clauses {
                        let binds_alias = subject_name_binds_alias
                            || pattern_shadows_alias_name_fallback(
                                &clause.pattern,
                                alias_name,
                                alias_id,
                            );
                        let clause_shadowed = fallback_shadowed || binds_alias;
                        clause_meta.push((clause.pattern, clause.guard.is_some()));
                        if let Some(guard) = clause.guard {
                            jobs.push(AliasStep::Visit(guard, clause_shadowed));
                        }
                        jobs.push(AliasStep::Visit(clause.body, clause_shadowed));
                    }
                    steps.push(AliasStep::Post(AliasPost::When {
                        subject_name,
                        clause_meta,
                    }));
                    while let Some(job) = jobs.pop() {
                        steps.push(job);
                    }
                    steps.push(AliasStep::Visit(subject.into_inner(), fallback_shadowed));
                }
                // The remaining arms carried the scope through unchanged and
                // were plain `map_children` rebuilds, in exactly this child
                // order.
                other => {
                    let (shell, kids) = split_children(other);
                    steps.push(AliasStep::Post(AliasPost::Plain(shell, kids.len())));
                    for kid in kids.into_iter().rev() {
                        steps.push(AliasStep::Visit(kid, fallback_shadowed));
                    }
                }
            },
            AliasStep::LetBody {
                name,
                id,
                body,
                fallback_shadowed,
            } => {
                let binder_id = id.unwrap_or_else(VarId::fresh_compat_placeholder);
                let body_shadowed = fallback_shadowed
                    || binder_shadows_alias_name_fallback(&name, binder_id, alias_name, alias_id);
                steps.push(AliasStep::Post(AliasPost::Let { name, id }));
                steps.push(AliasStep::Visit(body, body_shadowed));
            }
            AliasStep::Post(post) => {
                let rebuilt = match post {
                    AliasPost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    AliasPost::Apply {
                        arg_count,
                        fallback_shadowed,
                    } => {
                        let mut parts = take_done(&mut done, 1 + arg_count);
                        let args: Vec<_> = parts.split_off(1);
                        let function = parts.pop().expect("apply callee");

                        if matches_alias_var(&function, alias_name, alias_id, fallback_shadowed)
                            && args.len() == 2
                        {
                            let mut args = args;
                            let tail_expr =
                                args.pop().expect("list prepend tail argument should exist");
                            let head = args.pop().expect("list prepend head argument should exist");

                            if let PseudoExpr::List { mut elements, tail } = tail_expr {
                                elements.insert(0, head);
                                done.push(PseudoExpr::List { elements, tail });
                                continue;
                            }

                            done.push(PseudoExpr::List {
                                elements: vec![head].into(),
                                tail: Some(PBox::new(tail_expr)),
                            });
                            continue;
                        }

                        PseudoExpr::Apply {
                            function: PBox::new(function),
                            args: args.into(),
                        }
                    }
                    AliasPost::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let child_count: usize = 1 + clause_meta
                            .iter()
                            .map(|(_, has_guard)| 1 + usize::from(*has_guard))
                            .sum::<usize>();
                        let mut parts = take_done(&mut done, child_count).into_iter();
                        let subject = parts.next().expect("when subject");
                        let clauses = clause_meta
                            .into_iter()
                            .map(|(pattern, has_guard)| WhenClause {
                                pattern,
                                guard: has_guard.then(|| parts.next().expect("clause guard")),
                                body: parts.next().expect("clause body"),
                            })
                            .collect();
                        PseudoExpr::When {
                            subject: PBox::new(subject),
                            subject_name,
                            clauses,
                        }
                    }
                    AliasPost::Plain(shell, n) => {
                        let kids = take_done(&mut done, n);
                        join_children(shell, kids)
                    }
                };
                done.push(rebuilt);
            }
        }
    }

    done.pop()
        .expect("rewrite_list_prepend_alias_uses leaves exactly one result")
}

#[cfg(test)]
mod tests;
