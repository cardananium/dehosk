use crate::decompile::ScriptVersion;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
#[cfg(test)]
use crate::pseudo::ast::{BinaryOp, UnaryOp};
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

mod finalize;
mod rebuild;
mod schedule;
mod scope;

use self::finalize::{
    finalize_binop_from_results, finalize_index_access_from_results, finalize_let_from_results,
    finalize_unop_from_results,
};
#[cfg(test)]
use self::finalize::{finalize_inline_let_binding, resolve_inline_index_access};
use self::rebuild::{
    pop_result, rebuild_apply_from_results, rebuild_builtin_call_from_results,
    rebuild_constr_from_results, rebuild_delay_from_results, rebuild_field_access_from_results,
    rebuild_force_from_results, rebuild_if_from_results, rebuild_lambda_from_results,
    rebuild_list_from_results, rebuild_pair_from_results, rebuild_recfn_from_results,
    rebuild_trace_from_results, rebuild_tuple_from_results, rebuild_when_from_results,
};
use self::schedule::{
    ResolveTask, push_resolve_enter, schedule_after_when_subject, schedule_enter_apply,
    schedule_enter_index_access, schedule_enter_let, schedule_enter_when, schedule_structural,
};
#[cfg(test)]
use self::scope::rename_var_simple;
use self::scope::{collect_call_sites_simplified, collect_let_names, has_any_var_named};
use super::context::{
    context_element_type_name, context_field_at, context_field_type_from_display_name,
    sum_type_constructor_fields,
};
use super::context_schema::{ContextType, SumTypeId};

type InlineNames = HashMap<String, String>;
type InlineTypes = HashMap<String, String>;
type InlineOverrides = HashMap<String, Vec<String>>;
type ByIdNames = HashMap<VarId, String>;

/// Per-subtree context threaded through the inline traversal. Bundles the
/// three `Rc`-shared maps so call sites carry a single value instead of
/// three correlated parameters. Cloning is cheap — each field is an `Rc`.
#[derive(Clone)]
pub(super) struct InlineCtx {
    pub(super) names: Rc<InlineNames>,
    pub(super) types: Rc<InlineTypes>,
    pub(super) overrides: Rc<InlineOverrides>,
}

impl InlineCtx {
    pub(super) fn new(names: InlineNames, types: InlineTypes, overrides: InlineOverrides) -> Self {
        Self {
            names: Rc::new(names),
            types: Rc::new(types),
            overrides: Rc::new(overrides),
        }
    }
}

type InlineClauseJob = (Option<PseudoExpr>, PseudoExpr, InlineCtx);
type InlineClauseMeta = (WhenPattern, bool);

/// Resolve an expression to its semantic context name.
///
/// `Var(name)` resolves through the `VarId` map first, then the name map.
/// `FieldAccess(_, field)` resolves to `field` when that name is itself a known
/// context name or type.
fn resolve_expr_inline_context_name(
    expr: &PseudoExpr,
    context_names: &InlineNames,
    context_types: &InlineTypes,
    context_field_names_by_id: Option<&ByIdNames>,
) -> Option<String> {
    match expr {
        PseudoExpr::Var { name, id, .. } => {
            // VarId-first for disambiguation
            let by_id = context_field_names_by_id
                .and_then(|m| id.get().and_then(|vid| m.get(&vid)))
                .cloned();
            let by_name = context_names.get(name).cloned();
            by_id.or(by_name)
        }
        // After the inline resolver has already transformed script_context.fields[0] to
        // FieldAccess(Var("script_context"), "tx_info"), resolve by field name.
        PseudoExpr::FieldAccess { selector, .. } => {
            let name = selector.as_pretty_name();
            if context_names.contains_key(name) || context_types.contains_key(name) {
                return Some(name.to_string());
            }
            None
        }
        _ => None,
    }
}

fn resolve_inline_subject_context_and_type(
    resolved_subject: &PseudoExpr,
    context_names: &InlineNames,
    context_types: &InlineTypes,
    field_names_by_id: &ByIdNames,
    version: ScriptVersion,
) -> (Option<String>, Option<String>) {
    let subject_ctx = resolve_expr_inline_context_name(
        resolved_subject,
        context_names,
        context_types,
        Some(field_names_by_id),
    );

    let subject_type = subject_ctx.as_ref().and_then(|ctx| {
        if ContextType::from_display_name(ctx)
            .and_then(|t| context_field_at(t, 0, version))
            .is_some()
        {
            Some(ctx.clone())
        } else {
            context_types.get(ctx).cloned()
        }
    });

    (subject_ctx, subject_type)
}

fn prepare_inline_when_clause_jobs(
    clauses: Vec<WhenClause>,
    subject_ctx: Option<&str>,
    subject_type: Option<&str>,
    context_names: &InlineNames,
    context_types: &InlineTypes,
    sum_field_overrides: &InlineOverrides,
    version: ScriptVersion,
) -> (Vec<InlineClauseMeta>, Vec<InlineClauseJob>) {
    let mut clause_jobs: Vec<InlineClauseJob> = Vec::with_capacity(clauses.len());
    let mut clause_meta: Vec<InlineClauseMeta> = Vec::with_capacity(clauses.len());

    for clause in clauses {
        if let WhenPattern::Constructor {
            type_hint,
            tag,
            fields,
            shape,
        } = clause.pattern
        {
            let mut aug_types = context_types.clone();
            let mut aug_names = context_names.clone();
            let mut aug_overrides = sum_field_overrides.clone();
            let mut new_fields = fields.clone();
            let mut body = clause.body;
            let mut guard = clause.guard;

            if !fields.is_empty() {
                let semantic_fields: Option<Vec<String>> = subject_type
                    .and_then(|stype| {
                        let parent = ContextType::from_display_name(stype)?;
                        let names: Vec<Option<String>> = (0..fields.len())
                            .map(|i| {
                                context_field_at(parent, i, version)
                                    .map(|f| f.display_name().to_string())
                            })
                            .collect();
                        if names.iter().all(|n| n.is_some()) {
                            Some(names.into_iter().flatten().collect())
                        } else {
                            None
                        }
                    })
                    .or_else(|| {
                        subject_ctx.and_then(|ctx| {
                            SumTypeId::from_display_name(ctx)
                                .and_then(|id| sum_type_constructor_fields(id, tag, version))
                                .and_then(|cfields| {
                                    if cfields.len() >= fields.len() {
                                        Some(
                                            (0..fields.len())
                                                .map(|i| cfields[i].0.display_name().to_string())
                                                .collect(),
                                        )
                                    } else {
                                        None
                                    }
                                })
                        })
                    });

                if let Some(semantic) = semantic_fields.filter(|semantic| {
                    semantic_field_renames_are_safe(&fields, semantic, guard.as_ref(), &body)
                }) {
                    for (old, new_name) in fields.iter().zip(semantic.iter()) {
                        if old != new_name && old != "_" {
                            body = crate::decompile::simplify::Simplifier::rename_var_binding(
                                &body,
                                old.as_str(),
                                old.id.get(),
                                new_name,
                            );
                            guard = guard.map(|g| {
                                crate::decompile::simplify::Simplifier::rename_var_binding(
                                    &g,
                                    old.as_str(),
                                    old.id.get(),
                                    new_name,
                                )
                            });
                        }
                    }
                    new_fields = fields
                        .iter()
                        .zip(semantic)
                        .map(|(field, new_name)| field.renamed(new_name))
                        .collect();

                    for f in &new_fields {
                        aug_names.insert(f.to_string(), f.to_string());
                        if let Some(var_type) = context_field_type_from_display_name(f, version) {
                            aug_types.insert(f.to_string(), var_type.display_name().to_string());
                        }
                    }
                }
            }

            if let Some(ctx_name) = subject_ctx
                && let Some(constructor_fields) = SumTypeId::from_display_name(ctx_name)
                    .and_then(|id| sum_type_constructor_fields(id, tag, version))
            {
                let field_names: Vec<String> = constructor_fields
                    .iter()
                    .map(|(n, _)| n.display_name().to_string())
                    .collect();
                aug_overrides.insert(ctx_name.to_string(), field_names);

                for (cname, maybe_type) in &constructor_fields {
                    aug_names.insert(
                        cname.display_name().to_string(),
                        cname.display_name().to_string(),
                    );
                    if let Some(type_name) = maybe_type {
                        aug_types.insert(
                            cname.display_name().to_string(),
                            type_name.display_name().to_string(),
                        );
                    }
                }
            }

            let guard_present = guard.is_some();
            clause_meta.push((
                WhenPattern::Constructor {
                    type_hint,
                    tag,
                    fields: new_fields,
                    shape,
                },
                guard_present,
            ));
            clause_jobs.push((
                guard,
                body,
                InlineCtx::new(aug_names, aug_types, aug_overrides),
            ));
        } else {
            let guard_present = clause.guard.is_some();
            clause_meta.push((clause.pattern, guard_present));
            clause_jobs.push((
                clause.guard,
                clause.body,
                InlineCtx::new(
                    context_names.clone(),
                    context_types.clone(),
                    sum_field_overrides.clone(),
                ),
            ));
        }
    }

    (clause_meta, clause_jobs)
}

fn semantic_field_renames_are_safe(
    fields: &[Binder],
    semantic: &[String],
    guard: Option<&PseudoExpr>,
    body: &PseudoExpr,
) -> bool {
    let mut target_names = HashSet::new();

    for (index, (old, new_name)) in fields.iter().zip(semantic.iter()).enumerate() {
        if old == new_name || old == "_" {
            continue;
        }
        if !target_names.insert(new_name.as_str()) {
            return false;
        }
        if fields
            .iter()
            .enumerate()
            .any(|(other_index, field)| other_index != index && field == new_name)
        {
            return false;
        }
        if has_any_var_named(body, new_name)
            || guard.is_some_and(|guard| has_any_var_named(guard, new_name))
        {
            return false;
        }
    }

    true
}

fn prepare_inline_let_value_contexts(
    name: &str,
    id: Option<VarId>,
    value: &PseudoExpr,
    body: &PseudoExpr,
    context_names: &InlineNames,
    context_types: &InlineTypes,
    field_names_by_id: &ByIdNames,
) -> (Rc<InlineNames>, Rc<InlineTypes>) {
    let mut value_context_names = Rc::new(context_names.clone());
    let mut value_context_types = Rc::new(context_types.clone());

    let PseudoExpr::Lambda { params, .. } = value else {
        return (value_context_names, value_context_types);
    };

    let mut call_sites = Vec::new();
    collect_call_sites_simplified(body, name, id, &mut call_sites);
    if call_sites.is_empty() {
        return (value_context_names, value_context_types);
    }

    let mut aug_types = context_types.clone();
    let mut aug_names = context_names.clone();
    let mut any_propagated = false;

    for (i, param) in params.iter().enumerate() {
        if param == "_" {
            continue;
        }

        let mut consistent_type: Option<String> = None;
        let mut all_match = true;

        for args in &call_sites {
            if let Some(arg) = args.get(i) {
                if let Some(sem) = resolve_expr_inline_context_name(
                    arg,
                    context_names,
                    context_types,
                    Some(field_names_by_id),
                ) {
                    let arg_type = context_types.get(&sem).cloned().unwrap_or(sem);
                    if let Some(ref existing) = consistent_type {
                        if &arg_type != existing {
                            all_match = false;
                            break;
                        }
                    } else {
                        consistent_type = Some(arg_type);
                    }
                } else {
                    all_match = false;
                    break;
                }
            } else {
                all_match = false;
                break;
            }
        }

        if all_match && let Some(ctx_type) = consistent_type {
            aug_types.insert(param.to_string(), ctx_type);
            aug_names.insert(param.to_string(), param.to_string());
            any_propagated = true;
        }
    }

    if any_propagated {
        value_context_names = Rc::new(aug_names);
        value_context_types = Rc::new(aug_types);
    }

    (value_context_names, value_context_types)
}

fn resolve_inline_apply_element_type(
    args: &[PseudoExpr],
    context_names: &InlineNames,
    context_types: &InlineTypes,
    field_names_by_id: &ByIdNames,
) -> Option<String> {
    args.iter().find_map(|arg| {
        if let PseudoExpr::BuiltinCall {
            name: bname,
            args: bargs,
        } = arg
            && *bname == crate::BuiltinId::DataToList
            && bargs.len() == 1
        {
            let semantic = resolve_expr_inline_context_name(
                &bargs[0],
                context_names,
                context_types,
                Some(field_names_by_id),
            )?;
            return context_types.get(&semantic).cloned();
        }
        None
    })
}

fn prepare_inline_apply_arg_jobs(
    args: Vec<PseudoExpr>,
    context_names: &InlineNames,
    context_types: &InlineTypes,
    sum_field_overrides: &InlineOverrides,
    field_names_by_id: &ByIdNames,
) -> Vec<InlineClauseJob> {
    let element_type =
        resolve_inline_apply_element_type(&args, context_names, context_types, field_names_by_id);

    let mut arg_jobs = Vec::with_capacity(args.len());
    for arg in args {
        let mut arg_expr = arg;
        let mut arg_names = Rc::new(context_names.clone());
        let mut arg_types = Rc::new(context_types.clone());
        let arg_overrides = Rc::new(sum_field_overrides.clone());

        if let Some(ref elem_type) = element_type
            && let PseudoExpr::Lambda { params, body } = arg_expr
        {
            if params.len() == 1 && params[0] != "_" {
                let param = params
                    .into_iter()
                    .next()
                    .expect("single-param lambda should yield one binder");
                let old_name = param.to_string();
                let semantic_name = ContextType::from_display_name(elem_type)
                    .and_then(context_element_type_name)
                    .map(|s| s.to_string());
                let desired_name = semantic_name.unwrap_or(old_name.clone());

                let body_expr = body.into_inner();
                let use_name =
                    if desired_name != old_name && has_any_var_named(&body_expr, &desired_name) {
                        old_name.clone()
                    } else {
                        desired_name
                    };

                let mut renamed_body = body_expr;
                if use_name != old_name {
                    renamed_body = crate::decompile::simplify::Simplifier::rename_var_binding(
                        &renamed_body,
                        &old_name,
                        param.id.get(),
                        &use_name,
                    );
                }

                arg_expr = PseudoExpr::Lambda {
                    params: vec![param.renamed(use_name.clone())],
                    body: PBox::new(renamed_body),
                };

                let mut aug_types = context_types.clone();
                let mut aug_names = context_names.clone();
                aug_types.insert(use_name.clone(), elem_type.clone());
                aug_names.insert(use_name.clone(), use_name.clone());

                arg_names = Rc::new(aug_names);
                arg_types = Rc::new(aug_types);
            } else {
                arg_expr = PseudoExpr::Lambda { params, body };
            }
        }

        arg_jobs.push((
            None,
            arg_expr,
            InlineCtx {
                names: arg_names,
                types: arg_types,
                overrides: arg_overrides.clone(),
            },
        ));
    }

    arg_jobs
}

// Manual task-queue traversal rather than an `impl Walker`. Four variants
// (`IndexAccess`, `Let`, `Apply`, `When`) need a context *derived* from the
// parent — Apply's args reflect the function's element type, When's clauses
// the resolved subject, Let's value the body call-site analysis,
// IndexAccess's exit task the original context — and Walker's `pre_*` /
// `post_*` hooks share one `self` across all children with no per-child
// context channel. Threading those four through Walker would mean
// overriding `fold()` for each, duplicating the dispatch the trait already
// provides; the task queue is that dispatch, with the per-child context
// bundled into each `ResolveTask::Enter`. Every other variant walks its
// children with the parent's context unchanged, via `schedule_structural`.
//
// The queue is LIFO (a `Vec` popped from the back), so schedulers push
// children in *reverse* source order to walk them left-to-right (function
// before args, condition before then before else, message before value).
/// Rewrite `.fields[N]` into named field accesses wherever the parent's context
/// type is known and index `N` resolves to a name, including inline chains
/// (`script_context.fields[0]` → `script_context.tx_info`).
pub(crate) fn resolve_inline_field_accesses(
    expr: PseudoExpr,
    version: ScriptVersion,
    context_names: &InlineNames,
    context_types: &InlineTypes,
    sum_field_overrides: &InlineOverrides,
    context_field_names_by_id: &ByIdNames,
    context_var_types_by_id: &ByIdNames,
) -> PseudoExpr {
    // VarId-based maps (flat, not augmented per-scope)
    let field_names_by_id: Rc<ByIdNames> = Rc::new(context_field_names_by_id.clone());
    let _var_types_by_id: Rc<ByIdNames> = Rc::new(context_var_types_by_id.clone());

    let base_ctx = InlineCtx::new(
        context_names.clone(),
        context_types.clone(),
        sum_field_overrides.clone(),
    );
    let mut used_let_names = collect_let_names(&expr);

    let mut tasks = Vec::new();
    push_resolve_enter(&mut tasks, expr, base_ctx);
    let mut results: Vec<PseudoExpr> = Vec::new();

    while let Some(task) = tasks.pop() {
        match task {
            ResolveTask::Enter { expr, ctx } => match expr {
                // Four variants need per-child context derivation.
                PseudoExpr::IndexAccess { collection, index } => {
                    schedule_enter_index_access(&mut tasks, collection.into_inner(), index, ctx);
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    schedule_enter_let(
                        &mut tasks,
                        name,
                        id.unwrap_or_else(VarId::fresh_compat_placeholder),
                        value.into_inner(),
                        body.into_inner(),
                        ctx,
                        field_names_by_id.as_ref(),
                    );
                }
                PseudoExpr::Apply { function, args } => {
                    schedule_enter_apply(
                        &mut tasks,
                        function.into_inner(),
                        args.into_vec(),
                        ctx,
                        field_names_by_id.as_ref(),
                    );
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    schedule_enter_when(
                        &mut tasks,
                        subject.into_inner(),
                        subject_name,
                        clauses,
                        ctx,
                    );
                }
                // Structural variants walk children with the parent's
                // context unchanged; leaf nodes pass through.
                other => {
                    if let Some(leaf) = schedule_structural(&mut tasks, other, ctx) {
                        results.push(leaf);
                    }
                }
            },

            ResolveTask::ExitIndexAccess { index, ctx } => {
                let finalized = finalize_index_access_from_results(
                    &mut results,
                    index,
                    ctx.names.as_ref(),
                    ctx.types.as_ref(),
                    ctx.overrides.as_ref(),
                    field_names_by_id.as_ref(),
                    version,
                );
                results.push(finalized);
            }

            ResolveTask::ExitLet { name, id } => {
                let finalized =
                    finalize_let_from_results(&mut results, name, id, &mut used_let_names);
                results.push(finalized);
            }

            ResolveTask::ExitLambda { params } => {
                let rebuilt = rebuild_lambda_from_results(&mut results, params);
                results.push(rebuilt);
            }

            ResolveTask::ExitApply { args_len } => {
                let rebuilt = rebuild_apply_from_results(&mut results, args_len);
                results.push(rebuilt);
            }

            ResolveTask::ExitIf => {
                let rebuilt = rebuild_if_from_results(&mut results);
                results.push(rebuilt);
            }

            ResolveTask::AfterWhenSubject {
                subject_name,
                clauses,
                ctx,
            } => {
                let resolved_subject = pop_result(&mut results);
                schedule_after_when_subject(
                    &mut tasks,
                    resolved_subject,
                    subject_name,
                    clauses,
                    ctx,
                    field_names_by_id.as_ref(),
                    version,
                );
            }

            ResolveTask::ExitWhen {
                subject,
                subject_name,
                clauses,
            } => {
                let rebuilt =
                    rebuild_when_from_results(&mut results, subject, subject_name, clauses);
                results.push(rebuilt);
            }

            ResolveTask::ExitBinOp { op } => {
                let finalized = finalize_binop_from_results(&mut results, op, version);
                results.push(finalized);
            }

            ResolveTask::ExitUnOp { op } => {
                let finalized = finalize_unop_from_results(&mut results, op);
                results.push(finalized);
            }

            ResolveTask::ExitFieldAccess { selector, .. } => {
                let rebuilt = rebuild_field_access_from_results(&mut results, selector);
                results.push(rebuilt);
            }

            ResolveTask::ExitForce => {
                let rebuilt = rebuild_force_from_results(&mut results);
                results.push(rebuilt);
            }

            ResolveTask::ExitDelay => {
                let rebuilt = rebuild_delay_from_results(&mut results);
                results.push(rebuilt);
            }

            ResolveTask::ExitRecFn { name, params } => {
                let rebuilt = rebuild_recfn_from_results(&mut results, name, params);
                results.push(rebuilt);
            }

            ResolveTask::ExitBuiltinCall { name, args_len } => {
                let rebuilt = rebuild_builtin_call_from_results(&mut results, name, args_len);
                results.push(rebuilt);
            }

            ResolveTask::ExitList {
                elements_len,
                has_tail,
            } => {
                let rebuilt = rebuild_list_from_results(&mut results, elements_len, has_tail);
                results.push(rebuilt);
            }

            ResolveTask::ExitConstr {
                type_hint,
                tag,
                fields_len,
                shape,
            } => {
                let rebuilt =
                    rebuild_constr_from_results(&mut results, type_hint, tag, fields_len, shape);
                results.push(rebuilt);
            }

            ResolveTask::ExitTrace => {
                let rebuilt = rebuild_trace_from_results(&mut results);
                results.push(rebuilt);
            }

            ResolveTask::ExitTuple { len } => {
                let rebuilt = rebuild_tuple_from_results(&mut results, len);
                results.push(rebuilt);
            }

            ResolveTask::ExitPair => {
                let rebuilt = rebuild_pair_from_results(&mut results);
                results.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(results.len(), 1);
    pop_result(&mut results)
}

#[cfg(test)]
mod tests;
