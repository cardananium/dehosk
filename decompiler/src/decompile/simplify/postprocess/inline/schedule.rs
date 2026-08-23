use crate::builtins::BuiltinId;
use crate::decompile::{ScriptVersion, TypeHintId};
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

use super::{
    ByIdNames, InlineCtx, prepare_inline_apply_arg_jobs, prepare_inline_let_value_contexts,
    prepare_inline_when_clause_jobs, resolve_inline_subject_context_and_type,
};

pub(super) enum ResolveTask {
    Enter {
        expr: PseudoExpr,
        ctx: InlineCtx,
    },
    ExitIndexAccess {
        index: usize,
        ctx: InlineCtx,
    },
    ExitLet {
        name: String,
        id: VarId,
    },
    ExitLambda {
        params: Vec<Binder>,
    },
    ExitApply {
        args_len: usize,
    },
    ExitIf,
    AfterWhenSubject {
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
        ctx: InlineCtx,
    },
    ExitWhen {
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<(WhenPattern, bool)>,
    },
    ExitBinOp {
        op: BinaryOp,
    },
    ExitUnOp {
        op: UnaryOp,
    },
    ExitFieldAccess {
        selector: FieldSelector,
    },
    ExitForce,
    ExitDelay,
    ExitRecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    ExitBuiltinCall {
        name: BuiltinId,
        args_len: usize,
    },
    ExitList {
        elements_len: usize,
        has_tail: bool,
    },
    ExitConstr {
        type_hint: Option<TypeHintId>,
        tag: usize,
        fields_len: usize,
        shape: ConstructorShape,
    },
    ExitTrace,
    ExitTuple {
        len: usize,
    },
    ExitPair,
}

pub(super) fn push_resolve_enter(tasks: &mut Vec<ResolveTask>, expr: PseudoExpr, ctx: InlineCtx) {
    tasks.push(ResolveTask::Enter { expr, ctx });
}

// ---------- Bespoke schedulers ----------
//
// Four variants derive a child context that diverges from the parent's:
//
//   - `IndexAccess` — the collection is walked first and the result is
//     finalized later with the original context, so `ExitIndexAccess` must
//     carry it.
//   - `Let` — the value gets a context augmented from body call-site analysis
//     (`prepare_inline_let_value_contexts`); the body keeps the parent's.
//   - `Apply` — each arg gets a context shaped by the function's element type
//     (`prepare_inline_apply_arg_jobs`).
//   - `When` — the subject is walked first and the resolved subject feeds the
//     per-clause contexts (`prepare_inline_when_clause_jobs`).
//
// Every other variant is handled by `schedule_structural`.

pub(super) fn schedule_enter_index_access(
    tasks: &mut Vec<ResolveTask>,
    collection: PseudoExpr,
    index: usize,
    ctx: InlineCtx,
) {
    tasks.push(ResolveTask::ExitIndexAccess {
        index,
        ctx: ctx.clone(),
    });
    push_resolve_enter(tasks, collection, ctx);
}

#[allow(clippy::too_many_arguments)]
pub(super) fn schedule_enter_let(
    tasks: &mut Vec<ResolveTask>,
    name: String,
    id: VarId,
    value: PseudoExpr,
    body: PseudoExpr,
    ctx: InlineCtx,
    field_names_by_id: &ByIdNames,
) {
    let (value_names, value_types) = prepare_inline_let_value_contexts(
        &name,
        id.get(),
        &value,
        &body,
        ctx.names.as_ref(),
        ctx.types.as_ref(),
        field_names_by_id,
    );
    let value_ctx = InlineCtx {
        names: value_names,
        types: value_types,
        overrides: ctx.overrides.clone(),
    };

    tasks.push(ResolveTask::ExitLet { name, id });
    push_resolve_enter(tasks, body, ctx);
    push_resolve_enter(tasks, value, value_ctx);
}

pub(super) fn schedule_enter_apply(
    tasks: &mut Vec<ResolveTask>,
    function: PseudoExpr,
    args: Vec<PseudoExpr>,
    ctx: InlineCtx,
    field_names_by_id: &ByIdNames,
) {
    let arg_jobs = prepare_inline_apply_arg_jobs(
        args,
        ctx.names.as_ref(),
        ctx.types.as_ref(),
        ctx.overrides.as_ref(),
        field_names_by_id,
    );

    tasks.push(ResolveTask::ExitApply {
        args_len: arg_jobs.len(),
    });
    for (_guard, arg_expr, arg_ctx) in arg_jobs.into_iter().rev() {
        push_resolve_enter(tasks, arg_expr, arg_ctx);
    }
    push_resolve_enter(tasks, function, ctx);
}

pub(super) fn schedule_enter_when(
    tasks: &mut Vec<ResolveTask>,
    subject: PseudoExpr,
    subject_name: Option<Binder>,
    clauses: Vec<WhenClause>,
    ctx: InlineCtx,
) {
    tasks.push(ResolveTask::AfterWhenSubject {
        subject_name,
        clauses,
        ctx: ctx.clone(),
    });
    push_resolve_enter(tasks, subject, ctx);
}

#[allow(clippy::too_many_arguments)]
pub(super) fn schedule_after_when_subject(
    tasks: &mut Vec<ResolveTask>,
    resolved_subject: PseudoExpr,
    subject_name: Option<Binder>,
    clauses: Vec<WhenClause>,
    ctx: InlineCtx,
    field_names_by_id: &ByIdNames,
    version: ScriptVersion,
) {
    let (subject_ctx, subject_type) = resolve_inline_subject_context_and_type(
        &resolved_subject,
        ctx.names.as_ref(),
        ctx.types.as_ref(),
        field_names_by_id,
        version,
    );
    let (clause_meta, clause_jobs) = prepare_inline_when_clause_jobs(
        clauses,
        subject_ctx.as_deref(),
        subject_type.as_deref(),
        ctx.names.as_ref(),
        ctx.types.as_ref(),
        ctx.overrides.as_ref(),
        version,
    );

    tasks.push(ResolveTask::ExitWhen {
        subject: resolved_subject,
        subject_name,
        clauses: clause_meta,
    });

    for (guard, body, clause_ctx) in clause_jobs.into_iter().rev() {
        push_resolve_enter(tasks, body, clause_ctx.clone());
        if let Some(guard_expr) = guard {
            push_resolve_enter(tasks, guard_expr, clause_ctx);
        }
    }
}

// ---------- Structural scheduler ----------
//
// Handles every variant whose children walk with the parent's context
// unchanged; leaf nodes flow back as `Some(leaf)` for the caller to push
// onto the result stack.
//
// The match is exhaustive so a new `PseudoExpr` variant surfaces as a
// compile error rather than silently flowing through `Some(leaf)`, which
// would skip its children's traversal. Bespoke variants (`IndexAccess` /
// `Let` / `Apply` / `When`) are intercepted by the caller and trip
// `unreachable!` if they reach here.
pub(super) fn schedule_structural(
    tasks: &mut Vec<ResolveTask>,
    expr: PseudoExpr,
    ctx: InlineCtx,
) -> Option<PseudoExpr> {
    match expr {
        PseudoExpr::Lambda { params, body } => {
            tasks.push(ResolveTask::ExitLambda { params });
            push_resolve_enter(tasks, body.into_inner(), ctx);
            None
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            tasks.push(ResolveTask::ExitIf);
            push_resolve_enter(tasks, else_branch.into_inner(), ctx.clone());
            push_resolve_enter(tasks, then_branch.into_inner(), ctx.clone());
            push_resolve_enter(tasks, condition.into_inner(), ctx);
            None
        }
        PseudoExpr::BinOp { op, left, right } => {
            tasks.push(ResolveTask::ExitBinOp { op });
            push_resolve_enter(tasks, right.into_inner(), ctx.clone());
            push_resolve_enter(tasks, left.into_inner(), ctx);
            None
        }
        PseudoExpr::UnOp { op, operand } => {
            tasks.push(ResolveTask::ExitUnOp { op });
            push_resolve_enter(tasks, operand.into_inner(), ctx);
            None
        }
        PseudoExpr::FieldAccess {
            record, selector, ..
        } => {
            tasks.push(ResolveTask::ExitFieldAccess { selector });
            push_resolve_enter(tasks, record.into_inner(), ctx);
            None
        }
        PseudoExpr::Force(inner) => {
            tasks.push(ResolveTask::ExitForce);
            push_resolve_enter(tasks, inner.into_inner(), ctx);
            None
        }
        PseudoExpr::Delay(inner) => {
            tasks.push(ResolveTask::ExitDelay);
            push_resolve_enter(tasks, inner.into_inner(), ctx);
            None
        }
        PseudoExpr::RecFn { name, params, body } => {
            tasks.push(ResolveTask::ExitRecFn { name, params });
            push_resolve_enter(tasks, body.into_inner(), ctx);
            None
        }
        PseudoExpr::BuiltinCall { name, args } => {
            tasks.push(ResolveTask::ExitBuiltinCall {
                name,
                args_len: args.len(),
            });
            for arg in args.into_iter().rev() {
                push_resolve_enter(tasks, arg, ctx.clone());
            }
            None
        }
        PseudoExpr::List { elements, tail } => {
            tasks.push(ResolveTask::ExitList {
                elements_len: elements.len(),
                has_tail: tail.is_some(),
            });
            if let Some(tail_expr) = tail {
                push_resolve_enter(tasks, tail_expr.into_inner(), ctx.clone());
            }
            for element in elements.into_iter().rev() {
                push_resolve_enter(tasks, element, ctx.clone());
            }
            None
        }
        PseudoExpr::Constr {
            type_hint,
            tag,
            fields,
            shape,
        } => {
            tasks.push(ResolveTask::ExitConstr {
                type_hint,
                tag,
                fields_len: fields.len(),
                shape,
            });
            for field in fields.into_iter().rev() {
                push_resolve_enter(tasks, field, ctx.clone());
            }
            None
        }
        PseudoExpr::Trace { message, value } => {
            tasks.push(ResolveTask::ExitTrace);
            push_resolve_enter(tasks, value.into_inner(), ctx.clone());
            push_resolve_enter(tasks, message.into_inner(), ctx);
            None
        }
        PseudoExpr::Tuple(items) => {
            tasks.push(ResolveTask::ExitTuple { len: items.len() });
            for item in items.into_iter().rev() {
                push_resolve_enter(tasks, item, ctx.clone());
            }
            None
        }
        PseudoExpr::Pair(a, b) => {
            tasks.push(ResolveTask::ExitPair);
            push_resolve_enter(tasks, b.into_inner(), ctx.clone());
            push_resolve_enter(tasks, a.into_inner(), ctx);
            None
        }
        // Leaf nodes — caller pushes to results.
        leaf @ (PseudoExpr::Int(_)
        | PseudoExpr::ByteArray(_)
        | PseudoExpr::String(_)
        | PseudoExpr::Bool(_)
        | PseudoExpr::Unit
        | PseudoExpr::Var { .. }
        | PseudoExpr::Error { .. }
        | PseudoExpr::Raw { .. }
        | PseudoExpr::Data(_)
        | PseudoExpr::HelperSymbol(_)) => Some(leaf),
        // Bespoke variants — the caller intercepts these before reaching
        // here. Reaching them is a contract violation.
        PseudoExpr::IndexAccess { .. }
        | PseudoExpr::Let { .. }
        | PseudoExpr::Apply { .. }
        | PseudoExpr::When { .. } => unreachable!(
            "bespoke variants (IndexAccess/Let/Apply/When) must be handled before \
             reaching schedule_structural"
        ),
    }
}
