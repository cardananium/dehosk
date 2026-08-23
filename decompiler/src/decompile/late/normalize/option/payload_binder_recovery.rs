use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::builtins::BuiltinId;
use crate::decompile::blueprint_registry::{OPTION_TYPE_HINT_NAME, TypeHintId};
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;

use super::payload_access::replace_subject_payload_access;

fn is_generated_option_payload_name(name: &str) -> bool {
    name == "fields"
        || name == "item"
        || name == "payload"
        || name.starts_with("fields_")
        || name.starts_with("item_")
        || (name.contains('_') && name.chars().any(|ch| ch.is_ascii_digit()))
}

// The broad `(contains('_') && any digit)` catch-all is load-bearing:
// single-letter `<v>_<N>` names (`y2_2`, `y_13`, `x_77`) are
// legitimate Simplifier-generated payload binders that the recovery
// passes must find.

/// VarKind-based orphan-payload predicate, gated under
/// `DecompileOptions::use_varkind_recovery`. Delegates to the
/// `_with_name_resolution` form of
/// [`crate::decompile::varkind_recovery::is_orphan_payload_ref_typed_or_legacy`]
/// with this pass's legacy predicate (`is_generated_option_payload_name`).
///
/// An authoritative VarKind (`ConstrPayload`, `FieldIndexAlias`,
/// `Synthetic`) is an immediate yes; otherwise the legacy name pattern
/// decides, so the typed path is a SUPERSET of the legacy path on the
/// orphan-candidate set.
fn is_orphan_payload_ref(
    name: &str,
    id: Option<VarId>,
    kind_annotations: &HashMap<VarId, VarKind>,
    name_to_binder_id: &HashMap<String, VarId>,
    use_varkind_recovery: bool,
) -> bool {
    let id = id.unwrap_or_else(VarId::fresh_compat_placeholder);
    crate::decompile::varkind_recovery::is_orphan_payload_ref_typed_or_legacy_with_name_resolution(
        name,
        id,
        kind_annotations,
        name_to_binder_id,
        use_varkind_recovery,
        is_generated_option_payload_name,
        "option",
    )
}

fn choose_generated_option_payload_binder(free: &[Binder]) -> Option<Binder> {
    for candidate in ["fields", "item", "payload"] {
        let mut matching = free.iter().filter(|binder| binder.name == candidate);
        match (matching.next(), matching.next()) {
            (Some(binder), None) => return Some(binder.clone()),
            (Some(_), Some(_)) => return None,
            (None, _) => {}
        }
    }

    if let [binder] = free {
        return Some(binder.clone());
    }

    let mut plain = free.iter().filter(|binder| {
        !binder.name.chars().any(|ch| ch.is_ascii_digit()) && !binder.name.contains('_')
    });
    match (plain.next(), plain.next()) {
        (Some(binder), None) => Some(binder.clone()),
        _ => None,
    }
}

fn recovered_generated_option_payload_binder(payload_ref: &Binder) -> Binder {
    let id = payload_ref.id.get().unwrap_or_else(VarId::fresh_binding);
    Binder::new(payload_ref.name.clone(), id)
}

/// True if `binder` is ever used in callee position inside `expr`, i.e.
/// `Apply { function: Var(binder), .. }`. An Option payload is a `Data`
/// value, never a callee, so an applied candidate is the wrong pick:
/// rejecting it stops the recovery from binding a free recursive-helper
/// callee (e.g. `v_236`, matching the `<name>_<digit>` catch-all in
/// `is_generated_option_payload_name`) as the `Some` payload, which
/// renders as `Some(value_2) -> value_2(builtin.un_map_data(value_2))`.
fn binder_used_as_callee(expr: &PseudoExpr, binder: &Binder) -> bool {
    fn var_is(target: &Binder, name: &str, id: Option<VarId>) -> bool {
        match (id, target.id.get()) {
            (Some(a), Some(b)) => a == b,
            _ => name == target.name,
        }
    }
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Apply { function, args } => {
                // Unwrap `force`/`delay` thunk wrappers around the callee
                // head — `force(var)(args)` still applies `var` as a function.
                let mut head = function.as_ref();
                while let PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) = head {
                    head = inner;
                }
                if let PseudoExpr::Var { name, id } = head
                    && var_is(binder, name, *id)
                {
                    return true;
                }
                pending.extend(args.iter().rev());
                pending.push(function);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
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
                for c in clauses.iter().rev() {
                    pending.push(&c.body);
                    if let Some(g) = &c.guard {
                        pending.push(g);
                    }
                }
                pending.push(subject);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. }
            | PseudoExpr::Delay(operand)
            | PseudoExpr::Force(operand) => pending.push(operand),
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail.as_deref() {
                    pending.push(t);
                }
                pending.extend(elements.iter().rev());
            }
            PseudoExpr::Tuple(elements) => pending.extend(elements.iter().rev()),
            PseudoExpr::Pair(a, b) => {
                pending.push(b);
                pending.push(a);
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter().rev()),
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter().rev()),
            _ => {}
        }
    }
    false
}

/// One pending step of [`collect_free_generated_payload_binders`].
///
/// `Bind`/`Unbind` are steps in their own right because a scope opens
/// BETWEEN two child descents — a `let`'s value is walked outside the
/// binding, its body inside it — so neither can be folded into a child's
/// own step without moving the binding across it.
enum CollectStep<'a> {
    Visit(&'a PseudoExpr),
    /// Bring these binder ids into scope.
    Bind(Vec<VarId>),
    /// Restore `bound` to this length.
    Unbind(usize),
}

fn collect_free_generated_payload_binders(
    expr: &PseudoExpr,
    bound: &mut Vec<VarId>,
    free: &mut Vec<Binder>,
    kind_annotations: &HashMap<VarId, VarKind>,
    name_to_binder_id: &HashMap<String, VarId>,
    use_varkind_recovery: bool,
) {
    let mut steps = vec![CollectStep::Visit(expr)];
    while let Some(step) = steps.pop() {
        let expr = match step {
            CollectStep::Bind(ids) => {
                bound.extend(ids);
                continue;
            }
            CollectStep::Unbind(base) => {
                bound.truncate(base);
                continue;
            }
            CollectStep::Visit(expr) => expr,
        };
        match expr {
            PseudoExpr::Var { name, id } => {
                let id_opt = *id;
                let id_concrete = id_opt.unwrap_or_else(VarId::fresh_compat_placeholder);
                if !bound.iter().rev().any(|bound_id| *bound_id == id_concrete)
                    && is_orphan_payload_ref(
                        name,
                        id_opt,
                        kind_annotations,
                        name_to_binder_id,
                        use_varkind_recovery,
                    )
                    && !free.iter().any(|existing| Some(existing.id) == id_opt)
                {
                    free.push(Binder::new(name.clone(), id_concrete));
                }
            }
            PseudoExpr::Lambda { params, body } => {
                let base = bound.len();
                steps.push(CollectStep::Unbind(base));
                steps.push(CollectStep::Visit(body.as_ref()));
                steps.push(CollectStep::Bind(
                    params.iter().map(|param| param.id).collect(),
                ));
            }
            PseudoExpr::RecFn { name, params, body } => {
                let base = bound.len();
                let mut ids = vec![name.id];
                ids.extend(params.iter().map(|param| param.id));
                steps.push(CollectStep::Unbind(base));
                steps.push(CollectStep::Visit(body.as_ref()));
                steps.push(CollectStep::Bind(ids));
            }
            PseudoExpr::Let {
                id, value, body, ..
            } => {
                // The binding comes into scope AFTER the value is walked.
                let base = bound.len();
                steps.push(CollectStep::Unbind(base));
                steps.push(CollectStep::Visit(body.as_ref()));
                steps.push(CollectStep::Bind(id.iter().copied().collect()));
                steps.push(CollectStep::Visit(value.as_ref()));
            }
            PseudoExpr::Apply { function, args } => {
                for arg in args.iter().rev() {
                    steps.push(CollectStep::Visit(arg));
                }
                steps.push(CollectStep::Visit(function.as_ref()));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                steps.push(CollectStep::Visit(else_branch.as_ref()));
                steps.push(CollectStep::Visit(then_branch.as_ref()));
                steps.push(CollectStep::Visit(condition.as_ref()));
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                // Each clause opens its own scope, walks guard then body
                // inside it, and closes it again before the next clause.
                let base = bound.len();
                for clause in clauses.iter().rev() {
                    let mut ids = Vec::new();
                    if let Some(subject_name) = subject_name {
                        ids.push(subject_name.id);
                    }
                    ids.extend(clause.pattern.bound_ids());
                    steps.push(CollectStep::Unbind(base));
                    steps.push(CollectStep::Visit(&clause.body));
                    if let Some(guard) = &clause.guard {
                        steps.push(CollectStep::Visit(guard));
                    }
                    steps.push(CollectStep::Bind(ids));
                }
                steps.push(CollectStep::Visit(subject.as_ref()));
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(tail) = tail {
                    steps.push(CollectStep::Visit(tail.as_ref()));
                }
                for element in elements.iter().rev() {
                    steps.push(CollectStep::Visit(element));
                }
            }
            PseudoExpr::Tuple(elements) => {
                for element in elements.iter().rev() {
                    steps.push(CollectStep::Visit(element));
                }
            }
            PseudoExpr::Pair(first, second) => {
                steps.push(CollectStep::Visit(second.as_ref()));
                steps.push(CollectStep::Visit(first.as_ref()));
            }
            PseudoExpr::Constr { fields, .. } => {
                for field in fields.iter().rev() {
                    steps.push(CollectStep::Visit(field));
                }
            }
            PseudoExpr::FieldAccess { record, .. } => {
                steps.push(CollectStep::Visit(record.as_ref()));
            }
            PseudoExpr::IndexAccess { collection, .. } => {
                steps.push(CollectStep::Visit(collection.as_ref()));
            }
            PseudoExpr::BinOp { left, right, .. } => {
                steps.push(CollectStep::Visit(right.as_ref()));
                steps.push(CollectStep::Visit(left.as_ref()));
            }
            PseudoExpr::UnOp { operand, .. }
            | PseudoExpr::Delay(operand)
            | PseudoExpr::Force(operand) => {
                steps.push(CollectStep::Visit(operand.as_ref()));
            }
            PseudoExpr::Trace { message, value } => {
                steps.push(CollectStep::Visit(value.as_ref()));
                steps.push(CollectStep::Visit(message.as_ref()));
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args.iter().rev() {
                    steps.push(CollectStep::Visit(arg));
                }
            }
            PseudoExpr::Int(_)
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
}

/// Reassembly tag for a node kind that opens no scope of its own: same
/// children in the same order, same reconstruction, in both owned rewrites
/// below — so it is factored out once instead of repeated per machine.
enum PlainPost {
    Apply {
        argc: usize,
    },
    If,
    List {
        count: usize,
        has_tail: bool,
    },
    Tuple {
        count: usize,
    },
    Pair,
    Constr {
        type_hint: Option<TypeHintId>,
        tag: usize,
        count: usize,
        shape: ConstructorShape,
    },
    FieldAccess {
        selector: FieldSelector,
    },
    IndexAccess {
        index: usize,
    },
    BinOp {
        op: BinaryOp,
    },
    UnOp {
        op: UnaryOp,
    },
    Delay,
    Force,
    Trace,
    BuiltinCall {
        name: BuiltinId,
        argc: usize,
    },
}

/// Splits a scope-free node into its reassembly tag and its children in the
/// order the recursive originals rewrote them, for a machine to push in
/// reverse and rebuild via [`rebuild_plain`]. `Err` for everything the
/// callers already special-cased (`Var`/`Lambda`/`RecFn`/`Let`/`When`) plus
/// the leaves, which go onto `done` unchanged.
fn plain_children(expr: PseudoExpr) -> Result<(PlainPost, Vec<PseudoExpr>), PseudoExpr> {
    Ok(match expr {
        PseudoExpr::Apply { function, args } => {
            let argc = args.len();
            let mut children = vec![function.into_inner()];
            children.extend(args);
            (PlainPost::Apply { argc }, children)
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => (
            PlainPost::If,
            vec![
                condition.into_inner(),
                then_branch.into_inner(),
                else_branch.into_inner(),
            ],
        ),
        PseudoExpr::List { elements, tail } => {
            let count = elements.len();
            let has_tail = tail.is_some();
            let mut children = elements;
            if let Some(tail) = tail {
                children.push(tail.into_inner());
            }
            (PlainPost::List { count, has_tail }, children.into_vec())
        }
        PseudoExpr::Tuple(elements) => {
            let count = elements.len();
            (PlainPost::Tuple { count }, elements.into_vec())
        }
        PseudoExpr::Pair(first, second) => (
            PlainPost::Pair,
            vec![first.into_inner(), second.into_inner()],
        ),
        PseudoExpr::Constr {
            type_hint,
            tag,
            fields,
            shape,
        } => {
            let count = fields.len();
            (
                PlainPost::Constr {
                    type_hint,
                    tag,
                    count,
                    shape,
                },
                fields.into_vec(),
            )
        }
        PseudoExpr::FieldAccess {
            record, selector, ..
        } => (
            PlainPost::FieldAccess { selector },
            vec![record.into_inner()],
        ),
        PseudoExpr::IndexAccess { collection, index } => (
            PlainPost::IndexAccess { index },
            vec![collection.into_inner()],
        ),
        PseudoExpr::BinOp { op, left, right } => (
            PlainPost::BinOp { op },
            vec![left.into_inner(), right.into_inner()],
        ),
        PseudoExpr::UnOp { op, operand } => (PlainPost::UnOp { op }, vec![operand.into_inner()]),
        PseudoExpr::Delay(inner) => (PlainPost::Delay, vec![inner.into_inner()]),
        PseudoExpr::Force(inner) => (PlainPost::Force, vec![inner.into_inner()]),
        PseudoExpr::Trace { message, value } => (
            PlainPost::Trace,
            vec![message.into_inner(), value.into_inner()],
        ),
        PseudoExpr::BuiltinCall { name, args } => {
            let argc = args.len();
            (PlainPost::BuiltinCall { name, argc }, args.into_vec())
        }
        other => return Err(other),
    })
}

/// Takes the last `n` rewritten children off `done`, in source order.
fn take(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
    let at = done.len() - n;
    done.split_off(at)
}

fn rebuild_plain(kind: PlainPost, done: &mut Vec<PseudoExpr>) -> PseudoExpr {
    match kind {
        PlainPost::Apply { argc } => {
            let args = take(done, argc);
            let function = done.pop().expect("apply function");
            PseudoExpr::Apply {
                function: PBox::new(function),
                args: args.into(),
            }
        }
        PlainPost::If => {
            let mut parts = take(done, 3).into_iter();
            let condition = parts.next().expect("if condition");
            let then_branch = parts.next().expect("if then");
            let else_branch = parts.next().expect("if else");
            PseudoExpr::If {
                condition: PBox::new(condition),
                then_branch: PBox::new(then_branch),
                else_branch: PBox::new(else_branch),
            }
        }
        PlainPost::List { count, has_tail } => {
            let tail = if has_tail {
                Some(PBox::new(done.pop().expect("list tail")))
            } else {
                None
            };
            let elements = take(done, count);
            PseudoExpr::List {
                elements: elements.into(),
                tail,
            }
        }
        PlainPost::Tuple { count } => PseudoExpr::Tuple((take(done, count)).into()),
        PlainPost::Pair => {
            let second = done.pop().expect("pair second");
            let first = done.pop().expect("pair first");
            PseudoExpr::Pair(PBox::new(first), PBox::new(second))
        }
        PlainPost::Constr {
            type_hint,
            tag,
            count,
            shape,
        } => {
            let fields = take(done, count);
            PseudoExpr::Constr {
                type_hint,
                tag,
                fields: fields.into(),
                shape,
            }
        }
        PlainPost::FieldAccess { selector } => {
            let record = done.pop().expect("field access record");
            PseudoExpr::field_access_typed(record, selector)
        }
        PlainPost::IndexAccess { index } => {
            let collection = done.pop().expect("index access collection");
            PseudoExpr::IndexAccess {
                collection: PBox::new(collection),
                index,
            }
        }
        PlainPost::BinOp { op } => {
            let right = done.pop().expect("binop right");
            let left = done.pop().expect("binop left");
            PseudoExpr::BinOp {
                op,
                left: PBox::new(left),
                right: PBox::new(right),
            }
        }
        PlainPost::UnOp { op } => {
            let operand = done.pop().expect("unop operand");
            PseudoExpr::UnOp {
                op,
                operand: PBox::new(operand),
            }
        }
        PlainPost::Delay => PseudoExpr::Delay(PBox::new(done.pop().expect("delay inner"))),
        PlainPost::Force => PseudoExpr::Force(PBox::new(done.pop().expect("force inner"))),
        PlainPost::Trace => {
            let value = done.pop().expect("trace value");
            let message = done.pop().expect("trace message");
            PseudoExpr::Trace {
                message: PBox::new(message),
                value: PBox::new(value),
            }
        }
        PlainPost::BuiltinCall { name, argc } => {
            let args = take(done, argc);
            PseudoExpr::BuiltinCall {
                name,
                args: args.into(),
            }
        }
    }
}

/// One pending step of an owned, scope-tracking rewrite. `S` is the scope
/// stack's element type: `VarId` for
/// [`replace_free_generated_payload_binder`], `String` for the `rewrite`
/// inside [`recover_missing_option_payload_binders`].
enum RewriteStep<S> {
    Enter(PseudoExpr),
    /// Bring these binders into scope. Its own step because a scope opens
    /// BETWEEN two child descents — a `let`'s value is rewritten outside
    /// the binding, its body inside it.
    Bind(Vec<S>),
    /// Restore the scope stack to this length.
    Unbind(usize),
    Post(RewritePost),
}

enum RewritePost {
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    Let {
        name: String,
        id: Option<VarId>,
    },
    When {
        subject_name: Option<Binder>,
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// Number of results a `When`'s children leave on `done`: the subject plus
/// each clause's optional guard and its body.
fn when_child_count(clause_meta: &[(WhenPattern, bool)]) -> usize {
    1 + clause_meta
        .iter()
        .map(|(_, has_guard)| usize::from(*has_guard) + 1)
        .sum::<usize>()
}

fn replace_free_generated_payload_binder(
    expr: PseudoExpr,
    target: &Binder,
    binder: &Binder,
    bound: &mut Vec<VarId>,
) -> PseudoExpr {
    let mut steps = vec![RewriteStep::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RewriteStep::Bind(ids) => bound.extend(ids),
            RewriteStep::Unbind(base) => bound.truncate(base),
            RewriteStep::Enter(expr) => match expr {
                PseudoExpr::Var { name, id } => {
                    let id_concrete = id.unwrap_or_else(VarId::fresh_compat_placeholder);
                    // compat refs carry `id: None`, so match the recovery target
                    // by VarId when concrete, by name when unresolved.
                    let matches_target =
                        id == Some(target.id) || (id.is_none() && name == target.name);
                    done.push(
                        if matches_target
                            && !bound.iter().rev().any(|bound_id| *bound_id == id_concrete)
                        {
                            PseudoExpr::var_with_id(binder.name.clone(), binder.id)
                        } else {
                            PseudoExpr::Var { name, id }
                        },
                    );
                }
                PseudoExpr::Lambda { params, body } => {
                    let base = bound.len();
                    let ids: Vec<VarId> = params.iter().map(|param| param.id).collect();
                    steps.push(RewriteStep::Post(RewritePost::Lambda { params }));
                    steps.push(RewriteStep::Unbind(base));
                    steps.push(RewriteStep::Enter(body.into_inner()));
                    steps.push(RewriteStep::Bind(ids));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    let base = bound.len();
                    let mut ids = vec![name.id];
                    ids.extend(params.iter().map(|param| param.id));
                    steps.push(RewriteStep::Post(RewritePost::RecFn { name, params }));
                    steps.push(RewriteStep::Unbind(base));
                    steps.push(RewriteStep::Enter(body.into_inner()));
                    steps.push(RewriteStep::Bind(ids));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    let base = bound.len();
                    let ids: Vec<VarId> = id.into_iter().collect();
                    steps.push(RewriteStep::Post(RewritePost::Let { name, id }));
                    steps.push(RewriteStep::Unbind(base));
                    steps.push(RewriteStep::Enter(body.into_inner()));
                    steps.push(RewriteStep::Bind(ids));
                    steps.push(RewriteStep::Enter(value.into_inner()));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let base = bound.len();
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    // Built in pop order, then pushed in reverse.
                    let mut clause_steps = Vec::new();
                    for clause in clauses {
                        let WhenClause {
                            pattern,
                            guard,
                            body,
                        } = clause;
                        let mut ids = Vec::new();
                        if let Some(subject_name) = &subject_name {
                            ids.push(subject_name.id);
                        }
                        ids.extend(pattern.bound_ids());
                        let has_guard = guard.is_some();
                        clause_steps.push(RewriteStep::Bind(ids));
                        if let Some(guard) = guard {
                            clause_steps.push(RewriteStep::Enter(guard));
                        }
                        clause_steps.push(RewriteStep::Enter(body));
                        clause_steps.push(RewriteStep::Unbind(base));
                        clause_meta.push((pattern, has_guard));
                    }
                    steps.push(RewriteStep::Post(RewritePost::When {
                        subject_name,
                        clause_meta,
                    }));
                    for clause_step in clause_steps.into_iter().rev() {
                        steps.push(clause_step);
                    }
                    steps.push(RewriteStep::Enter(subject.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(RewriteStep::Post(RewritePost::Plain(kind)));
                        for child in children.into_iter().rev() {
                            steps.push(RewriteStep::Enter(child));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            RewriteStep::Post(post) => {
                let rebuilt = match post {
                    RewritePost::Lambda { params } => {
                        let body = done.pop().expect("lambda body");
                        PseudoExpr::Lambda {
                            params,
                            body: PBox::new(body),
                        }
                    }
                    RewritePost::RecFn { name, params } => {
                        let body = done.pop().expect("recfn body");
                        PseudoExpr::RecFn {
                            name,
                            params,
                            body: PBox::new(body),
                        }
                    }
                    RewritePost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    RewritePost::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let mut parts = take(&mut done, when_child_count(&clause_meta)).into_iter();
                        let subject = parts.next().expect("when subject");
                        let clauses = clause_meta
                            .into_iter()
                            .map(|(pattern, has_guard)| WhenClause {
                                pattern,
                                guard: has_guard.then(|| parts.next().expect("when guard")),
                                body: parts.next().expect("when clause body"),
                            })
                            .collect();
                        PseudoExpr::When {
                            subject: PBox::new(subject),
                            subject_name,
                            clauses,
                        }
                    }
                    RewritePost::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "the replace machine must leave one result");
    done.pop().expect("replace result")
}

fn choose_option_payload_binder_name(subject_hint: &str, bound: &[String]) -> String {
    for candidate in ["payload".to_string(), format!("{subject_hint}_value")] {
        if !bound.iter().any(|bound_name| bound_name == &candidate) {
            return candidate;
        }
    }

    let mut suffix = 2usize;
    loop {
        let candidate = format!("{subject_hint}_value_{suffix}");
        if !bound.iter().any(|bound_name| bound_name == &candidate) {
            return candidate;
        }
        suffix += 1;
    }
}

pub(in crate::decompile::late::normalize) fn recover_missing_option_payload_binders(
    expr: PseudoExpr,
    kind_annotations: &HashMap<VarId, VarKind>,
    use_varkind_recovery: bool,
) -> PseudoExpr {
    // Built once for the entry expression so the typed predicate
    // can resolve refs whose VarId diverged from the binder.
    let name_to_binder_id = crate::decompile::varkind_recovery::build_name_to_binder_id_map(&expr);
    fn rewrite(
        expr: PseudoExpr,
        bound: &mut Vec<String>,
        kind_annotations: &HashMap<VarId, VarKind>,
        name_to_binder_id: &HashMap<String, VarId>,
        use_varkind_recovery: bool,
    ) -> PseudoExpr {
        let mut steps = vec![RewriteStep::Enter(expr)];
        let mut done: Vec<PseudoExpr> = Vec::new();

        while let Some(step) = steps.pop() {
            match step {
                RewriteStep::Bind(names) => bound.extend(names),
                RewriteStep::Unbind(base) => bound.truncate(base),
                RewriteStep::Enter(expr) => match expr {
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        let base = bound.len();
                        let mut clause_meta = Vec::with_capacity(clauses.len());
                        // Built in pop order, then pushed in reverse.
                        let mut clause_steps = Vec::new();
                        for clause in clauses {
                            let WhenClause {
                                pattern,
                                guard,
                                body,
                            } = clause;
                            let mut names = Vec::new();
                            if let Some(subject_name) = &subject_name {
                                names.push(subject_name.name.clone());
                            }
                            names.extend(pattern.bound_names());
                            let has_guard = guard.is_some();
                            clause_steps.push(RewriteStep::Bind(names));
                            if let Some(guard) = guard {
                                clause_steps.push(RewriteStep::Enter(guard));
                            }
                            clause_steps.push(RewriteStep::Enter(body));
                            clause_steps.push(RewriteStep::Unbind(base));
                            clause_meta.push((pattern, has_guard));
                        }
                        steps.push(RewriteStep::Post(RewritePost::When {
                            subject_name,
                            clause_meta,
                        }));
                        for clause_step in clause_steps.into_iter().rev() {
                            steps.push(clause_step);
                        }
                        steps.push(RewriteStep::Enter(subject.into_inner()));
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        let base = bound.len();
                        let names = vec![name.clone()];
                        steps.push(RewriteStep::Post(RewritePost::Let { name, id }));
                        steps.push(RewriteStep::Unbind(base));
                        steps.push(RewriteStep::Enter(body.into_inner()));
                        steps.push(RewriteStep::Bind(names));
                        steps.push(RewriteStep::Enter(value.into_inner()));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        let base = bound.len();
                        let names: Vec<String> =
                            params.iter().map(|param| param.name.clone()).collect();
                        steps.push(RewriteStep::Post(RewritePost::Lambda { params }));
                        steps.push(RewriteStep::Unbind(base));
                        steps.push(RewriteStep::Enter(body.into_inner()));
                        steps.push(RewriteStep::Bind(names));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let base = bound.len();
                        let mut names = vec![name.name.clone()];
                        names.extend(params.iter().map(|param| param.name.clone()));
                        steps.push(RewriteStep::Post(RewritePost::RecFn { name, params }));
                        steps.push(RewriteStep::Unbind(base));
                        steps.push(RewriteStep::Enter(body.into_inner()));
                        steps.push(RewriteStep::Bind(names));
                    }
                    other => match plain_children(other) {
                        Ok((kind, children)) => {
                            steps.push(RewriteStep::Post(RewritePost::Plain(kind)));
                            for child in children.into_iter().rev() {
                                steps.push(RewriteStep::Enter(child));
                            }
                        }
                        Err(leaf) => done.push(leaf),
                    },
                },
                RewriteStep::Post(post) => {
                    let rebuilt = match post {
                        RewritePost::When {
                            subject_name,
                            clause_meta,
                        } => {
                            let mut parts =
                                take(&mut done, when_child_count(&clause_meta)).into_iter();
                            let subject = parts.next().expect("when subject");
                            let mut clauses = clause_meta
                                .into_iter()
                                .map(|(pattern, has_guard)| WhenClause {
                                    pattern,
                                    guard: has_guard.then(|| parts.next().expect("when guard")),
                                    body: parts.next().expect("when clause body"),
                                })
                                .collect::<Vec<_>>();

                            for clause in clauses.iter_mut() {
                                let clause_pattern_bound_ids = clause.pattern.bound_ids();
                                let WhenPattern::Constructor {
                                    type_hint,
                                    tag: 0,
                                    fields,
                                    shape,
                                    ..
                                } = &mut clause.pattern
                                else {
                                    continue;
                                };
                                let is_some = matches!(
                                    *shape,
                                    ConstructorShape::Known(KnownConstructor::Some)
                                ) || type_hint.as_ref().map(TypeHintId::as_str)
                                    == Some(OPTION_TYPE_HINT_NAME);
                                if !is_some || !fields.is_empty() {
                                    continue;
                                }

                                let mut clause_bound = bound.clone();
                                if let Some(subject_name) = &subject_name {
                                    clause_bound.push(subject_name.name.clone());
                                }
                                let mut clause_bound_ids = Vec::new();
                                if let Some(subject_name) = &subject_name {
                                    clause_bound_ids.push(subject_name.id);
                                }
                                clause_bound_ids.extend(clause_pattern_bound_ids);
                                let mut free = Vec::new();
                                if let Some(guard) = &clause.guard {
                                    collect_free_generated_payload_binders(
                                        guard,
                                        &mut clause_bound_ids,
                                        &mut free,
                                        kind_annotations,
                                        name_to_binder_id,
                                        use_varkind_recovery,
                                    );
                                }
                                collect_free_generated_payload_binders(
                                    &clause.body,
                                    &mut clause_bound_ids,
                                    &mut free,
                                    kind_annotations,
                                    name_to_binder_id,
                                    use_varkind_recovery,
                                );
                                // Reject a candidate applied as a function in the
                                // clause body or guard: an Option payload is a `Data`
                                // value, never a callee. Recovery then falls through
                                // to the subject-based path below. `choose_*` only
                                // returns a `v_NN`-style helper through its
                                // sole-candidate fallback (named
                                // `payload`/`item`/`fields` rank first;
                                // `<name>_<digit>` names are excluded from the `plain`
                                // filter), so rejecting the single pick never discards
                                // a viable alternative.
                                let chosen =
                                    choose_generated_option_payload_binder(&free).filter(|cand| {
                                        !binder_used_as_callee(&clause.body, cand)
                                            && clause
                                                .guard
                                                .as_ref()
                                                .is_none_or(|g| !binder_used_as_callee(g, cand))
                                    });
                                if let Some(payload_ref) = chosen {
                                    let binder =
                                        recovered_generated_option_payload_binder(&payload_ref);
                                    let mut replace_bound = clause_bound_ids.clone();
                                    if let Some(guard) = clause.guard.take() {
                                        clause.guard = Some(replace_free_generated_payload_binder(
                                            guard,
                                            &payload_ref,
                                            &binder,
                                            &mut replace_bound,
                                        ));
                                    }
                                    clause.body = replace_free_generated_payload_binder(
                                        clause.body.clone(),
                                        &payload_ref,
                                        &binder,
                                        &mut replace_bound,
                                    );
                                    *fields = vec![binder];
                                    *shape = ConstructorShape::Known(KnownConstructor::Some);
                                    *type_hint = None;
                                    continue;
                                }

                                let payload_subject: Option<(&str, Option<VarId>)> = subject_name
                                    .as_ref()
                                    .map(|binder| (binder.name.as_str(), Some(binder.id)))
                                    .or(match &subject {
                                        PseudoExpr::Var { name, id, .. } => {
                                            Some((name.as_str(), *id))
                                        }
                                        _ => None,
                                    });
                                if let Some((subject_hint, subject_id)) = payload_subject {
                                    let binder_name = choose_option_payload_binder_name(
                                        subject_hint,
                                        bound.as_slice(),
                                    );
                                    let binder = Binder::new(binder_name, VarId::fresh_binding());
                                    let (new_body, body_changed) = replace_subject_payload_access(
                                        clause.body.clone(),
                                        subject_id,
                                        &binder,
                                    );
                                    let (new_guard, guard_changed) = if let Some(guard) =
                                        clause.guard.take()
                                    {
                                        let (guard, guard_changed) = replace_subject_payload_access(
                                            guard, subject_id, &binder,
                                        );
                                        (Some(guard), guard_changed)
                                    } else {
                                        (None, false)
                                    };
                                    if body_changed || guard_changed {
                                        clause.body = new_body;
                                        clause.guard = new_guard;
                                        *fields = vec![binder];
                                        *shape = ConstructorShape::Known(KnownConstructor::Some);
                                        *type_hint = None;
                                    }
                                }
                            }
                            PseudoExpr::When {
                                subject: PBox::new(subject),
                                subject_name,
                                clauses,
                            }
                        }
                        RewritePost::Let { name, id } => {
                            let body = done.pop().expect("let body");
                            let value = done.pop().expect("let value");
                            PseudoExpr::Let {
                                name,
                                id,
                                value: PBox::new(value),
                                body: PBox::new(body),
                            }
                        }
                        RewritePost::Lambda { params } => {
                            let body = done.pop().expect("lambda body");
                            PseudoExpr::Lambda {
                                params,
                                body: PBox::new(body),
                            }
                        }
                        RewritePost::RecFn { name, params } => {
                            let body = done.pop().expect("recfn body");
                            PseudoExpr::RecFn {
                                name,
                                params,
                                body: PBox::new(body),
                            }
                        }
                        RewritePost::Plain(kind) => rebuild_plain(kind, &mut done),
                    };
                    done.push(rebuilt);
                }
            }
        }

        debug_assert_eq!(done.len(), 1, "the rewrite machine must leave one result");
        done.pop().expect("rewrite result")
    }

    rewrite(
        expr,
        &mut Vec::new(),
        kind_annotations,
        &name_to_binder_id,
        use_varkind_recovery,
    )
}
