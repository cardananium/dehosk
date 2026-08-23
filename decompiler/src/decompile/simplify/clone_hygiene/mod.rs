//! Hygienic cloning for simplify inlining paths.
//!
//! Inlining transforms such as `replace_forced_var` copy a
//! subtree; without renumbering, every copy shares the
//! original binder `VarId`s, violating the "one binder per
//! id" invariant and stranding refs across clones.
//!
//! `clone_with_fresh_binder_ids` deep-clones an expression,
//! allocating a fresh `VarId` (via a caller-supplied
//! callback) for every binder and retargeting internal refs
//! through a scope stack. External captures — refs to
//! binders outside the cloned subtree — and
//! compat-placeholder ids (`id.get().is_none()`) pass
//! through unchanged.
//!
//! Pass `|| simplifier.fresh_synthetic_binding_id()` as the
//! callback: the per-instance counter keeps fresh ids
//! deterministic within a run, where the process-wide
//! `VarId::fresh_binding()` counter drifts between runs.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::builtins::BuiltinId;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::type_hint::TypeHintId;
use crate::pseudo::var_id::VarId;

/// `fresh` is called once per authoritative binder; its `VarId`
/// becomes the binder's new id and is recorded on the scope stack
/// so internal refs with the old id rewrite to it.
pub(crate) fn clone_with_fresh_binder_ids<F>(expr: &PseudoExpr, mut fresh: F) -> PseudoExpr
where
    F: FnMut() -> VarId,
{
    let mut stack: Vec<HashMap<VarId, VarId>> = vec![HashMap::new()];
    go(expr, &mut stack, &mut fresh)
}

fn lookup(stack: &[HashMap<VarId, VarId>], old: VarId) -> Option<VarId> {
    for frame in stack.iter().rev() {
        if let Some(&new) = frame.get(&old) {
            return Some(new);
        }
    }
    None
}

fn allocate_for<F>(stack: &mut [HashMap<VarId, VarId>], old: VarId, fresh: &mut F) -> VarId
where
    F: FnMut() -> VarId,
{
    // Compat-placeholder ids are not authoritative binders —
    // leave them unchanged for compat-dependent outer paths.
    if old.get().is_none() {
        return old;
    }
    let new = fresh();
    if let Some(top) = stack.last_mut() {
        top.insert(old, new);
    }
    new
}

fn rebind<F>(stack: &mut [HashMap<VarId, VarId>], b: &Binder, fresh: &mut F) -> Binder
where
    F: FnMut() -> VarId,
{
    let new_id = allocate_for(stack, b.var_id(), fresh);
    Binder::new(b.as_str().to_string(), new_id)
}

/// A `Visit` reads a borrowed child; a `Post*` reassembles the owned clone of
/// a node once its children's clones are sitting on `done`, mirroring
/// `crate::pseudo::fold`'s `FoldStep`/`PostKind` split — the two-stage
/// `PostLetOpenBody` / `PostLetFinal` pair for `Let` is that machinery's
/// `LetBody`/`LetPost`, needed because the fresh binder id must be allocated
/// (and scoped) BETWEEN cloning the value and cloning the body, never before.
enum Step<'a> {
    Visit(&'a PseudoExpr),
    /// The value is cloned; push its scope, allocate its (possibly fresh)
    /// binder id, then clone the body inside that scope.
    PostLetOpenBody {
        name: &'a str,
        id: Option<VarId>,
        body: &'a PseudoExpr,
    },
    /// The body is cloned; pop the scope and assemble the `Let`.
    PostLetFinal {
        name: &'a str,
        new_id: Option<VarId>,
        value: PseudoExpr,
    },
    PostLambda {
        params: Vec<Binder>,
    },
    PostRecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    PostApply {
        argc: usize,
    },
    PostIf,
    PostBinOp {
        op: BinaryOp,
    },
    PostUnOp {
        op: UnaryOp,
    },
    PostBuiltinCall {
        name: BuiltinId,
        argc: usize,
    },
    PostDelay,
    PostForce,
    PostTrace,
    PostList {
        count: usize,
        has_tail: bool,
    },
    PostTuple {
        count: usize,
    },
    PostPair,
    PostConstr {
        type_hint: Option<TypeHintId>,
        tag: usize,
        count: usize,
        shape: ConstructorShape,
    },
    PostFieldAccess {
        selector: FieldSelector,
    },
    PostIndexAccess {
        index: usize,
    },
}

/// Deep-clone `expr`, allocating fresh binder ids and retargeting internal
/// refs. See the module doc for the scope-stack contract `stack`/`fresh`
/// keep with `lookup`/`allocate_for`/`rebind`.
fn go<F>(expr: &PseudoExpr, stack: &mut Vec<HashMap<VarId, VarId>>, fresh: &mut F) -> PseudoExpr
where
    F: FnMut() -> VarId,
{
    fn take(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
        let at = done.len() - n;
        done.split_off(at)
    }

    let mut steps: Vec<Step<'_>> = vec![Step::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Visit(expr) => match expr {
                PseudoExpr::Var { name, id } => {
                    done.push(PseudoExpr::Var {
                        name: name.clone(),
                        id: id.and_then(|v| lookup(stack, v)).or(*id),
                    });
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    // Value is evaluated in the OUTER scope — no fresh
                    // binder is in scope yet.
                    steps.push(Step::PostLetOpenBody {
                        name,
                        id: *id,
                        body,
                    });
                    steps.push(Step::Visit(value));
                }
                PseudoExpr::Lambda { params, body } => {
                    stack.push(HashMap::new());
                    let new_params: Vec<Binder> =
                        params.iter().map(|b| rebind(stack, b, fresh)).collect();
                    steps.push(Step::PostLambda { params: new_params });
                    steps.push(Step::Visit(body));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    stack.push(HashMap::new());
                    let new_name = rebind(stack, name, fresh);
                    let new_params: Vec<Binder> =
                        params.iter().map(|b| rebind(stack, b, fresh)).collect();
                    steps.push(Step::PostRecFn {
                        name: new_name,
                        params: new_params,
                    });
                    steps.push(Step::Visit(body));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    // Subject is evaluated in the outer scope — subject_name
                    // binder is only in scope inside the clauses. See `go`'s
                    // doc: this whole node is cloned via bounded recursion,
                    // not decomposed into the step machine.
                    let new_subject = go(subject, stack, fresh);
                    let pushed = subject_name.is_some();
                    if pushed {
                        stack.push(HashMap::new());
                    }
                    let new_subject_name = subject_name.as_ref().map(|b| rebind(stack, b, fresh));
                    let new_clauses: Vec<WhenClause> = clauses
                        .iter()
                        .map(|c| clone_clause(c, stack, fresh))
                        .collect();
                    if pushed {
                        stack.pop();
                    }
                    done.push(PseudoExpr::When {
                        subject: PBox::new(new_subject),
                        subject_name: new_subject_name,
                        clauses: new_clauses,
                    });
                }
                PseudoExpr::Apply { function, args } => {
                    steps.push(Step::PostApply { argc: args.len() });
                    for a in args.iter().rev() {
                        steps.push(Step::Visit(a));
                    }
                    steps.push(Step::Visit(function));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(Step::PostIf);
                    steps.push(Step::Visit(else_branch));
                    steps.push(Step::Visit(then_branch));
                    steps.push(Step::Visit(condition));
                }
                PseudoExpr::BinOp { op, left, right } => {
                    steps.push(Step::PostBinOp { op: *op });
                    steps.push(Step::Visit(right));
                    steps.push(Step::Visit(left));
                }
                PseudoExpr::UnOp { op, operand } => {
                    steps.push(Step::PostUnOp { op: *op });
                    steps.push(Step::Visit(operand));
                }
                PseudoExpr::BuiltinCall { name, args } => {
                    steps.push(Step::PostBuiltinCall {
                        name: *name,
                        argc: args.len(),
                    });
                    for a in args.iter().rev() {
                        steps.push(Step::Visit(a));
                    }
                }
                PseudoExpr::Delay(inner) => {
                    steps.push(Step::PostDelay);
                    steps.push(Step::Visit(inner));
                }
                PseudoExpr::Force(inner) => {
                    steps.push(Step::PostForce);
                    steps.push(Step::Visit(inner));
                }
                PseudoExpr::Trace { message, value } => {
                    steps.push(Step::PostTrace);
                    steps.push(Step::Visit(value));
                    steps.push(Step::Visit(message));
                }
                PseudoExpr::List { elements, tail } => {
                    steps.push(Step::PostList {
                        count: elements.len(),
                        has_tail: tail.is_some(),
                    });
                    if let Some(t) = tail.as_deref() {
                        steps.push(Step::Visit(t));
                    }
                    for e in elements.iter().rev() {
                        steps.push(Step::Visit(e));
                    }
                }
                PseudoExpr::Tuple(items) => {
                    steps.push(Step::PostTuple { count: items.len() });
                    for i in items.iter().rev() {
                        steps.push(Step::Visit(i));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    steps.push(Step::PostPair);
                    steps.push(Step::Visit(b));
                    steps.push(Step::Visit(a));
                }
                PseudoExpr::Constr {
                    type_hint,
                    tag,
                    fields,
                    shape,
                } => {
                    steps.push(Step::PostConstr {
                        type_hint: type_hint.clone(),
                        tag: *tag,
                        count: fields.len(),
                        shape: *shape,
                    });
                    for f in fields.iter().rev() {
                        steps.push(Step::Visit(f));
                    }
                }
                PseudoExpr::FieldAccess { record, selector } => {
                    steps.push(Step::PostFieldAccess {
                        selector: selector.clone(),
                    });
                    steps.push(Step::Visit(record));
                }
                PseudoExpr::IndexAccess { collection, index } => {
                    steps.push(Step::PostIndexAccess { index: *index });
                    steps.push(Step::Visit(collection));
                }
                // Leaves: no binders, no refs to retarget.
                PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::Unit
                | PseudoExpr::Error { .. }
                | PseudoExpr::Raw { .. }
                | PseudoExpr::Data(_)
                | PseudoExpr::HelperSymbol(_) => done.push(expr.clone()),
            },
            Step::PostLetOpenBody { name, id, body } => {
                let value = done.pop().expect("let value");
                stack.push(HashMap::new());
                let new_id = id.map(|v| allocate_for(stack, v, fresh));
                steps.push(Step::PostLetFinal {
                    name,
                    new_id,
                    value,
                });
                steps.push(Step::Visit(body));
            }
            Step::PostLetFinal {
                name,
                new_id,
                value,
            } => {
                let body = done.pop().expect("let body");
                stack.pop();
                done.push(PseudoExpr::Let {
                    name: name.to_string(),
                    id: new_id,
                    value: PBox::new(value),
                    body: PBox::new(body),
                });
            }
            Step::PostLambda { params } => {
                let body = done.pop().expect("lambda body");
                stack.pop();
                done.push(PseudoExpr::Lambda {
                    params,
                    body: PBox::new(body),
                });
            }
            Step::PostRecFn { name, params } => {
                let body = done.pop().expect("recfn body");
                stack.pop();
                done.push(PseudoExpr::RecFn {
                    name,
                    params,
                    body: PBox::new(body),
                });
            }
            Step::PostApply { argc } => {
                let args = take(&mut done, argc);
                let function = done.pop().expect("apply function");
                done.push(PseudoExpr::Apply {
                    function: PBox::new(function),
                    args: args.into(),
                });
            }
            Step::PostIf => {
                let else_branch = done.pop().expect("if else");
                let then_branch = done.pop().expect("if then");
                let condition = done.pop().expect("if condition");
                done.push(PseudoExpr::If {
                    condition: PBox::new(condition),
                    then_branch: PBox::new(then_branch),
                    else_branch: PBox::new(else_branch),
                });
            }
            Step::PostBinOp { op } => {
                let right = done.pop().expect("binop right");
                let left = done.pop().expect("binop left");
                done.push(PseudoExpr::BinOp {
                    op,
                    left: PBox::new(left),
                    right: PBox::new(right),
                });
            }
            Step::PostUnOp { op } => {
                let operand = done.pop().expect("unop operand");
                done.push(PseudoExpr::UnOp {
                    op,
                    operand: PBox::new(operand),
                });
            }
            Step::PostBuiltinCall { name, argc } => {
                let args = take(&mut done, argc);
                done.push(PseudoExpr::BuiltinCall {
                    name,
                    args: args.into(),
                });
            }
            Step::PostDelay => {
                let inner = done.pop().expect("delay inner");
                done.push(PseudoExpr::Delay(PBox::new(inner)));
            }
            Step::PostForce => {
                let inner = done.pop().expect("force inner");
                done.push(PseudoExpr::Force(PBox::new(inner)));
            }
            Step::PostTrace => {
                let value = done.pop().expect("trace value");
                let message = done.pop().expect("trace message");
                done.push(PseudoExpr::Trace {
                    message: PBox::new(message),
                    value: PBox::new(value),
                });
            }
            Step::PostList { count, has_tail } => {
                let tail = if has_tail { done.pop() } else { None };
                let elements = take(&mut done, count);
                done.push(PseudoExpr::List {
                    elements: elements.into(),
                    tail: tail.map(PBox::new),
                });
            }
            Step::PostTuple { count } => {
                let elements = take(&mut done, count);
                done.push(PseudoExpr::Tuple(elements.into()));
            }
            Step::PostPair => {
                let b = done.pop().expect("pair second");
                let a = done.pop().expect("pair first");
                done.push(PseudoExpr::Pair(PBox::new(a), PBox::new(b)));
            }
            Step::PostConstr {
                type_hint,
                tag,
                count,
                shape,
            } => {
                let fields = take(&mut done, count);
                done.push(PseudoExpr::Constr {
                    type_hint,
                    tag,
                    fields: fields.into(),
                    shape,
                });
            }
            Step::PostFieldAccess { selector } => {
                let record = done.pop().expect("field access record");
                done.push(PseudoExpr::FieldAccess {
                    record: PBox::new(record),
                    selector,
                });
            }
            Step::PostIndexAccess { index } => {
                let collection = done.pop().expect("index access collection");
                done.push(PseudoExpr::IndexAccess {
                    collection: PBox::new(collection),
                    index,
                });
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "the clone machine must leave one result");
    done.pop().expect("clone result")
}

fn clone_clause<F>(
    c: &WhenClause,
    stack: &mut Vec<HashMap<VarId, VarId>>,
    fresh: &mut F,
) -> WhenClause
where
    F: FnMut() -> VarId,
{
    stack.push(HashMap::new());
    let new_pattern = clone_pattern(&c.pattern, stack, fresh);
    let new_guard = c.guard.as_ref().map(|g| go(g, stack, fresh));
    let new_body = go(&c.body, stack, fresh);
    stack.pop();
    WhenClause {
        pattern: new_pattern,
        guard: new_guard,
        body: new_body,
    }
}

fn clone_pattern<F>(
    p: &WhenPattern,
    stack: &mut Vec<HashMap<VarId, VarId>>,
    fresh: &mut F,
) -> WhenPattern
where
    F: FnMut() -> VarId,
{
    match p {
        WhenPattern::Wildcard => WhenPattern::Wildcard,
        WhenPattern::Literal(e) => WhenPattern::Literal(go(e, stack, fresh)),
        WhenPattern::Var(b) => WhenPattern::Var(rebind(stack, b, fresh)),
        WhenPattern::Constructor {
            type_hint,
            tag,
            fields,
            shape,
        } => WhenPattern::Constructor {
            type_hint: type_hint.clone(),
            tag: *tag,
            fields: fields.iter().map(|b| rebind(stack, b, fresh)).collect(),
            shape: *shape,
        },
        WhenPattern::Tuple(fs) => {
            WhenPattern::Tuple(fs.iter().map(|b| rebind(stack, b, fresh)).collect())
        }
        WhenPattern::List { elements, tail } => WhenPattern::List {
            elements: elements.iter().map(|b| rebind(stack, b, fresh)).collect(),
            tail: tail.as_ref().map(|b| rebind(stack, b, fresh)),
        },
        WhenPattern::Pair(a, b) => {
            WhenPattern::Pair(rebind(stack, a, fresh), rebind(stack, b, fresh))
        }
    }
}

#[cfg(test)]
mod tests;
