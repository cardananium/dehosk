//! Post-solve enrichment of `Function` types.
//!
//! After [`harvest_final_type_table`](super::harvest::harvest_final_type_table)
//! populates the table, Lambda and RecFn values hold the conservative
//! `Function { params: [Unknown; N], ret: Unknown }` shape. A fixed-point
//! loop replaces those all-Unknown entries with concrete types read off
//! the AST: body-derivation (param types from each param `VarId`'s solved
//! entry, return type from `derive_body_type`) and call-site refinement
//! (`Apply(Var(f), args)` and curried Apply chains fill `f`'s param slots).
//!
//! Iterate up to `MAX_ENRICH_ITERATIONS` until no entry changes.
//! [`merge_more_concrete`] is monotonic (Unknown loses to concrete at
//! every nesting level, concrete-vs-concrete keeps the existing entry),
//! so the loop converges. Refined param types shadow
//! `table.type_of_var(...)` only inside the Lambda whose body is being
//! derived; the global param VarId table is never mutated, since that
//! would overcommit under polymorphic use.
//!
//! The renderer's F-suppress filter is still required: the weak-Function
//! policy in `prefer_conflict_resolution` lets `Function ⊓ Pair/List/etc.
//! → concrete data` merge past the Function evidence.

use std::rc::Rc;

use crate::decompile::final_type_table::FinalTypeTable;
use crate::pseudo::ast::{PseudoExpr, PseudoType};

/// Iteration cap. The table is monotonic (Unknown → concrete,
/// never demoted), so it settles in a few passes; the cap only
/// bounds pathological mutual recursion.
const MAX_ENRICH_ITERATIONS: usize = 8;

pub(super) fn enrich_function_types(expr: &PseudoExpr, table: &mut FinalTypeTable) {
    // Both passes increment `ctx.changed` when they rebind a
    // Function entry; the loop stops at the first idle iteration.
    for _ in 0..MAX_ENRICH_ITERATIONS {
        let mut ctx = EnrichCtx { changed: 0 };
        walk(expr, table, &mut ctx);
        refine_function_params_from_call_sites(expr, table, &mut ctx);
        if ctx.changed == 0 {
            break;
        }
    }
}

struct EnrichCtx {
    changed: usize,
}

fn walk(expr: &PseudoExpr, table: &mut FinalTypeTable, ctx: &mut EnrichCtx) {
    enum Frame<'a> {
        Enter(&'a PseudoExpr),
        Exit(&'a PseudoExpr),
    }

    let mut stack: Vec<Frame> = vec![Frame::Enter(expr)];
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Enter(node) => {
                stack.push(Frame::Exit(node));
                match node {
                    PseudoExpr::Let { value, body, .. } => {
                        stack.push(Frame::Enter(body));
                        stack.push(Frame::Enter(value));
                    }
                    PseudoExpr::RecFn { body, .. } | PseudoExpr::Lambda { body, .. } => {
                        stack.push(Frame::Enter(body));
                    }
                    PseudoExpr::When {
                        subject, clauses, ..
                    } => {
                        for clause in clauses.iter().rev() {
                            stack.push(Frame::Enter(&clause.body));
                            if let Some(guard) = &clause.guard {
                                stack.push(Frame::Enter(guard));
                            }
                        }
                        stack.push(Frame::Enter(subject));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        stack.push(Frame::Enter(else_branch));
                        stack.push(Frame::Enter(then_branch));
                        stack.push(Frame::Enter(condition));
                    }
                    PseudoExpr::Apply { function, args } => {
                        for arg in args.iter().rev() {
                            stack.push(Frame::Enter(arg));
                        }
                        stack.push(Frame::Enter(function));
                    }
                    PseudoExpr::BinOp { left, right, .. } => {
                        stack.push(Frame::Enter(right));
                        stack.push(Frame::Enter(left));
                    }
                    PseudoExpr::UnOp { operand, .. } => stack.push(Frame::Enter(operand)),
                    PseudoExpr::Constr { fields, .. } => {
                        for field in fields.iter().rev() {
                            stack.push(Frame::Enter(field));
                        }
                    }
                    PseudoExpr::BuiltinCall { args, .. } => {
                        for arg in args.iter().rev() {
                            stack.push(Frame::Enter(arg));
                        }
                    }
                    PseudoExpr::List { elements, tail } => {
                        if let Some(t) = tail {
                            stack.push(Frame::Enter(t));
                        }
                        for element in elements.iter().rev() {
                            stack.push(Frame::Enter(element));
                        }
                    }
                    PseudoExpr::Tuple(elements) => {
                        for element in elements.iter().rev() {
                            stack.push(Frame::Enter(element));
                        }
                    }
                    PseudoExpr::Pair(a, b) => {
                        stack.push(Frame::Enter(b));
                        stack.push(Frame::Enter(a));
                    }
                    PseudoExpr::FieldAccess { record, .. } => stack.push(Frame::Enter(record)),
                    PseudoExpr::IndexAccess { collection, .. } => {
                        stack.push(Frame::Enter(collection))
                    }
                    PseudoExpr::Trace { message, value } => {
                        stack.push(Frame::Enter(value));
                        stack.push(Frame::Enter(message));
                    }
                    PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                        stack.push(Frame::Enter(inner))
                    }
                    _ => {}
                }
            }
            Frame::Exit(node) => match node {
                PseudoExpr::Let { id, value, .. } => {
                    if let Some(vid) = *id {
                        match value.as_ref() {
                            PseudoExpr::Lambda {
                                params,
                                body: lbody,
                            } => {
                                refine_function_entry(table, vid, params, lbody, ctx);
                            }
                            PseudoExpr::RecFn {
                                params,
                                body: lbody,
                                ..
                            } => {
                                refine_function_entry(table, vid, params, lbody, ctx);
                            }
                            _ => {}
                        }
                    }
                }
                // RecFn not directly under a Let (e.g. nested as a Lambda
                // body or arg): post-order refine using its own name.
                PseudoExpr::RecFn { name, params, body } => {
                    refine_function_entry(table, name.id, params, body, ctx);
                }
                _ => {}
            },
        }
    }
}

fn refine_function_entry(
    table: &mut FinalTypeTable,
    binder_id: crate::pseudo::var_id::VarId,
    params: &[crate::pseudo::ast::Binder],
    body: &PseudoExpr,
    ctx: &mut EnrichCtx,
) {
    // Only refine when `binder_id` already holds a Function entry
    // of matching arity; the weak-Function policy may have
    // demoted it to a data shape, in which case leave it alone.
    let current = match table.type_of_var(binder_id) {
        Some(ty) => ty,
        None => return,
    };
    let (existing_params, existing_ret) = match current.as_ref() {
        PseudoType::Function { params: p, ret: r } if p.len() == params.len() => {
            (p.clone(), r.clone())
        }
        _ => return,
    };

    // Harvest each param's type from its own VarId entry. Merge
    // structurally so a Function-typed slot can be refined further
    // (Function([Unknown], Int) → Function([Int], Int)) instead of
    // staying frozen at the first non-Unknown shape.
    let mut refined_params = Vec::with_capacity(params.len());
    for (i, param) in params.iter().enumerate() {
        let existing = existing_params[i].clone();
        let refined = match table.type_of_var(param.id) {
            Some(candidate) => merge_more_concrete(&existing, &candidate),
            None => existing,
        };
        refined_params.push(refined);
    }

    // Local param overlay: refined param types reach
    // `derive_body_type(Var(param_id))` without mutating the global
    // table. In `let id = fn(x) { x } in id(0)`, once call-site
    // refinement sets `id.params[0]` to Int, the body's `Var(x_id)`
    // resolves to Int here, so ret refines on the next iteration.
    // A VarId write-back would leak outside this Lambda's body.
    let mut overlay = std::collections::HashMap::new();
    for (i, param) in params.iter().enumerate() {
        if !matches!(refined_params[i].as_ref(), PseudoType::Unknown) {
            overlay.insert(param.id, refined_params[i].clone());
        }
    }

    // Derive the body's type structurally; merge with the existing
    // ret so Function-typed rets can be refined recursively.
    let refined_ret = match derive_body_type_with_overlay(body, table, &overlay) {
        Some(candidate) => merge_more_concrete(&existing_ret, &candidate),
        None => existing_ret.clone(),
    };

    // Skip the rebind if nothing changed: `merge_more_concrete`
    // returns the existing Rc when the merger is a no-op, so
    // ptr-equality is a precise signal.
    //
    // Refined param types are deliberately not written back to the
    // param's VarId entry: an overcommitting call site (a param used
    // polymorphically) would stamp a wrong concrete type onto a VarId
    // that may also serve as an if condition elsewhere, tripping the
    // type-invariant pass. Body-derived rets stay Unknown instead
    // when only call-site evidence exists.
    let changed = refined_params
        .iter()
        .zip(existing_params.iter())
        .any(|(a, b)| !Rc::ptr_eq(a, b))
        || !Rc::ptr_eq(&refined_ret, &existing_ret);
    if !changed {
        return;
    }

    // `bind_var` panics after `freeze()`; enrichment runs while the
    // table is still mutable.
    table.bind_var(
        binder_id,
        Rc::new(PseudoType::Function {
            params: refined_params,
            ret: refined_ret,
        }),
    );
    ctx.changed += 1;
}

/// Merge two `PseudoType`s, preferring concrete leaves over Unknown
/// at every level, so enrichment sharpens entries monotonically.
///
/// Rules:
/// - `Unknown ⊓ T` = `T` (and vice versa).
/// - Two identical concrete types: identity.
/// - Same-arity Functions and same-shape wrappers (List, Option,
///   Pair, Result, Tuple): recurse on each child.
/// - Conflicting concrete types: keep `existing` (never demote).
///
/// Returns `existing` (no allocation) when the merger is a no-op,
/// so callers can `Rc::ptr_eq(&merged, &existing)` to detect change.
fn merge_more_concrete(existing: &Rc<PseudoType>, candidate: &Rc<PseudoType>) -> Rc<PseudoType> {
    // Pointer or structural identity → no-op
    // (prevents Unknown/Unknown churn in the fixed-point counter).
    if Rc::ptr_eq(existing, candidate) {
        return existing.clone();
    }
    if existing.as_ref() == candidate.as_ref() {
        return existing.clone();
    }
    match (existing.as_ref(), candidate.as_ref()) {
        (PseudoType::Unknown, _) => candidate.clone(),
        (_, PseudoType::Unknown) => existing.clone(),
        (
            PseudoType::Function {
                params: ep,
                ret: er,
            },
            PseudoType::Function {
                params: cp,
                ret: cr,
            },
        ) if ep.len() == cp.len() => {
            let mut merged_params = Vec::with_capacity(ep.len());
            let mut any_change = false;
            for (e, c) in ep.iter().zip(cp.iter()) {
                let merged = merge_more_concrete(e, c);
                if !Rc::ptr_eq(&merged, e) {
                    any_change = true;
                }
                merged_params.push(merged);
            }
            let merged_ret = merge_more_concrete(er, cr);
            if !Rc::ptr_eq(&merged_ret, er) {
                any_change = true;
            }
            if !any_change {
                existing.clone()
            } else {
                Rc::new(PseudoType::Function {
                    params: merged_params,
                    ret: merged_ret,
                })
            }
        }
        // Wrapper recursion: `List<Unknown>` ⊓ `List<Int>` refines
        // to `List<Int>`; same for the other wrappers below.
        (PseudoType::List(ei), PseudoType::List(ci)) => {
            let merged = merge_more_concrete(ei, ci);
            if Rc::ptr_eq(&merged, ei) {
                existing.clone()
            } else {
                Rc::new(PseudoType::List(merged))
            }
        }
        (PseudoType::Option(ei), PseudoType::Option(ci)) => {
            let merged = merge_more_concrete(ei, ci);
            if Rc::ptr_eq(&merged, ei) {
                existing.clone()
            } else {
                Rc::new(PseudoType::Option(merged))
            }
        }
        (PseudoType::Pair(ea, eb), PseudoType::Pair(ca, cb)) => {
            let ma = merge_more_concrete(ea, ca);
            let mb = merge_more_concrete(eb, cb);
            if Rc::ptr_eq(&ma, ea) && Rc::ptr_eq(&mb, eb) {
                existing.clone()
            } else {
                Rc::new(PseudoType::Pair(ma, mb))
            }
        }
        (PseudoType::Result(eok, eerr), PseudoType::Result(cok, cerr)) => {
            let mok = merge_more_concrete(eok, cok);
            let merr = merge_more_concrete(eerr, cerr);
            if Rc::ptr_eq(&mok, eok) && Rc::ptr_eq(&merr, eerr) {
                existing.clone()
            } else {
                Rc::new(PseudoType::Result(mok, merr))
            }
        }
        (PseudoType::Tuple(ev), PseudoType::Tuple(cv)) if ev.len() == cv.len() => {
            let mut merged = Vec::with_capacity(ev.len());
            let mut any_change = false;
            for (e, c) in ev.iter().zip(cv.iter()) {
                let m = merge_more_concrete(e, c);
                if !Rc::ptr_eq(&m, e) {
                    any_change = true;
                }
                merged.push(m);
            }
            if !any_change {
                existing.clone()
            } else {
                Rc::new(PseudoType::Tuple(merged))
            }
        }
        // Conflicting concretes: keep existing (never demote).
        _ => existing.clone(),
    }
}

/// `derive_body_type_with_overlay` with an empty overlay, for
/// callers with no param-overlay context (call-site refinement).
fn derive_body_type(expr: &PseudoExpr, table: &FinalTypeTable) -> Option<Rc<PseudoType>> {
    derive_body_type_with_overlay(expr, table, &ParamOverlay::default())
}

type ParamOverlay = std::collections::HashMap<crate::pseudo::var_id::VarId, Rc<PseudoType>>;

/// Structurally derive a concrete type for a Lambda's body
/// expression; `None` for any shape the rules don't recognize,
/// which the caller reads as `Unknown`.
///
/// For a `Var` whose binder is in `overlay`, the overlay shadows
/// `table.type_of_var(...)`, carrying call-site-refined param
/// types into the body without mutating the global table. The
/// overlay is local to the Lambda being derived.
fn derive_body_type_with_overlay(
    expr: &PseudoExpr,
    table: &FinalTypeTable,
    overlay: &ParamOverlay,
) -> Option<Rc<PseudoType>> {
    type Ty = Rc<PseudoType>;

    enum Frame<'a> {
        IfThen {
            else_branch: &'a PseudoExpr,
        },
        IfElse {
            t1: Ty,
        },
        WhenFirst {
            rest: std::slice::Iter<'a, crate::pseudo::ast::WhenClause>,
        },
        WhenRest {
            first: Ty,
            rest: std::slice::Iter<'a, crate::pseudo::ast::WhenClause>,
        },
        ListElem {
            inner: Ty,
            rest: std::slice::Iter<'a, PseudoExpr>,
            tail: Option<&'a PseudoExpr>,
        },
        ListTail {
            inner: Ty,
        },
        PairA {
            b: &'a PseudoExpr,
        },
        PairB {
            ta: Ty,
        },
        TupleElem {
            collected: Vec<Ty>,
            rest: std::slice::Iter<'a, PseudoExpr>,
        },
        ApplyArgs {
            args_len: usize,
        },
    }

    enum Step<'a> {
        Eval(&'a PseudoExpr),
        Resume(Option<Ty>),
    }

    let mut stack: Vec<Frame> = Vec::new();
    let mut step = Step::Eval(expr);

    loop {
        // Evaluate a leaf directly into `value`; a compound node instead
        // pushes the `Frame` its first child's return will resume into,
        // redirects `step` to that child, and `continue`s — exactly the
        // original's first recursive call, minus the native stack frame.
        let value: Option<Ty> = match step {
            Step::Resume(v) => v,
            Step::Eval(node) => match node {
                PseudoExpr::Int(_) => Some(Rc::new(PseudoType::Int)),
                PseudoExpr::ByteArray(_) => Some(Rc::new(PseudoType::ByteArray)),
                PseudoExpr::String(_) => Some(Rc::new(PseudoType::String)),
                PseudoExpr::Bool(_) => Some(Rc::new(PseudoType::Bool)),
                PseudoExpr::Unit => Some(Rc::new(PseudoType::Unit)),
                PseudoExpr::Var { id: Some(vid), .. } => overlay
                    .get(vid)
                    .cloned()
                    .or_else(|| table.type_of_var(*vid)),
                // Let chain: the chain's type is the inner body's type.
                PseudoExpr::Let { body, .. } => {
                    step = Step::Eval(body);
                    continue;
                }
                // If/When: the branches must agree on a concrete type.
                PseudoExpr::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    stack.push(Frame::IfThen { else_branch });
                    step = Step::Eval(then_branch);
                    continue;
                }
                PseudoExpr::When { clauses, .. } => {
                    let mut iter = clauses.iter();
                    match iter.next() {
                        Some(first_clause) => {
                            stack.push(Frame::WhenFirst { rest: iter });
                            step = Step::Eval(&first_clause.body);
                            continue;
                        }
                        None => None,
                    }
                }
                // Lambda/RecFn body → Function type. A Lambda has no
                // binder to look up, so it emits the baseline arity shape.
                PseudoExpr::Lambda { params, .. } => Some(Rc::new(PseudoType::Function {
                    params: (0..params.len())
                        .map(|_| Rc::new(PseudoType::Unknown))
                        .collect(),
                    ret: Rc::new(PseudoType::Unknown),
                })),
                PseudoExpr::RecFn { name, params, .. } => {
                    // Prefer the entry under `name.id`, already enriched
                    // by the post-order walk; fall back to the baseline
                    // shape.
                    match table.type_of_var(name.id) {
                        Some(ty) if matches!(ty.as_ref(), PseudoType::Function { .. }) => Some(ty),
                        _ => Some(Rc::new(PseudoType::Function {
                            params: (0..params.len())
                                .map(|_| Rc::new(PseudoType::Unknown))
                                .collect(),
                            ret: Rc::new(PseudoType::Unknown),
                        })),
                    }
                }
                // Arithmetic / comparison return types, mirroring the
                // arms in `type_solver/mod.rs::expr_type_var::BinOp`.
                PseudoExpr::BinOp { op, .. } => {
                    use crate::pseudo::ast::BinaryOp;
                    match op {
                        BinaryOp::Add
                        | BinaryOp::Sub
                        | BinaryOp::Mul
                        | BinaryOp::Div
                        | BinaryOp::Mod => Some(Rc::new(PseudoType::Int)),
                        BinaryOp::Eq
                        | BinaryOp::Neq
                        | BinaryOp::Lt
                        | BinaryOp::Lte
                        | BinaryOp::Gt
                        | BinaryOp::Gte
                        | BinaryOp::And
                        | BinaryOp::Or => Some(Rc::new(PseudoType::Bool)),
                        BinaryOp::Cons | BinaryOp::Concat => None,
                    }
                }
                PseudoExpr::UnOp { op, .. } => {
                    use crate::pseudo::ast::UnaryOp;
                    match op {
                        UnaryOp::Not => Some(Rc::new(PseudoType::Bool)),
                        UnaryOp::Negate | UnaryOp::Length => Some(Rc::new(PseudoType::Int)),
                    }
                }
                PseudoExpr::BuiltinCall { name, args } => {
                    // Reuse the solver's monomorphic return-type table.
                    super::infer_builtin_return_type(name, args).map(Rc::new)
                }
                // Wrapper bodies: inner types come from elements.
                PseudoExpr::List { elements, tail } => {
                    // If no element's type resolves, inner stays Unknown;
                    // a bare List type still beats no type at all.
                    let mut rest = elements.iter();
                    match rest.next() {
                        Some(first_el) => {
                            stack.push(Frame::ListElem {
                                inner: Rc::new(PseudoType::Unknown),
                                rest,
                                tail: tail.as_deref(),
                            });
                            step = Step::Eval(first_el);
                            continue;
                        }
                        // The tail is itself a `List<inner>`-typed
                        // expression; unify its inner if available.
                        None => match tail.as_deref() {
                            Some(t) => {
                                stack.push(Frame::ListTail {
                                    inner: Rc::new(PseudoType::Unknown),
                                });
                                step = Step::Eval(t);
                                continue;
                            }
                            None => Some(Rc::new(PseudoType::List(Rc::new(PseudoType::Unknown)))),
                        },
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    stack.push(Frame::PairA { b });
                    step = Step::Eval(a);
                    continue;
                }
                PseudoExpr::Tuple(elements) => {
                    let mut rest = elements.iter();
                    match rest.next() {
                        Some(first_el) => {
                            stack.push(Frame::TupleElem {
                                collected: Vec::with_capacity(elements.len()),
                                rest,
                            });
                            step = Step::Eval(first_el);
                            continue;
                        }
                        None => Some(Rc::new(PseudoType::Tuple(Vec::new()))),
                    }
                }
                // Apply chain: resolve the function's type, consume args
                // left-to-right against its params, return the residual
                // (see `apply_function_type`).
                PseudoExpr::Apply { function, args } => {
                    stack.push(Frame::ApplyArgs {
                        args_len: args.len(),
                    });
                    step = Step::Eval(function);
                    continue;
                }
                _ => None,
            },
        };

        // `value` is the just-completed child's result; feed it to the
        // frame that was waiting on it, or (empty stack) return it as the
        // whole call's result — this is the "return to caller" half of
        // every recursive call above.
        let Some(frame) = stack.pop() else {
            return value;
        };
        step = match frame {
            Frame::IfThen { else_branch } => match value {
                None => Step::Resume(None),
                Some(t1) => {
                    stack.push(Frame::IfElse { t1 });
                    Step::Eval(else_branch)
                }
            },
            Frame::IfElse { t1 } => match value {
                None => Step::Resume(None),
                Some(t2) => {
                    if Rc::ptr_eq(&t1, &t2) || *t1 == *t2 {
                        Step::Resume(Some(t1))
                    } else {
                        Step::Resume(None)
                    }
                }
            },
            Frame::WhenFirst { mut rest } => match value {
                None => Step::Resume(None),
                Some(first) => match rest.next() {
                    Some(next_clause) => {
                        stack.push(Frame::WhenRest { first, rest });
                        Step::Eval(&next_clause.body)
                    }
                    None => Step::Resume(Some(first)),
                },
            },
            Frame::WhenRest { first, mut rest } => match value {
                None => Step::Resume(None),
                Some(t) if !(Rc::ptr_eq(&t, &first) || *t == *first) => Step::Resume(None),
                Some(_) => match rest.next() {
                    Some(next_clause) => {
                        stack.push(Frame::WhenRest { first, rest });
                        Step::Eval(&next_clause.body)
                    }
                    None => Step::Resume(Some(first)),
                },
            },
            Frame::ListElem {
                mut inner,
                mut rest,
                tail,
            } => {
                if let Some(t) = value {
                    inner = merge_more_concrete(&inner, &t);
                }
                match rest.next() {
                    Some(next_el) => {
                        stack.push(Frame::ListElem { inner, rest, tail });
                        Step::Eval(next_el)
                    }
                    None => match tail {
                        Some(t) => {
                            stack.push(Frame::ListTail { inner });
                            Step::Eval(t)
                        }
                        None => Step::Resume(Some(Rc::new(PseudoType::List(inner)))),
                    },
                }
            }
            Frame::ListTail { mut inner } => {
                if let Some(tt) = value {
                    if let PseudoType::List(tail_inner) = tt.as_ref() {
                        inner = merge_more_concrete(&inner, tail_inner);
                    }
                }
                Step::Resume(Some(Rc::new(PseudoType::List(inner))))
            }
            Frame::PairA { b } => {
                let ta = value.unwrap_or_else(|| Rc::new(PseudoType::Unknown));
                stack.push(Frame::PairB { ta });
                Step::Eval(b)
            }
            Frame::PairB { ta } => {
                let tb = value.unwrap_or_else(|| Rc::new(PseudoType::Unknown));
                Step::Resume(Some(Rc::new(PseudoType::Pair(ta, tb))))
            }
            Frame::TupleElem {
                mut collected,
                mut rest,
            } => {
                collected.push(value.unwrap_or_else(|| Rc::new(PseudoType::Unknown)));
                match rest.next() {
                    Some(next_el) => {
                        stack.push(Frame::TupleElem { collected, rest });
                        Step::Eval(next_el)
                    }
                    None => Step::Resume(Some(Rc::new(PseudoType::Tuple(collected)))),
                }
            }
            Frame::ApplyArgs { args_len } => match value {
                Some(fn_ty) => Step::Resume(apply_function_type(fn_ty, args_len, table)),
                None => Step::Resume(None),
            },
        };
    }
}

/// Residual type after applying `consumed` args to `fn_ty`.
/// `table` is only a passthrough for the nested recursion; the
/// shape of `fn_ty` decides the result.
fn apply_function_type(
    fn_ty: Rc<PseudoType>,
    consumed: usize,
    table: &FinalTypeTable,
) -> Option<Rc<PseudoType>> {
    let (params, ret) = match fn_ty.as_ref() {
        PseudoType::Function { params, ret } => (params.clone(), ret.clone()),
        _ => return None,
    };
    let n = params.len();
    if consumed == n {
        Some(ret)
    } else if consumed < n {
        // Partial: residual Function with the still-pending params.
        Some(Rc::new(PseudoType::Function {
            params: params[consumed..].to_vec(),
            ret,
        }))
    } else {
        // Over-apply: recurse on `ret` with the remaining args.
        // Curried chains appear as `Apply(Apply(f, [a]), [b])`,
        // which flattens only when each intermediate ret is
        // itself a Function.
        apply_function_type(ret, consumed - n, table)
    }
}

/// Walk the AST and refine Function param slots from concrete
/// call-site arg types.
///
/// At `Apply(Var(f), args)`, the arg type at position `i` refines
/// `f`'s `params[i]` only while that slot is Unknown; a concrete
/// slot is never demoted. Curried chains (`Apply(Apply(f, [a]),
/// [b])`) are flattened first, down to the terminal Var binder.
fn refine_function_params_from_call_sites(
    expr: &PseudoExpr,
    table: &mut FinalTypeTable,
    ctx: &mut EnrichCtx,
) {
    visit_apply_sites(expr, table, ctx);
}

fn visit_apply_sites(expr: &PseudoExpr, table: &mut FinalTypeTable, ctx: &mut EnrichCtx) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let PseudoExpr::Apply { .. } = current {
            if let Some((target_id, args)) = flatten_apply_to_target(current) {
                refine_function_from_args(target_id, &args, table, ctx);
            }
        }
        match current {
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            PseudoExpr::Apply { function, args } => {
                for arg in args.iter().rev() {
                    pending.push(arg);
                }
                pending.push(function);
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
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
                pending.push(condition);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::Constr { fields, .. } => {
                for field in fields.iter().rev() {
                    pending.push(field);
                }
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args.iter().rev() {
                    pending.push(arg);
                }
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    pending.push(t);
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
            PseudoExpr::Pair(a, b) => {
                pending.push(b);
                pending.push(a);
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            _ => {}
        }
    }
}

/// Peel curried-Apply chains down to a terminal `Var { id }` target,
/// collecting all args in application order
/// (`Apply(Apply(f, [a]), [b])` → `(f.id, [a, b])`).
/// Returns `None` if the terminal is not a Var with an id.
fn flatten_apply_to_target(
    expr: &PseudoExpr,
) -> Option<(crate::pseudo::var_id::VarId, Vec<PseudoExpr>)> {
    let mut current = expr;
    let mut all_args: Vec<PseudoExpr> = Vec::new();
    loop {
        match current {
            PseudoExpr::Apply { function, args } => {
                // Peeling runs outside-in, so prepend this level's args to
                // keep the final list in application order.
                let mut new_args = args.clone();
                new_args.extend(all_args);
                all_args = new_args.into_vec();
                current = function.as_ref();
            }
            PseudoExpr::Var { id: Some(vid), .. } => return Some((*vid, all_args)),
            _ => return None,
        }
    }
}

/// Refine `target_id`'s Function entry from concrete arg types,
/// sharpening Unknown leaves and never demoting a concrete one.
/// Args past the current arity are ignored (curried over-apply);
/// the residual ret-as-Function is left to forward derivation.
fn refine_function_from_args(
    target_id: crate::pseudo::var_id::VarId,
    args: &[PseudoExpr],
    table: &mut FinalTypeTable,
    ctx: &mut EnrichCtx,
) {
    let current = match table.type_of_var(target_id) {
        Some(ty) => ty,
        None => return,
    };
    let (existing_params, existing_ret) = match current.as_ref() {
        PseudoType::Function { params, ret } => (params.clone(), ret.clone()),
        _ => return,
    };

    // Merge structurally so a partially-refined Function slot can
    // be sharpened further, not frozen at its first shape.
    let mut refined_params = existing_params.clone();
    let mut any_change = false;
    for (i, arg) in args.iter().enumerate() {
        if i >= refined_params.len() {
            break;
        }
        if let Some(arg_ty) = derive_body_type(arg, table) {
            let merged = merge_more_concrete(&refined_params[i], &arg_ty);
            if !Rc::ptr_eq(&merged, &refined_params[i]) {
                refined_params[i] = merged;
                any_change = true;
            }
        }
    }
    if !any_change {
        return;
    }

    table.bind_var(
        target_id,
        Rc::new(PseudoType::Function {
            params: refined_params,
            ret: existing_ret,
        }),
    );
    ctx.changed += 1;
}

#[cfg(test)]
mod tests;
