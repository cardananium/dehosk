//! Decode a fully-abstracted Church-pair constructor applied to its
//! two fields into a native `Pair`.
//!
//! The Church encoding `λa.λb.λk. k a b` applied to exactly its two
//! field arguments (not the consumer) is a 3-param lambda applied to
//! 2 args. `beta_reduce_lambda_apply` only folds exact-arity
//! applications. `hoist_church_pair_pack` recognizes the already-reduced
//! `fn(k) { k(a, b) }` form but runs far earlier, before these
//! applications are exposed — they stay hidden inside a malformed `If`
//! until `undo_if_on_function_condition` reverses it. Hence a dedicated
//! recognizer at this point.
//!
//! Consumers of these sites already destructure them natively
//! (`when v is { Pair(a, b) -> … }`).
//!
//! - Matches only the exact canonical shape: a plain `Lambda` with
//!   exactly 3 params whose body is `param2(param0, param1)`, applied
//!   to exactly 2 args. A Scott-encoded tagged-union constructor
//!   (e.g. the 5-param `λa.λb.λ_.λk.λ_. k a b`) does not match — it is
//!   not a pair and must not be rendered as one.
//! - Evaluation order is unchanged: `x`/`y` are evaluated at the
//!   application, and in `Pair(x, y)` at construction — the same point.
//!   No purity gate is needed because the fields never cross a
//!   thunk/lambda boundary.
//! - Skipped in function position: in
//!   `Apply(Apply(λa.λb.λk. k a b, [x, y]), [consumer])` the consumer
//!   is already supplied, so the inner application is a real call,
//!   and collapsing it would yield the invalid `Pair(x, y)(k)`.

use crate::builtins::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::type_hint::TypeHintId;
use crate::pseudo::var_id::VarId;

pub(super) fn decode_church_pair_application(expr: PseudoExpr) -> PseudoExpr {
    recurse(expr, false)
}

/// `in_function_position` is true when `expr` is the callee of an
/// enclosing `Apply`: the consumer is being applied to it, so it is a
/// real call, not a stored pair value, and must NOT collapse to `Pair`.
///
/// The flag propagates through the RESULT-position children of value-
/// producing wrappers (`Let` body, `If`/`When` branch results, `Force`/
/// `Delay` inner, `Trace` value) — whatever such a wrapper evaluates to
/// is what actually lands in function position. Non-result children
/// (`Let` value, `If` condition, `When` subject/guards, `Trace`
/// message) reset to `false`.
fn recurse(root: PseudoExpr, root_flag: bool) -> PseudoExpr {
    enum Step {
        /// Fold this subtree; `bool` is its own "in function position" flag.
        Enter(PseudoExpr, bool),
        Apply {
            in_function_position: bool,
            argc: usize,
        },
        Let {
            name: String,
            id: Option<VarId>,
        },
        If,
        When {
            subject_name: Option<Binder>,
            clause_shapes: Vec<(WhenPattern, bool)>,
        },
        Force,
        Delay,
        Trace,
        Lambda {
            params: Vec<Binder>,
        },
        RecFn {
            name: Binder,
            params: Vec<Binder>,
        },
        BinOp {
            op: BinaryOp,
        },
        UnOp {
            op: UnaryOp,
        },
        Constr {
            tag: usize,
            shape: ConstructorShape,
            type_hint: Option<TypeHintId>,
            count: usize,
        },
        BuiltinCall {
            name: BuiltinId,
            argc: usize,
        },
        List {
            count: usize,
            has_tail: bool,
        },
        Tuple {
            count: usize,
        },
        Pair,
        FieldAccess {
            selector: FieldSelector,
        },
        IndexAccess {
            index: usize,
        },
    }

    let mut stack = vec![Step::Enter(root, root_flag)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = stack.pop() {
        match step {
            Step::Enter(expr, flag) => match expr {
                PseudoExpr::Apply { function, args } => {
                    stack.push(Step::Apply {
                        in_function_position: flag,
                        argc: args.len(),
                    });
                    for a in args.into_iter().rev() {
                        stack.push(Step::Enter(a, false));
                    }
                    stack.push(Step::Enter(function.into_inner(), true));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    stack.push(Step::Let { name, id });
                    stack.push(Step::Enter(body.into_inner(), flag));
                    stack.push(Step::Enter(value.into_inner(), false));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    stack.push(Step::If);
                    stack.push(Step::Enter(else_branch.into_inner(), flag));
                    stack.push(Step::Enter(then_branch.into_inner(), flag));
                    stack.push(Step::Enter(condition.into_inner(), false));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let mut clause_shapes = Vec::with_capacity(clauses.len());
                    let mut clause_exprs = Vec::with_capacity(clauses.len());
                    for c in clauses {
                        clause_shapes.push((c.pattern, c.guard.is_some()));
                        clause_exprs.push((c.guard, c.body));
                    }
                    stack.push(Step::When {
                        subject_name,
                        clause_shapes,
                    });
                    for (guard, body) in clause_exprs.into_iter().rev() {
                        stack.push(Step::Enter(body, flag));
                        if let Some(g) = guard {
                            stack.push(Step::Enter(g, false));
                        }
                    }
                    stack.push(Step::Enter(subject.into_inner(), false));
                }
                PseudoExpr::Force(inner) => {
                    stack.push(Step::Force);
                    stack.push(Step::Enter(inner.into_inner(), flag));
                }
                PseudoExpr::Delay(inner) => {
                    stack.push(Step::Delay);
                    stack.push(Step::Enter(inner.into_inner(), flag));
                }
                PseudoExpr::Trace { message, value } => {
                    stack.push(Step::Trace);
                    stack.push(Step::Enter(value.into_inner(), flag));
                    stack.push(Step::Enter(message.into_inner(), false));
                }
                PseudoExpr::Lambda { params, body } => {
                    stack.push(Step::Lambda { params });
                    stack.push(Step::Enter(body.into_inner(), false));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    stack.push(Step::RecFn { name, params });
                    stack.push(Step::Enter(body.into_inner(), false));
                }
                PseudoExpr::BinOp { op, left, right } => {
                    stack.push(Step::BinOp { op });
                    stack.push(Step::Enter(right.into_inner(), false));
                    stack.push(Step::Enter(left.into_inner(), false));
                }
                PseudoExpr::UnOp { op, operand } => {
                    stack.push(Step::UnOp { op });
                    stack.push(Step::Enter(operand.into_inner(), false));
                }
                PseudoExpr::Constr {
                    tag,
                    fields,
                    shape,
                    type_hint,
                } => {
                    stack.push(Step::Constr {
                        tag,
                        shape,
                        type_hint,
                        count: fields.len(),
                    });
                    for f in fields.into_iter().rev() {
                        stack.push(Step::Enter(f, false));
                    }
                }
                PseudoExpr::BuiltinCall { name, args } => {
                    stack.push(Step::BuiltinCall {
                        name,
                        argc: args.len(),
                    });
                    for a in args.into_iter().rev() {
                        stack.push(Step::Enter(a, false));
                    }
                }
                PseudoExpr::List { elements, tail } => {
                    stack.push(Step::List {
                        count: elements.len(),
                        has_tail: tail.is_some(),
                    });
                    if let Some(t) = tail {
                        stack.push(Step::Enter(t.into_inner(), false));
                    }
                    for e in elements.into_iter().rev() {
                        stack.push(Step::Enter(e, false));
                    }
                }
                PseudoExpr::Tuple(elements) => {
                    stack.push(Step::Tuple {
                        count: elements.len(),
                    });
                    for e in elements.into_iter().rev() {
                        stack.push(Step::Enter(e, false));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    stack.push(Step::Pair);
                    stack.push(Step::Enter(b.into_inner(), false));
                    stack.push(Step::Enter(a.into_inner(), false));
                }
                PseudoExpr::FieldAccess { record, selector } => {
                    stack.push(Step::FieldAccess { selector });
                    stack.push(Step::Enter(record.into_inner(), false));
                }
                PseudoExpr::IndexAccess { collection, index } => {
                    stack.push(Step::IndexAccess { index });
                    stack.push(Step::Enter(collection.into_inner(), false));
                }
                // Leaves (Int/ByteArray/String/Bool/Unit/Var/Error/Raw/
                // Data/HelperSymbol): no children, never `Apply`, pass
                // through untouched regardless of `flag`.
                leaf => done.push(leaf),
            },

            Step::Apply {
                in_function_position,
                argc,
            } => {
                let args = done.split_off(done.len() - argc);
                let function = done.pop().expect("apply function");
                let rebuilt = PseudoExpr::Apply {
                    function: PBox::new(function),
                    args: args.into(),
                };
                done.push(if in_function_position {
                    rebuilt
                } else {
                    try_decode_pair(rebuilt)
                });
            }
            Step::Let { name, id } => {
                let body = done.pop().expect("let body");
                let value = done.pop().expect("let value");
                done.push(PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(body),
                });
            }
            Step::If => {
                let else_branch = done.pop().expect("if else");
                let then_branch = done.pop().expect("if then");
                let condition = done.pop().expect("if condition");
                done.push(PseudoExpr::If {
                    condition: PBox::new(condition),
                    then_branch: PBox::new(then_branch),
                    else_branch: PBox::new(else_branch),
                });
            }
            Step::When {
                subject_name,
                clause_shapes,
            } => {
                let total: usize = 1 + clause_shapes
                    .iter()
                    .map(|(_, has_guard)| if *has_guard { 2 } else { 1 })
                    .sum::<usize>();
                let mut items = done.split_off(done.len() - total).into_iter();
                let subject = items.next().expect("subject");
                let mut clauses = Vec::with_capacity(clause_shapes.len());
                for (pattern, has_guard) in clause_shapes {
                    let guard = if has_guard {
                        Some(items.next().expect("guard"))
                    } else {
                        None
                    };
                    let body = items.next().expect("body");
                    clauses.push(WhenClause {
                        pattern,
                        guard,
                        body,
                    });
                }
                done.push(PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                });
            }
            Step::Force => {
                let inner = done.pop().expect("force inner");
                done.push(PseudoExpr::Force(PBox::new(inner)));
            }
            Step::Delay => {
                let inner = done.pop().expect("delay inner");
                done.push(PseudoExpr::Delay(PBox::new(inner)));
            }
            Step::Trace => {
                let value = done.pop().expect("trace value");
                let message = done.pop().expect("trace message");
                done.push(PseudoExpr::Trace {
                    message: PBox::new(message),
                    value: PBox::new(value),
                });
            }
            Step::Lambda { params } => {
                let body = done.pop().expect("lambda body");
                done.push(PseudoExpr::Lambda {
                    params,
                    body: PBox::new(body),
                });
            }
            Step::RecFn { name, params } => {
                let body = done.pop().expect("recfn body");
                done.push(PseudoExpr::RecFn {
                    name,
                    params,
                    body: PBox::new(body),
                });
            }
            Step::BinOp { op } => {
                let right = done.pop().expect("binop right");
                let left = done.pop().expect("binop left");
                done.push(PseudoExpr::BinOp {
                    op,
                    left: PBox::new(left),
                    right: PBox::new(right),
                });
            }
            Step::UnOp { op } => {
                let operand = done.pop().expect("unop operand");
                done.push(PseudoExpr::UnOp {
                    op,
                    operand: PBox::new(operand),
                });
            }
            Step::Constr {
                tag,
                shape,
                type_hint,
                count,
            } => {
                let fields = done.split_off(done.len() - count);
                done.push(PseudoExpr::Constr {
                    type_hint,
                    tag,
                    fields: fields.into(),
                    shape,
                });
            }
            Step::BuiltinCall { name, argc } => {
                let args = done.split_off(done.len() - argc);
                done.push(PseudoExpr::BuiltinCall {
                    name,
                    args: args.into(),
                });
            }
            Step::List { count, has_tail } => {
                let mut items = done.split_off(done.len() - (count + has_tail as usize));
                let tail = if has_tail {
                    Some(PBox::new(items.pop().expect("list tail")))
                } else {
                    None
                };
                done.push(PseudoExpr::List {
                    elements: items.into(),
                    tail,
                });
            }
            Step::Tuple { count } => {
                let elements = done.split_off(done.len() - count);
                done.push(PseudoExpr::Tuple(elements.into()));
            }
            Step::Pair => {
                let b = done.pop().expect("pair second");
                let a = done.pop().expect("pair first");
                done.push(PseudoExpr::Pair(PBox::new(a), PBox::new(b)));
            }
            Step::FieldAccess { selector } => {
                let record = done.pop().expect("field access record");
                done.push(PseudoExpr::FieldAccess {
                    record: PBox::new(record),
                    selector,
                });
            }
            Step::IndexAccess { index } => {
                let collection = done.pop().expect("index access collection");
                done.push(PseudoExpr::IndexAccess {
                    collection: PBox::new(collection),
                    index,
                });
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "the step machine must leave one result");
    done.pop().expect("recurse result")
}

fn try_decode_pair(expr: PseudoExpr) -> PseudoExpr {
    let PseudoExpr::Apply { function, args } = &expr else {
        return expr;
    };
    if args.len() != 2 {
        return expr;
    }
    let PseudoExpr::Lambda { params, body } = function.as_ref() else {
        return expr;
    };
    if params.len() != 3 {
        return expr;
    }
    let PseudoExpr::Apply {
        function: body_fn,
        args: body_args,
    } = body.as_ref()
    else {
        return expr;
    };
    if body_args.len() != 2 {
        return expr;
    }
    // body must be exactly `param2(param0, param1)`.
    if !is_var_with_id(body_fn, params[2].id)
        || !is_var_with_id(&body_args[0], params[0].id)
        || !is_var_with_id(&body_args[1], params[1].id)
    {
        return expr;
    }

    // Match — rebuild as `Pair(arg0, arg1)`.
    let PseudoExpr::Apply { args, .. } = expr else {
        unreachable!("just matched Apply above");
    };
    let mut it = args.into_iter();
    let a = it.next().expect("len checked == 2");
    let b = it.next().expect("len checked == 2");
    PseudoExpr::Pair(PBox::new(a), PBox::new(b))
}

fn is_var_with_id(expr: &PseudoExpr, target: VarId) -> bool {
    matches!(expr, PseudoExpr::Var { id: Some(v), .. } if *v == target)
}

#[cfg(test)]
mod tests;
