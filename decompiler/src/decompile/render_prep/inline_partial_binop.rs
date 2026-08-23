//! Inline a partially-applied binary-operator builtin so the dotted, partial
//! `Int.lt_partial`/`Int.add_partial`/… binding disappears.
//!
//! Lowering turns a fully-applied binary builtin into a `BinOp` (`a < b`), but
//! a partial application stays a `BuiltinCall` — an invalid dotted identifier
//! and an awkward partial call. When such a `let P = <binop-builtin>(a)` is
//! used only as completed applications `P(b)`, rewrite each `P(b)` to the full
//! `a <op> b` and drop the binding:
//!
//!   let Int.lt_partial_2 = Int.lt(to_int_55)   →   (binding dropped)
//!   if Int.lt_partial_2(8) { … }               →   if to_int_55 < 8 { … }
//!
//! Soundness: `binop(a)(b)` is exactly `a <op> b` (same operand order as
//! lowering's full-application rule). `a` is duplicated at each call site, so
//! the pass only fires when `a` is a simple pure value (Var/literal) — free to
//! duplicate, no recomputation, no effect/trace. If `P` is ever used as a bare
//! value (passed to a HOF), it is genuinely partial and left untouched.

use crate::builtins::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::type_hint::TypeHintId;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::children;

/// One `when` in progress for the step machines below: its already-folded
/// subject, the clauses still to fold, and the clauses already rebuilt.
struct WhenBuild {
    subject: PseudoExpr,
    subject_name: Option<Binder>,
    remaining: std::vec::IntoIter<WhenClause>,
    finished: Vec<WhenClause>,
}

pub(super) fn inline_partial_binop(root: PseudoExpr) -> PseudoExpr {
    enum Step {
        Enter(PseudoExpr),
        LetPost {
            name: String,
            id: Option<VarId>,
        },
        Lambda {
            params: Vec<Binder>,
        },
        RecFn {
            name: Binder,
            params: Vec<Binder>,
        },
        Apply {
            argc: usize,
        },
        If,
        WhenSubjectDone {
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        },
        WhenNext(WhenBuild),
        WhenClauseDone {
            build: WhenBuild,
            pattern: WhenPattern,
            has_guard: bool,
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
        Trace,
        Delay,
        Force,
    }

    let mut stack = vec![Step::Enter(root)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = stack.pop() {
        match step {
            Step::Enter(expr) => match expr {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    let eliminable = id.is_some_and(|pid| {
                        partial_binop(&value).is_some()
                            && is_simple_dup(partial_arg(&value))
                            && has_use(&body, pid)
                            && all_uses_completed(&body, pid)
                    });
                    if eliminable {
                        let pid = id.expect("checked by `eliminable`");
                        let (op, arg1) = partial_binop(&value).expect("checked");
                        let arg1 = arg1.clone();
                        let new_body = rewrite_completions(body.into_inner(), pid, op, &arg1);
                        stack.push(Step::Enter(new_body));
                    } else {
                        stack.push(Step::LetPost { name, id });
                        stack.push(Step::Enter(body.into_inner()));
                        stack.push(Step::Enter(value.into_inner()));
                    }
                }
                PseudoExpr::Lambda { params, body } => {
                    stack.push(Step::Lambda { params });
                    stack.push(Step::Enter(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    stack.push(Step::RecFn { name, params });
                    stack.push(Step::Enter(body.into_inner()));
                }
                PseudoExpr::Apply { function, args } => {
                    stack.push(Step::Apply { argc: args.len() });
                    for a in args.into_iter().rev() {
                        stack.push(Step::Enter(a));
                    }
                    stack.push(Step::Enter(function.into_inner()));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    stack.push(Step::If);
                    stack.push(Step::Enter(else_branch.into_inner()));
                    stack.push(Step::Enter(then_branch.into_inner()));
                    stack.push(Step::Enter(condition.into_inner()));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    stack.push(Step::WhenSubjectDone {
                        subject_name,
                        clauses,
                    });
                    stack.push(Step::Enter(subject.into_inner()));
                }
                PseudoExpr::BinOp { op, left, right } => {
                    stack.push(Step::BinOp { op });
                    stack.push(Step::Enter(right.into_inner()));
                    stack.push(Step::Enter(left.into_inner()));
                }
                PseudoExpr::UnOp { op, operand } => {
                    stack.push(Step::UnOp { op });
                    stack.push(Step::Enter(operand.into_inner()));
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
                        stack.push(Step::Enter(f));
                    }
                }
                PseudoExpr::BuiltinCall { name, args } => {
                    stack.push(Step::BuiltinCall {
                        name,
                        argc: args.len(),
                    });
                    for a in args.into_iter().rev() {
                        stack.push(Step::Enter(a));
                    }
                }
                PseudoExpr::List { elements, tail } => {
                    stack.push(Step::List {
                        count: elements.len(),
                        has_tail: tail.is_some(),
                    });
                    if let Some(t) = tail {
                        stack.push(Step::Enter(t.into_inner()));
                    }
                    for e in elements.into_iter().rev() {
                        stack.push(Step::Enter(e));
                    }
                }
                PseudoExpr::Tuple(elements) => {
                    stack.push(Step::Tuple {
                        count: elements.len(),
                    });
                    for e in elements.into_iter().rev() {
                        stack.push(Step::Enter(e));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    stack.push(Step::Pair);
                    stack.push(Step::Enter(b.into_inner()));
                    stack.push(Step::Enter(a.into_inner()));
                }
                PseudoExpr::FieldAccess { record, selector } => {
                    stack.push(Step::FieldAccess { selector });
                    stack.push(Step::Enter(record.into_inner()));
                }
                PseudoExpr::IndexAccess { collection, index } => {
                    stack.push(Step::IndexAccess { index });
                    stack.push(Step::Enter(collection.into_inner()));
                }
                PseudoExpr::Trace { message, value } => {
                    stack.push(Step::Trace);
                    stack.push(Step::Enter(value.into_inner()));
                    stack.push(Step::Enter(message.into_inner()));
                }
                PseudoExpr::Delay(inner) => {
                    stack.push(Step::Delay);
                    stack.push(Step::Enter(inner.into_inner()));
                }
                PseudoExpr::Force(inner) => {
                    stack.push(Step::Force);
                    stack.push(Step::Enter(inner.into_inner()));
                }
                // Leaves (Int/ByteArray/String/Bool/Unit/Var/Error/Raw/
                // Data/HelperSymbol): nothing to descend into.
                leaf => done.push(leaf),
            },

            Step::LetPost { name, id } => {
                let body = done.pop().expect("let body");
                let value = done.pop().expect("let value");
                done.push(PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(body),
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
            Step::Apply { argc } => {
                let args = done.split_off(done.len() - argc);
                let function = done.pop().expect("apply function");
                done.push(PseudoExpr::Apply {
                    function: PBox::new(function),
                    args: args.into(),
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
            Step::WhenSubjectDone {
                subject_name,
                clauses,
            } => {
                let subject = done.pop().expect("when subject");
                stack.push(Step::WhenNext(WhenBuild {
                    subject,
                    subject_name,
                    remaining: clauses.into_iter(),
                    finished: Vec::new(),
                }));
            }
            Step::WhenNext(mut build) => match build.remaining.next() {
                None => done.push(PseudoExpr::When {
                    subject: PBox::new(build.subject),
                    subject_name: build.subject_name,
                    clauses: build.finished,
                }),
                Some(WhenClause {
                    pattern,
                    guard,
                    body,
                }) => {
                    let has_guard = guard.is_some();
                    stack.push(Step::WhenClauseDone {
                        build,
                        pattern,
                        has_guard,
                    });
                    stack.push(Step::Enter(body));
                    if let Some(g) = guard {
                        stack.push(Step::Enter(g));
                    }
                }
            },
            Step::WhenClauseDone {
                mut build,
                pattern,
                has_guard,
            } => {
                let body = done.pop().expect("clause body");
                let guard = if has_guard {
                    Some(done.pop().expect("clause guard"))
                } else {
                    None
                };
                build.finished.push(WhenClause {
                    pattern,
                    guard,
                    body,
                });
                stack.push(Step::WhenNext(build));
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
            Step::Trace => {
                let value = done.pop().expect("trace value");
                let message = done.pop().expect("trace message");
                done.push(PseudoExpr::Trace {
                    message: PBox::new(message),
                    value: PBox::new(value),
                });
            }
            Step::Delay => {
                let inner = done.pop().expect("delay inner");
                done.push(PseudoExpr::Delay(PBox::new(inner)));
            }
            Step::Force => {
                let inner = done.pop().expect("force inner");
                done.push(PseudoExpr::Force(PBox::new(inner)));
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "the step machine must leave one result");
    done.pop().expect("inline_partial_binop result")
}

/// `Some((op, arg1))` if `e` is `<binop-builtin>(arg1)` (a single-arg partial of
/// a builtin that lowering maps to `BinOp op`).
fn partial_binop(e: &PseudoExpr) -> Option<(BinaryOp, &PseudoExpr)> {
    if let PseudoExpr::BuiltinCall { name, args } = e {
        if args.len() == 1 {
            return binop_of(*name).map(|op| (op, &args[0]));
        }
    }
    None
}

fn partial_arg(e: &PseudoExpr) -> &PseudoExpr {
    match e {
        PseudoExpr::BuiltinCall { args, .. } if args.len() == 1 => &args[0],
        _ => e,
    }
}

fn binop_of(b: BuiltinId) -> Option<BinaryOp> {
    Some(match b {
        BuiltinId::IntAdd => BinaryOp::Add,
        BuiltinId::IntSub => BinaryOp::Sub,
        BuiltinId::IntMul => BinaryOp::Mul,
        BuiltinId::IntDiv => BinaryOp::Div,
        BuiltinId::IntMod => BinaryOp::Mod,
        BuiltinId::IntEq | BuiltinId::ByteArrayEq => BinaryOp::Eq,
        BuiltinId::IntLt | BuiltinId::ByteArrayLt => BinaryOp::Lt,
        BuiltinId::IntLte | BuiltinId::ByteArrayLte => BinaryOp::Lte,
        BuiltinId::ByteArrayConcat => BinaryOp::Concat,
        _ => return None,
    })
}

/// Simple pure value, cheap to duplicate at each call site.
fn is_simple_dup(e: &PseudoExpr) -> bool {
    matches!(
        e,
        PseudoExpr::Var { .. }
            | PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
    )
}

fn is_var(e: &PseudoExpr, pid: VarId) -> bool {
    matches!(e, PseudoExpr::Var { id: Some(v), .. } if *v == pid)
}

fn has_use(expr: &PseudoExpr, pid: VarId) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if is_var(current, pid) {
            return true;
        }
        pending.extend(children(current));
    }
    false
}

/// Every occurrence of `Var{pid}` is the function of a single-argument `Apply`
/// (a completion `P(b)`) — never a bare function value.
fn all_uses_completed(expr: &PseudoExpr, pid: VarId) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Apply { function, args } if is_var(function, pid) => {
                if args.len() != 1 {
                    return false;
                }
                pending.extend(args.iter());
            }
            PseudoExpr::Var { id: Some(v), .. } if *v == pid => return false, // bare use
            other => pending.extend(children(other)),
        }
    }
    true
}

struct CompletionRewriter<'a> {
    pid: VarId,
    op: BinaryOp,
    arg1: &'a PseudoExpr,
}

impl ExprFolder for CompletionRewriter<'_> {
    fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
        pattern
    }

    fn post_apply(&mut self, function: PseudoExpr, mut args: Vec<PseudoExpr>) -> PseudoExpr {
        if args.len() == 1 && is_var(&function, self.pid) {
            let arg2 = args.pop().expect("len 1");
            return PseudoExpr::BinOp {
                op: self.op,
                left: PBox::new(self.arg1.clone()),
                right: PBox::new(arg2),
            };
        }
        PseudoExpr::Apply {
            function: PBox::new(function),
            args: args.into(),
        }
    }
}

fn rewrite_completions(
    expr: PseudoExpr,
    pid: VarId,
    op: BinaryOp,
    arg1: &PseudoExpr,
) -> PseudoExpr {
    CompletionRewriter { pid, op, arg1 }.fold(expr)
}

#[cfg(test)]
mod tests;
