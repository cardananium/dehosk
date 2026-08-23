use crate::builtins::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::type_hint::TypeHintId;
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

use super::shadowing::pattern_has_matching_binder;

/// Replace `force(x)` with `x` for every reference matching
/// `name`/`target_id`, skipping scopes where a binder shadows it.
pub(super) fn strip_force_on_var(
    expr: PseudoExpr,
    name: &str,
    target_id: Option<VarId>,
) -> PseudoExpr {
    let matches_target = |n: &str, id: Option<VarId>| {
        crate::decompile::var_match::refs_match(n, id, name, target_id)
    };
    let binder_blocks_target = |b: &Binder| matches_target(b.as_str(), b.id.get());
    let pattern_blocks_target =
        |p: &WhenPattern| pattern_has_matching_binder(p, |b| binder_blocks_target(b));
    let when_clause_blocks_target = |subject_name: Option<&Binder>, pattern: &WhenPattern| {
        subject_name.is_some_and(|sn| binder_blocks_target(sn)) || pattern_blocks_target(pattern)
    };

    /// One `when` in progress: its (already-folded) subject, the clauses
    /// still to process, and the clauses already rebuilt.
    struct WhenBuild {
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        remaining: std::vec::IntoIter<WhenClause>,
        finished: Vec<WhenClause>,
    }

    enum Step {
        Enter(PseudoExpr),
        Force,
        LetBody {
            name: String,
            id: Option<VarId>,
            body: PBox,
        },
        LetPost {
            name: String,
            id: Option<VarId>,
            value: PseudoExpr,
            blocks: bool,
        },
        Lambda {
            params: Vec<Binder>,
            blocks: bool,
        },
        RecFn {
            name: Binder,
            params: Vec<Binder>,
            blocks: bool,
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
        WhenLiteralPatternDone {
            build: WhenBuild,
            guard: Option<PseudoExpr>,
            body: PseudoExpr,
        },
        WhenClauseDone {
            build: WhenBuild,
            pattern: WhenPattern,
            blocks: bool,
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
    }

    fn push_guard_then_body(stack: &mut Vec<Step>, guard: Option<PseudoExpr>, body: PseudoExpr) {
        stack.push(Step::Enter(body));
        if let Some(g) = guard {
            stack.push(Step::Enter(g));
        }
    }

    let mut stack = vec![Step::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();
    let mut blocked_depth: usize = 0;

    while let Some(step) = stack.pop() {
        match step {
            Step::Enter(expr) => {
                // Once inside a scope where a binder shadows the target,
                // the whole subtree is left untouched — no need to walk
                // into it at all, and (unlike the borrowed `&PseudoExpr`
                // the original `pre_expr` saw) we already own it, so no
                // clone is needed either.
                if blocked_depth > 0 {
                    done.push(expr);
                    continue;
                }

                if let PseudoExpr::Force(inner) = expr {
                    let is_target_var = matches!(
                        inner.as_ref(),
                        PseudoExpr::Var { name, id, .. } if matches_target(name, id.get())
                    );
                    if is_target_var {
                        done.push(inner.into_inner());
                    } else {
                        stack.push(Step::Force);
                        stack.push(Step::Enter(inner.into_inner()));
                    }
                    continue;
                }

                match expr {
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
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        stack.push(Step::LetBody { name, id, body });
                        stack.push(Step::Enter(value.into_inner()));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        let blocks = params.iter().any(|p| binder_blocks_target(p));
                        if blocks {
                            blocked_depth += 1;
                        }
                        stack.push(Step::Lambda { params, blocks });
                        stack.push(Step::Enter(body.into_inner()));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let blocks = binder_blocks_target(&name)
                            || params.iter().any(|p| binder_blocks_target(p));
                        if blocks {
                            blocked_depth += 1;
                        }
                        stack.push(Step::RecFn {
                            name,
                            params,
                            blocks,
                        });
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
                    // Leaves (Int/ByteArray/String/Bool/Unit/Var/Error/Raw/
                    // Data/HelperSymbol) and the already-handled `Force`:
                    // nothing further to do.
                    leaf => done.push(leaf),
                }
            }

            Step::Force => {
                let inner = done.pop().expect("force inner");
                done.push(PseudoExpr::Force(PBox::new(inner)));
            }
            Step::LetBody { name, id, body } => {
                let value = done.pop().expect("let value");
                // The binding comes into scope BETWEEN the value and the
                // body, so whether it blocks the target is decided here —
                // between the two children — not before or after both.
                let blocks = matches_target(&name, id.get());
                if blocks {
                    blocked_depth += 1;
                }
                stack.push(Step::LetPost {
                    name,
                    id,
                    value,
                    blocks,
                });
                stack.push(Step::Enter(body.into_inner()));
            }
            Step::LetPost {
                name,
                id,
                value,
                blocks,
            } => {
                let body = done.pop().expect("let body");
                if blocks {
                    blocked_depth -= 1;
                }
                done.push(PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(body),
                });
            }
            Step::Lambda { params, blocks } => {
                let body = done.pop().expect("lambda body");
                if blocks {
                    blocked_depth -= 1;
                }
                done.push(PseudoExpr::Lambda {
                    params,
                    body: PBox::new(body),
                });
            }
            Step::RecFn {
                name,
                params,
                blocks,
            } => {
                let body = done.pop().expect("recfn body");
                if blocks {
                    blocked_depth -= 1;
                }
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
                    pattern: WhenPattern::Literal(inner),
                    guard,
                    body,
                }) => {
                    // Only `Literal` patterns carry a sub-expression; it is
                    // folded (under the AMBIENT depth — this clause's own
                    // shadowing, if any, isn't known until the pattern is)
                    // before `blocks` is decided.
                    stack.push(Step::WhenLiteralPatternDone { build, guard, body });
                    stack.push(Step::Enter(inner));
                }
                Some(WhenClause {
                    pattern,
                    guard,
                    body,
                }) => {
                    let blocks = when_clause_blocks_target(build.subject_name.as_ref(), &pattern);
                    if blocks {
                        blocked_depth += 1;
                    }
                    let has_guard = guard.is_some();
                    stack.push(Step::WhenClauseDone {
                        build,
                        pattern,
                        blocks,
                        has_guard,
                    });
                    push_guard_then_body(&mut stack, guard, body);
                }
            },
            Step::WhenLiteralPatternDone { build, guard, body } => {
                let folded_inner = done.pop().expect("literal pattern inner");
                let pattern = WhenPattern::Literal(folded_inner);
                let blocks = when_clause_blocks_target(build.subject_name.as_ref(), &pattern);
                if blocks {
                    blocked_depth += 1;
                }
                let has_guard = guard.is_some();
                stack.push(Step::WhenClauseDone {
                    build,
                    pattern,
                    blocks,
                    has_guard,
                });
                push_guard_then_body(&mut stack, guard, body);
            }
            Step::WhenClauseDone {
                mut build,
                pattern,
                blocks,
                has_guard,
            } => {
                let body = done.pop().expect("clause body");
                let guard = if has_guard {
                    Some(done.pop().expect("clause guard"))
                } else {
                    None
                };
                if blocks {
                    blocked_depth -= 1;
                }
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
        }
    }

    debug_assert_eq!(done.len(), 1, "the step machine must leave one result");
    done.pop().expect("strip_force_on_var result")
}
