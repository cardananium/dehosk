//! Dead-let elimination over `NamelessExpr`.
//!
//! Liveness is **pure VarId-count**: a nameless `Var` carries
//! no name, so the textual-name fallback for refs whose id
//! mismatches their binder is neither possible nor needed —
//! that mismatch cannot occur here.
//!
//! A let whose value is `Apply` / `Force` / `Trace`, or that
//! contains an explicit `Error`, is preserved even when unused.

use std::collections::HashMap;

use crate::pseudo::nameless::{NamelessClause, NamelessExpr};
use crate::pseudo::var_id::VarId;

/// Drop Let bindings whose `binder` is unused in the body and
/// whose value has no observable side effect.
pub(crate) fn eliminate_dead_lets_nameless(expr: NamelessExpr) -> NamelessExpr {
    // Count uses once, not per Let: cheaper on large ASTs.
    let mut counts: HashMap<VarId, usize> = HashMap::new();
    count_uses(&expr, &mut counts);
    fold(expr, &counts)
}

fn count_uses(expr: &NamelessExpr, out: &mut HashMap<VarId, usize>) {
    use crate::pseudo::nameless::fold::NamelessVisitor;

    struct UseCounter<'a> {
        out: &'a mut HashMap<VarId, usize>,
    }

    impl NamelessVisitor for UseCounter<'_> {
        fn visit_var(&mut self, id: VarId) {
            *self.out.entry(id).or_insert(0) += 1;
        }
    }

    UseCounter { out }.walk(expr);
}

/// Conservative side-effect detection. A let whose value matches
/// any of these is preserved even with use-count 0.
pub(super) fn has_observable_effect(value: &NamelessExpr) -> bool {
    // Floor: any top-level Apply/Force/Trace/Error is preserved.
    if matches!(
        value,
        NamelessExpr::Apply { .. }
            | NamelessExpr::Force(_)
            | NamelessExpr::Trace { .. }
            | NamelessExpr::Error { .. }
    ) {
        return true;
    }
    // Also retain a strict-evaluation FAILPOINT at ANY nesting depth — an
    // Error, or a non-builtin call/force in strict position inside a
    // Constr/Pair/Tuple/List field, a BuiltinCall argument, or an inner Let
    // chain. `contains_explicit_error` additionally preserves a nested Trace
    // (observable log side effect).
    nameless_contains_strict_failpoint(value) || contains_explicit_error(value)
}

/// Nameless mirror of `Simplifier::contains_strict_failpoint`
/// (decompiler/src/decompile/simplify/helpers/effects.rs): true when strict
/// evaluation of `expr` can FAIL — a literal Error, or a non-builtin call /
/// forced opaque thunk in strict position. Builtin partiality is NOT judged
/// (a builtin-headed apply recurses into its operands only). Anything the
/// simplify gate retains must be retained here, or this pass re-drops it.
fn nameless_contains_strict_failpoint(expr: &NamelessExpr) -> bool {
    let mut pending: Vec<&NamelessExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            NamelessExpr::Error { .. } => return true,
            NamelessExpr::Apply { function, args } => {
                if !nameless_apply_head_is_builtin(function) {
                    return true;
                }
                for a in args.iter().rev() {
                    pending.push(a);
                }
                pending.push(function);
            }
            NamelessExpr::Force(inner) => match inner.as_ref() {
                NamelessExpr::Delay(body) => pending.push(body),
                _ if nameless_apply_head_is_builtin(inner) => pending.push(inner),
                _ => return true,
            },
            NamelessExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            NamelessExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
            NamelessExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
                pending.push(condition);
            }
            NamelessExpr::When {
                subject, clauses, ..
            } => {
                for c in clauses.iter().rev() {
                    pending.push(&c.body);
                }
                pending.push(subject);
            }
            NamelessExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            NamelessExpr::UnOp { operand, .. } => pending.push(operand),
            NamelessExpr::FieldAccess { record, .. } => pending.push(record),
            NamelessExpr::IndexAccess { collection, .. } => pending.push(collection),
            // Suspended: only runs when forced/called.
            NamelessExpr::Delay(_) | NamelessExpr::Lambda { .. } | NamelessExpr::RecFn { .. } => {}
            NamelessExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    pending.push(f);
                }
            }
            NamelessExpr::Tuple(items) => {
                for i in items.iter().rev() {
                    pending.push(i);
                }
            }
            NamelessExpr::Pair(a, b) => {
                pending.push(b);
                pending.push(a);
            }
            NamelessExpr::List { elements, tail } => {
                if let Some(t) = tail.as_deref() {
                    pending.push(t);
                }
                for e in elements.iter().rev() {
                    pending.push(e);
                }
            }
            NamelessExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
            }
            // Raw is opaque undecompiled UPLC — retain on doubt.
            NamelessExpr::Raw { .. } => return true,
            NamelessExpr::Var(_)
            | NamelessExpr::Bool(_)
            | NamelessExpr::Int(_)
            | NamelessExpr::ByteArray(_)
            | NamelessExpr::String(_)
            | NamelessExpr::Unit
            | NamelessExpr::Data(_)
            | NamelessExpr::HelperSymbol(_) => {}
        }
    }
    false
}

/// Nameless mirror of `Simplifier::apply_head_is_builtin`. True iff the head
/// of an apply-spine resolves to a `BuiltinCall` (peeling the curried Apply
/// spine and any Force wrappers; Delay is NOT peeled).
fn nameless_apply_head_is_builtin(function: &NamelessExpr) -> bool {
    let mut current = function;
    loop {
        match current {
            NamelessExpr::BuiltinCall { .. } => return true,
            NamelessExpr::Force(inner) => current = inner,
            NamelessExpr::Apply { function, .. } => current = function,
            _ => return false,
        }
    }
}

fn contains_explicit_error(expr: &NamelessExpr) -> bool {
    use crate::pseudo::nameless::fold::{NamelessVisitor, VisitAction};

    struct ErrorScanner {
        found: bool,
    }
    impl NamelessVisitor for ErrorScanner {
        fn visit_expr(&mut self, expr: &NamelessExpr) -> VisitAction {
            if self.found {
                return VisitAction::Skip;
            }
            match expr {
                // Trace emits a log entry, Error aborts — dropping the
                // surrounding let would lose observable behavior.
                NamelessExpr::Error { .. } | NamelessExpr::Trace { .. } => {
                    self.found = true;
                    VisitAction::Skip
                }
                // Lambda / RecFn / Delay are deferred — an Error or
                // Trace inside them is not an observable effect of
                // the surrounding let value.
                NamelessExpr::Lambda { .. }
                | NamelessExpr::RecFn { .. }
                | NamelessExpr::Delay(_) => VisitAction::Skip,
                _ => VisitAction::Walk,
            }
        }
    }

    let mut scanner = ErrorScanner { found: false };
    scanner.walk(expr);
    scanner.found
}

fn fold(expr: NamelessExpr, counts: &HashMap<VarId, usize>) -> NamelessExpr {
    use crate::pseudo::ast::{BinaryOp, UnaryOp};
    use crate::pseudo::constructor::ConstructorShape;
    use crate::pseudo::field_selector::FieldSelector;
    use crate::pseudo::nameless::NamelessPattern;
    use crate::pseudo::type_hint::TypeHintId;

    enum Step {
        Enter(NamelessExpr),
        Post(Post),
    }

    enum Post {
        Lambda {
            params: Vec<VarId>,
        },
        RecFn {
            name: VarId,
            params: Vec<VarId>,
        },
        Apply {
            argc: usize,
        },
        Let {
            binder: VarId,
        },
        If,
        /// `(pattern, has_guard)` per clause, in original clause order.
        When {
            subject_name: Option<VarId>,
            clause_meta: Vec<(NamelessPattern, bool)>,
        },
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
        BuiltinCall {
            name: crate::BuiltinId,
            argc: usize,
        },
        Delay,
        Force,
        Trace,
    }

    fn take(done: &mut Vec<NamelessExpr>, n: usize) -> Vec<NamelessExpr> {
        let at = done.len() - n;
        done.split_off(at)
    }

    let mut steps: Vec<Step> = vec![Step::Enter(expr)];
    let mut done: Vec<NamelessExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(expr) => match expr {
                NamelessExpr::Lambda { params, body } => {
                    steps.push(Step::Post(Post::Lambda { params }));
                    steps.push(Step::Enter(*body));
                }
                NamelessExpr::RecFn { name, params, body } => {
                    steps.push(Step::Post(Post::RecFn { name, params }));
                    steps.push(Step::Enter(*body));
                }
                NamelessExpr::Apply { function, args } => {
                    steps.push(Step::Post(Post::Apply { argc: args.len() }));
                    for a in args.into_iter().rev() {
                        steps.push(Step::Enter(a));
                    }
                    steps.push(Step::Enter(*function));
                }
                NamelessExpr::Let {
                    binder,
                    value,
                    body,
                } => {
                    // The value must be folded before the body — see the
                    // function-level comment.
                    steps.push(Step::Post(Post::Let { binder }));
                    steps.push(Step::Enter(*body));
                    steps.push(Step::Enter(*value));
                }
                NamelessExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(Step::Post(Post::If));
                    steps.push(Step::Enter(*else_branch));
                    steps.push(Step::Enter(*then_branch));
                    steps.push(Step::Enter(*condition));
                }
                NamelessExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let clause_meta = clauses
                        .iter()
                        .map(|c| (c.pattern.clone(), c.guard.is_some()))
                        .collect();
                    steps.push(Step::Post(Post::When {
                        subject_name,
                        clause_meta,
                    }));
                    for c in clauses.into_iter().rev() {
                        steps.push(Step::Enter(c.body));
                        if let Some(g) = c.guard {
                            steps.push(Step::Enter(g));
                        }
                    }
                    steps.push(Step::Enter(*subject));
                }
                NamelessExpr::List { elements, tail } => {
                    steps.push(Step::Post(Post::List {
                        count: elements.len(),
                        has_tail: tail.is_some(),
                    }));
                    if let Some(t) = tail {
                        steps.push(Step::Enter(*t));
                    }
                    for e in elements.into_iter().rev() {
                        steps.push(Step::Enter(e));
                    }
                }
                NamelessExpr::Tuple(items) => {
                    steps.push(Step::Post(Post::Tuple { count: items.len() }));
                    for i in items.into_iter().rev() {
                        steps.push(Step::Enter(i));
                    }
                }
                NamelessExpr::Pair(a, b) => {
                    steps.push(Step::Post(Post::Pair));
                    steps.push(Step::Enter(*b));
                    steps.push(Step::Enter(*a));
                }
                NamelessExpr::Constr {
                    type_hint,
                    tag,
                    fields,
                    shape,
                } => {
                    steps.push(Step::Post(Post::Constr {
                        type_hint,
                        tag,
                        count: fields.len(),
                        shape,
                    }));
                    for f in fields.into_iter().rev() {
                        steps.push(Step::Enter(f));
                    }
                }
                NamelessExpr::FieldAccess { record, selector } => {
                    steps.push(Step::Post(Post::FieldAccess { selector }));
                    steps.push(Step::Enter(*record));
                }
                NamelessExpr::IndexAccess { collection, index } => {
                    steps.push(Step::Post(Post::IndexAccess { index }));
                    steps.push(Step::Enter(*collection));
                }
                NamelessExpr::BinOp { op, left, right } => {
                    steps.push(Step::Post(Post::BinOp { op }));
                    steps.push(Step::Enter(*right));
                    steps.push(Step::Enter(*left));
                }
                NamelessExpr::UnOp { op, operand } => {
                    steps.push(Step::Post(Post::UnOp { op }));
                    steps.push(Step::Enter(*operand));
                }
                NamelessExpr::BuiltinCall { name, args } => {
                    steps.push(Step::Post(Post::BuiltinCall {
                        name,
                        argc: args.len(),
                    }));
                    for a in args.into_iter().rev() {
                        steps.push(Step::Enter(a));
                    }
                }
                NamelessExpr::Delay(inner) => {
                    steps.push(Step::Post(Post::Delay));
                    steps.push(Step::Enter(*inner));
                }
                NamelessExpr::Force(inner) => {
                    steps.push(Step::Post(Post::Force));
                    steps.push(Step::Enter(*inner));
                }
                NamelessExpr::Trace { message, value } => {
                    steps.push(Step::Post(Post::Trace));
                    steps.push(Step::Enter(*value));
                    steps.push(Step::Enter(*message));
                }
                other => done.push(other),
            },
            Step::Post(post) => {
                let rebuilt = match post {
                    Post::Lambda { params } => {
                        let body = done.pop().expect("lambda body");
                        NamelessExpr::Lambda {
                            params,
                            body: Box::new(body),
                        }
                    }
                    Post::RecFn { name, params } => {
                        let body = done.pop().expect("recfn body");
                        NamelessExpr::RecFn {
                            name,
                            params,
                            body: Box::new(body),
                        }
                    }
                    Post::Apply { argc } => {
                        let args = take(&mut done, argc);
                        let function = done.pop().expect("apply function");
                        NamelessExpr::Apply {
                            function: Box::new(function),
                            args,
                        }
                    }
                    Post::Let { binder } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        let used = counts.get(&binder).copied().unwrap_or(0) > 0;
                        if !used && !has_observable_effect(&value) {
                            body
                        } else {
                            NamelessExpr::Let {
                                binder,
                                value: Box::new(value),
                                body: Box::new(body),
                            }
                        }
                    }
                    Post::If => {
                        let else_branch = done.pop().expect("if else");
                        let then_branch = done.pop().expect("if then");
                        let condition = done.pop().expect("if condition");
                        NamelessExpr::If {
                            condition: Box::new(condition),
                            then_branch: Box::new(then_branch),
                            else_branch: Box::new(else_branch),
                        }
                    }
                    Post::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let total: usize = clause_meta
                            .iter()
                            .map(|(_, has_guard)| if *has_guard { 2 } else { 1 })
                            .sum();
                        let mut items = take(&mut done, total).into_iter();
                        let mut clauses = Vec::with_capacity(clause_meta.len());
                        for (pattern, has_guard) in clause_meta {
                            let guard = if has_guard {
                                Some(items.next().expect("clause guard"))
                            } else {
                                None
                            };
                            let body = items.next().expect("clause body");
                            clauses.push(NamelessClause {
                                pattern,
                                guard,
                                body,
                            });
                        }
                        let subject = done.pop().expect("when subject");
                        NamelessExpr::When {
                            subject: Box::new(subject),
                            subject_name,
                            clauses,
                        }
                    }
                    Post::List { count, has_tail } => {
                        let tail = if has_tail { done.pop() } else { None };
                        let elements = take(&mut done, count);
                        NamelessExpr::List {
                            elements,
                            tail: tail.map(Box::new),
                        }
                    }
                    Post::Tuple { count } => NamelessExpr::Tuple(take(&mut done, count)),
                    Post::Pair => {
                        let second = done.pop().expect("pair second");
                        let first = done.pop().expect("pair first");
                        NamelessExpr::Pair(Box::new(first), Box::new(second))
                    }
                    Post::Constr {
                        type_hint,
                        tag,
                        count,
                        shape,
                    } => {
                        let fields = take(&mut done, count);
                        NamelessExpr::Constr {
                            type_hint,
                            tag,
                            fields,
                            shape,
                        }
                    }
                    Post::FieldAccess { selector } => {
                        let record = done.pop().expect("field access record");
                        NamelessExpr::FieldAccess {
                            record: Box::new(record),
                            selector,
                        }
                    }
                    Post::IndexAccess { index } => {
                        let collection = done.pop().expect("index access collection");
                        NamelessExpr::IndexAccess {
                            collection: Box::new(collection),
                            index,
                        }
                    }
                    Post::BinOp { op } => {
                        let right = done.pop().expect("binop right");
                        let left = done.pop().expect("binop left");
                        NamelessExpr::BinOp {
                            op,
                            left: Box::new(left),
                            right: Box::new(right),
                        }
                    }
                    Post::UnOp { op } => {
                        let operand = done.pop().expect("unop operand");
                        NamelessExpr::UnOp {
                            op,
                            operand: Box::new(operand),
                        }
                    }
                    Post::BuiltinCall { name, argc } => {
                        let args = take(&mut done, argc);
                        NamelessExpr::BuiltinCall { name, args }
                    }
                    Post::Delay => {
                        let inner = done.pop().expect("delay inner");
                        NamelessExpr::Delay(Box::new(inner))
                    }
                    Post::Force => {
                        let inner = done.pop().expect("force inner");
                        NamelessExpr::Force(Box::new(inner))
                    }
                    Post::Trace => {
                        let value = done.pop().expect("trace value");
                        let message = done.pop().expect("trace message");
                        NamelessExpr::Trace {
                            message: Box::new(message),
                            value: Box::new(value),
                        }
                    }
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "the fold machine must leave one result");
    done.pop().expect("fold result")
}

#[cfg(test)]
mod tests;
