use std::collections::HashSet;

use crate::decompile::constructor_data::{
    is_bool_false_like, is_standard_option_none_candidate, is_standard_option_some_candidate,
};
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};

fn expr_contains_named_option(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Constr {
                shape:
                    ConstructorShape::Known(KnownConstructor::Some)
                    | ConstructorShape::Known(KnownConstructor::None),
                ..
            } => return true,
            PseudoExpr::Let { value, body, .. } => {
                pending.push(value);
                pending.push(body);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(condition);
                pending.push(then_branch);
                pending.push(else_branch);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                pending.push(subject);
                for clause in clauses {
                    if let Some(guard) = &clause.guard {
                        pending.push(guard);
                    }
                    pending.push(&clause.body);
                }
            }
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args.iter());
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            PseudoExpr::UnOp { operand, .. }
            | PseudoExpr::Delay(operand)
            | PseudoExpr::Force(operand) => pending.push(operand),
            PseudoExpr::Trace { message, value } => {
                pending.push(message);
                pending.push(value);
            }
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter()),
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements.iter());
                if let Some(tail) = tail.as_ref() {
                    pending.push(tail);
                }
            }
            PseudoExpr::Tuple(elements) => pending.extend(elements.iter()),
            PseudoExpr::Pair(first, second) => {
                pending.push(first);
                pending.push(second);
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            _ => {}
        }
    }
    false
}

/// Every return leaf of `body` is a NAMED `Known(Some)` (1 field) or
/// `Known(None)` (0 fields) — with at least one of EACH — or an
/// `Error` (an aborting leaf is Option-neutral). Strictly stronger
/// than `expr_contains_named_option`: admits LAMBDA-valued `let fn`
/// definitions into the option-like set without the contains-check's
/// false-positive surface, where a closure that merely USES an Option
/// internally would relabel its consumers.
fn body_leaves_are_named_option(body: &PseudoExpr) -> bool {
    // This is a universal ("every leaf must qualify") search that also
    // mutates `saw_some`/`saw_none` as it visits, so it isn't a plain
    // existential predicate — but the mutation is safe to reorder: the
    // caller only consults the flags when `walk` returns `true`, and
    // `true` is only reachable if EVERY node was actually visited (both
    // `If` branches, every `When` arm), so the flags end up identical
    // regardless of the order nodes are popped in. On any failing node
    // the answer is `false` immediately, and the flags are never read in
    // that case.
    fn walk(expr: &PseudoExpr, saw_some: &mut bool, saw_none: &mut bool) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Constr {
                    shape: ConstructorShape::Known(KnownConstructor::Some),
                    fields,
                    ..
                } if fields.len() == 1 => {
                    *saw_some = true;
                }
                PseudoExpr::Constr {
                    shape: ConstructorShape::Known(KnownConstructor::None),
                    fields,
                    ..
                } if fields.is_empty() => {
                    *saw_none = true;
                }
                PseudoExpr::Error { .. } => {}
                PseudoExpr::Trace { value, .. } => pending.push(value),
                PseudoExpr::Let { body, .. } => pending.push(body),
                PseudoExpr::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    pending.push(then_branch);
                    pending.push(else_branch);
                }
                PseudoExpr::When { clauses, .. } if !clauses.is_empty() => {
                    pending.extend(clauses.iter().map(|clause| &clause.body));
                }
                _ => return false,
            }
        }
        true
    }
    let (mut saw_some, mut saw_none) = (false, false);
    walk(body, &mut saw_some, &mut saw_none) && saw_some && saw_none
}

/// This is a top-down walk — the `RecFn`/`Let` arms record a name BEFORE
/// descending — so the arms keep their original order and their original
/// child lists (note that a `RecFn` failing its guard is NOT descended
/// into). Children are pushed in REVERSE so they pop in source order.
pub(in crate::decompile::late::normalize) fn collect_option_like_function_names(
    expr: &PseudoExpr,
    names: &mut HashSet<String>,
) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];

    while let Some(expr) = pending.pop() {
        match expr {
            PseudoExpr::RecFn { name, body, .. } if expr_contains_named_option(body) => {
                names.insert(name.name.clone());
                pending.push(body);
            }
            PseudoExpr::Lambda { body, .. } => pending.push(body),
            // A LAMBDA-valued fn definition whose EVERY return leaf is a
            // named Some/None is an Option producer; without this arm the
            // expect-destructure consumers of a plain (non-rec) `fn` stay
            // raw (`expect Unknown_E_1_0(payload) = f_11(...)`).
            PseudoExpr::Let {
                name, value, body, ..
            } if matches!(
                value.as_ref(),
                PseudoExpr::Lambda { body, .. } if body_leaves_are_named_option(body)
            ) =>
            {
                names.insert(name.clone());
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
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
                for clause in clauses.iter().rev() {
                    pending.push(&clause.body);
                    if let Some(guard) = &clause.guard {
                        pending.push(guard);
                    }
                }
                pending.push(subject);
            }
            PseudoExpr::Apply { function, args } => {
                for arg in args.iter().rev() {
                    pending.push(arg);
                }
                pending.push(function);
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
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args.iter().rev() {
                    pending.push(arg);
                }
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(tail) = tail {
                    pending.push(tail);
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
            PseudoExpr::Pair(first, second) => {
                pending.push(second);
                pending.push(first);
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            _ => {}
        }
    }
}

/// One job on [`is_option_like_value`]'s stack. `Post` holds everything the
/// arm needs that is NOT a child answer — the non-recursive `None`-shape
/// probes run on the way down.
enum OptStep<'a> {
    Visit(&'a PseudoExpr),
    Post(OptPost),
}

enum OptPost {
    /// `value_answer || body_answer`.
    Let,
    /// The two branch answers plus each branch's `None`-shape probe.
    If {
        then_none_like: bool,
        else_none_like: bool,
    },
    /// `has_none` is decided without recursion; the clause bodies supply
    /// `has_option_branch`.
    When { has_none: bool, clause_count: usize },
}

/// A bottom-up boolean fold: each node's answer is combined from its
/// children's answers, popped off `answers` in the order the children were
/// pushed (REVERSE, so they pop in source order). The arms keep their
/// original order — the two `other if …` probes still shadow `Let`/`If`/
/// `When` — and every combinator is a side-effect-free `||`/`&&` over pure
/// predicates, so evaluating both operands instead of short-circuiting
/// changes nothing but the work done (strictly less here: the recursive
/// `If` arm re-evaluated each branch twice).
pub(in crate::decompile::late::normalize) fn is_option_like_value(
    expr: &PseudoExpr,
    option_like_functions: &HashSet<String>,
    option_like_vars: &[HashSet<String>],
) -> bool {
    let mut steps: Vec<OptStep<'_>> = vec![OptStep::Visit(expr)];
    let mut answers: Vec<bool> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            OptStep::Visit(expr) => match expr {
                PseudoExpr::Constr {
                    shape:
                        ConstructorShape::Known(KnownConstructor::Some)
                        | ConstructorShape::Known(KnownConstructor::None),
                    ..
                } => answers.push(true),
                other if is_standard_option_none_candidate(other) || is_bool_false_like(other) => {
                    answers.push(true)
                }
                other if is_standard_option_some_candidate(other) => answers.push(true),
                PseudoExpr::Var { name, .. } => answers.push(
                    option_like_vars
                        .iter()
                        .rev()
                        .any(|scope| scope.contains(name)),
                ),
                PseudoExpr::Apply { function, .. } => answers.push(match function.as_ref() {
                    PseudoExpr::Var { name, .. } => option_like_functions.contains(name),
                    PseudoExpr::RecFn { name, .. } => {
                        option_like_functions.contains(name.name.as_str())
                    }
                    _ => false,
                }),
                PseudoExpr::Let { value, body, .. } => {
                    steps.push(OptStep::Post(OptPost::Let));
                    steps.push(OptStep::Visit(body));
                    steps.push(OptStep::Visit(value));
                }
                PseudoExpr::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    steps.push(OptStep::Post(OptPost::If {
                        then_none_like: is_standard_option_none_candidate(then_branch)
                            || is_bool_false_like(then_branch),
                        else_none_like: is_standard_option_none_candidate(else_branch)
                            || is_bool_false_like(else_branch),
                    }));
                    steps.push(OptStep::Visit(else_branch));
                    steps.push(OptStep::Visit(then_branch));
                }
                PseudoExpr::When { clauses, .. } => {
                    let has_none = clauses.iter().any(|clause| {
                        is_standard_option_none_candidate(&clause.body)
                            || is_bool_false_like(&clause.body)
                    });
                    steps.push(OptStep::Post(OptPost::When {
                        has_none,
                        clause_count: clauses.len(),
                    }));
                    for clause in clauses.iter().rev() {
                        steps.push(OptStep::Visit(&clause.body));
                    }
                }
                _ => answers.push(false),
            },
            OptStep::Post(post) => {
                let answer = match post {
                    OptPost::Let => {
                        let body = answers.pop().expect("let body answer");
                        let value = answers.pop().expect("let value answer");
                        value || body
                    }
                    OptPost::If {
                        then_none_like,
                        else_none_like,
                    } => {
                        let else_branch = answers.pop().expect("if else answer");
                        let then_branch = answers.pop().expect("if then answer");
                        let has_none =
                            then_branch && then_none_like || else_branch && else_none_like;
                        let has_option_branch = then_branch || else_branch;
                        has_none && has_option_branch
                    }
                    OptPost::When {
                        has_none,
                        clause_count,
                    } => {
                        let at = answers.len() - clause_count;
                        let has_option_branch = answers.split_off(at).into_iter().any(|a| a);
                        has_none && has_option_branch
                    }
                };
                answers.push(answer);
            }
        }
    }

    answers
        .pop()
        .expect("is_option_like_value leaves one answer")
}
