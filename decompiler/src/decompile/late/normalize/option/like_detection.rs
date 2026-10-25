use std::collections::HashSet;

use crate::decompile::constructor_data::{
    is_bool_false_like, is_standard_option_none_candidate, is_standard_option_some_candidate,
};
use crate::pseudo::ast::{PseudoExpr, WhenClause};
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

/// How many option-like scopes a value needs to be option-like, counted from
/// the outermost: it is option-like under a scope stack of length `k` exactly
/// when the need is `Some(t)` with `t <= k`. `Some(0)` means always, `None`
/// never. A scope only ever turns a `Var`'s answer on, and every combinator
/// below is an `||`/`&&` over those answers, so one threshold answers every
/// prefix of the stack — which lets a walk that pushes and pops scopes compute
/// each node's answer once, bottom-up, and ask it at any ancestor.
pub(in crate::decompile::late::normalize) type OptionLikeNeed = Option<usize>;

/// Whether a value with this need is option-like under `scopes` scopes.
pub(in crate::decompile::late::normalize) fn need_holds(
    need: OptionLikeNeed,
    scopes: usize,
) -> bool {
    need.is_some_and(|threshold| threshold <= scopes)
}

/// `a || b`.
fn either(a: OptionLikeNeed, b: OptionLikeNeed) -> OptionLikeNeed {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, None) => a,
        (None, b) => b,
    }
}

/// `a && b`.
fn both(a: OptionLikeNeed, b: OptionLikeNeed) -> OptionLikeNeed {
    Some(a?.max(b?))
}

/// One node of the option-like fold: either answered on its own, or the
/// children whose answers it combines.
pub(in crate::decompile::late::normalize) enum OptionLikeNode<'a> {
    Leaf(OptionLikeNeed),
    /// `value || body`.
    Let {
        value: &'a PseudoExpr,
        body: &'a PseudoExpr,
    },
    /// The two branch answers plus each branch's `None`-shape probe.
    If {
        then_branch: &'a PseudoExpr,
        else_branch: &'a PseudoExpr,
        then_none_like: bool,
        else_none_like: bool,
    },
    /// `has_none` is decided on the spot; the clause bodies supply
    /// `has_option_branch`.
    When {
        has_none: bool,
        clauses: &'a [WhenClause],
    },
}

/// Classify one node. The arms keep their original order — the two `other if
/// …` probes still shadow `Let`/`If`/`When`. A `Var` needs the outermost scope
/// that holds its name.
pub(in crate::decompile::late::normalize) fn option_like_node<'a>(
    expr: &'a PseudoExpr,
    option_like_functions: &HashSet<String>,
    option_like_vars: &[HashSet<String>],
) -> OptionLikeNode<'a> {
    match expr {
        PseudoExpr::Constr {
            shape:
                ConstructorShape::Known(KnownConstructor::Some)
                | ConstructorShape::Known(KnownConstructor::None),
            ..
        } => OptionLikeNode::Leaf(Some(0)),
        other if is_standard_option_none_candidate(other) || is_bool_false_like(other) => {
            OptionLikeNode::Leaf(Some(0))
        }
        other if is_standard_option_some_candidate(other) => OptionLikeNode::Leaf(Some(0)),
        PseudoExpr::Var { name, .. } => OptionLikeNode::Leaf(
            option_like_vars
                .iter()
                .position(|scope| scope.contains(name))
                .map(|outermost| outermost + 1),
        ),
        PseudoExpr::Apply { function, .. } => {
            let option_like = match function.as_ref() {
                PseudoExpr::Var { name, .. } => option_like_functions.contains(name),
                PseudoExpr::RecFn { name, .. } => {
                    option_like_functions.contains(name.name.as_str())
                }
                _ => false,
            };
            OptionLikeNode::Leaf(option_like.then_some(0))
        }
        PseudoExpr::Let { value, body, .. } => OptionLikeNode::Let { value, body },
        PseudoExpr::If {
            then_branch,
            else_branch,
            ..
        } => OptionLikeNode::If {
            then_branch,
            else_branch,
            then_none_like: is_standard_option_none_candidate(then_branch)
                || is_bool_false_like(then_branch),
            else_none_like: is_standard_option_none_candidate(else_branch)
                || is_bool_false_like(else_branch),
        },
        PseudoExpr::When { clauses, .. } => OptionLikeNode::When {
            has_none: clauses.iter().any(|clause| {
                is_standard_option_none_candidate(&clause.body) || is_bool_false_like(&clause.body)
            }),
            clauses,
        },
        _ => OptionLikeNode::Leaf(None),
    }
}

pub(in crate::decompile::late::normalize) fn let_need(
    value: OptionLikeNeed,
    body: OptionLikeNeed,
) -> OptionLikeNeed {
    either(value, body)
}

pub(in crate::decompile::late::normalize) fn if_need(
    then_branch: OptionLikeNeed,
    else_branch: OptionLikeNeed,
    then_none_like: bool,
    else_none_like: bool,
) -> OptionLikeNeed {
    let has_none = either(
        if then_none_like { then_branch } else { None },
        if else_none_like { else_branch } else { None },
    );
    let has_option_branch = either(then_branch, else_branch);
    both(has_none, has_option_branch)
}

pub(in crate::decompile::late::normalize) fn when_need(
    has_none: bool,
    bodies: impl IntoIterator<Item = OptionLikeNeed>,
) -> OptionLikeNeed {
    let has_option_branch = bodies.into_iter().fold(None, either);
    if has_none { has_option_branch } else { None }
}

/// One job on [`option_like_need`]'s stack.
enum OptStep<'a> {
    Visit(&'a PseudoExpr),
    Let,
    If {
        then_none_like: bool,
        else_none_like: bool,
    },
    When {
        has_none: bool,
        clause_count: usize,
    },
}

/// The need of a whole value, folded bottom-up: each node's need is combined
/// from its children's, popped off `needs` in the order the children were
/// pushed (REVERSE, so they pop in source order). Every `Var` is looked up in
/// `option_like_vars` as given, so the answer holds for that stack and every
/// prefix of it.
pub(in crate::decompile::late::normalize) fn option_like_need(
    expr: &PseudoExpr,
    option_like_functions: &HashSet<String>,
    option_like_vars: &[HashSet<String>],
) -> OptionLikeNeed {
    let mut steps: Vec<OptStep<'_>> = vec![OptStep::Visit(expr)];
    let mut needs: Vec<OptionLikeNeed> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            OptStep::Visit(expr) => {
                match option_like_node(expr, option_like_functions, option_like_vars) {
                    OptionLikeNode::Leaf(need) => needs.push(need),
                    OptionLikeNode::Let { value, body } => {
                        steps.push(OptStep::Let);
                        steps.push(OptStep::Visit(body));
                        steps.push(OptStep::Visit(value));
                    }
                    OptionLikeNode::If {
                        then_branch,
                        else_branch,
                        then_none_like,
                        else_none_like,
                    } => {
                        steps.push(OptStep::If {
                            then_none_like,
                            else_none_like,
                        });
                        steps.push(OptStep::Visit(else_branch));
                        steps.push(OptStep::Visit(then_branch));
                    }
                    OptionLikeNode::When { has_none, clauses } => {
                        steps.push(OptStep::When {
                            has_none,
                            clause_count: clauses.len(),
                        });
                        for clause in clauses.iter().rev() {
                            steps.push(OptStep::Visit(&clause.body));
                        }
                    }
                }
            }
            OptStep::Let => {
                let body = needs.pop().expect("let body need");
                let value = needs.pop().expect("let value need");
                needs.push(let_need(value, body));
            }
            OptStep::If {
                then_none_like,
                else_none_like,
            } => {
                let else_branch = needs.pop().expect("if else need");
                let then_branch = needs.pop().expect("if then need");
                needs.push(if_need(
                    then_branch,
                    else_branch,
                    then_none_like,
                    else_none_like,
                ));
            }
            OptStep::When {
                has_none,
                clause_count,
            } => {
                let at = needs.len() - clause_count;
                let bodies = needs.split_off(at);
                needs.push(when_need(has_none, bodies));
            }
        }
    }

    needs.pop().expect("option_like_need leaves one need")
}
