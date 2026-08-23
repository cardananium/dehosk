use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

use super::shadowing::pattern_has_matching_binder;

/// Count how many references to `name`/`target_id` appear in `expr`, and how
/// many of those are immediately under a `Force`.
pub(super) fn count_var_usages(
    expr: &PseudoExpr,
    name: &str,
    target_id: Option<VarId>,
) -> (usize, usize) {
    let matches_target = |n: &str, id: Option<VarId>| {
        crate::decompile::var_match::refs_match(n, id, name, target_id)
    };
    let binder_blocks_target = |b: &Binder| matches_target(b.as_str(), b.id.get());
    let pattern_blocks_target =
        |p: &WhenPattern| pattern_has_matching_binder(p, |b| binder_blocks_target(b));
    let when_clause_blocks_target = |subject_name: Option<&Binder>, clause: &WhenClause| {
        subject_name.is_some_and(|sn| binder_blocks_target(sn))
            || pattern_blocks_target(&clause.pattern)
    };

    enum Step<'a> {
        Enter(&'a PseudoExpr),
        Unblock {
            blocks: bool,
        },
        LetValue {
            name: &'a str,
            id: &'a Option<VarId>,
            body: &'a PseudoExpr,
        },
        WhenNext {
            subject_name: Option<&'a Binder>,
            clauses: &'a [WhenClause],
            idx: usize,
        },
        WhenClauseBody {
            subject_name: Option<&'a Binder>,
            clauses: &'a [WhenClause],
            idx: usize,
        },
    }

    let mut stack = vec![Step::Enter(expr)];
    let mut blocked_depth: usize = 0;
    let mut suppressed_forced_var_hits: usize = 0;
    let mut force_uses: usize = 0;
    let mut total_uses: usize = 0;

    while let Some(step) = stack.pop() {
        match step {
            Step::Enter(expr) => match expr {
                PseudoExpr::Var { name: n, id } => {
                    if blocked_depth > 0 || !matches_target(n, id.get()) {
                        continue;
                    }
                    if suppressed_forced_var_hits > 0 {
                        suppressed_forced_var_hits -= 1;
                        continue;
                    }
                    total_uses += 1;
                }
                PseudoExpr::Force(inner) => {
                    if blocked_depth == 0
                        && let PseudoExpr::Var { name: n, id, .. } = inner.as_ref()
                        && matches_target(n, id.get())
                    {
                        force_uses += 1;
                        total_uses += 1;
                        suppressed_forced_var_hits += 1;
                    }
                    stack.push(Step::Enter(inner));
                }
                PseudoExpr::Lambda { params, body } => {
                    let blocks = params.iter().any(|p| binder_blocks_target(p));
                    if blocks {
                        blocked_depth += 1;
                    }
                    stack.push(Step::Unblock { blocks });
                    stack.push(Step::Enter(body));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    let blocks = binder_blocks_target(name)
                        || params.iter().any(|p| binder_blocks_target(p));
                    if blocks {
                        blocked_depth += 1;
                    }
                    stack.push(Step::Unblock { blocks });
                    stack.push(Step::Enter(body));
                }
                PseudoExpr::Apply { function, args } => {
                    for a in args.iter().rev() {
                        stack.push(Step::Enter(a));
                    }
                    stack.push(Step::Enter(function));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    // The binding comes into scope BETWEEN the value and the
                    // body, so whether it blocks the target is decided in
                    // `Step::LetValue`, after `value` is walked but before
                    // `body` is.
                    stack.push(Step::LetValue { name, id, body });
                    stack.push(Step::Enter(value));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    stack.push(Step::Enter(else_branch));
                    stack.push(Step::Enter(then_branch));
                    stack.push(Step::Enter(condition));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    stack.push(Step::WhenNext {
                        subject_name: subject_name.as_ref(),
                        clauses,
                        idx: 0,
                    });
                    stack.push(Step::Enter(subject));
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail {
                        stack.push(Step::Enter(t));
                    }
                    for e in elements.iter().rev() {
                        stack.push(Step::Enter(e));
                    }
                }
                PseudoExpr::Tuple(elements) => {
                    for e in elements.iter().rev() {
                        stack.push(Step::Enter(e));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    stack.push(Step::Enter(b));
                    stack.push(Step::Enter(a));
                }
                PseudoExpr::Constr { fields, .. } => {
                    for f in fields.iter().rev() {
                        stack.push(Step::Enter(f));
                    }
                }
                PseudoExpr::FieldAccess { record, .. } => {
                    stack.push(Step::Enter(record));
                }
                PseudoExpr::IndexAccess { collection, .. } => {
                    stack.push(Step::Enter(collection));
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    stack.push(Step::Enter(right));
                    stack.push(Step::Enter(left));
                }
                PseudoExpr::UnOp { operand, .. } => {
                    stack.push(Step::Enter(operand));
                }
                PseudoExpr::BuiltinCall { args, .. } => {
                    for a in args.iter().rev() {
                        stack.push(Step::Enter(a));
                    }
                }
                PseudoExpr::Delay(inner) => {
                    stack.push(Step::Enter(inner));
                }
                PseudoExpr::Trace { message, value } => {
                    stack.push(Step::Enter(value));
                    stack.push(Step::Enter(message));
                }
                // Leaves: nothing further to do.
                PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::Unit
                | PseudoExpr::Error { .. }
                | PseudoExpr::Raw { .. }
                | PseudoExpr::Data(_)
                | PseudoExpr::HelperSymbol(_) => {}
            },
            Step::Unblock { blocks } => {
                if blocks {
                    blocked_depth -= 1;
                }
            }
            Step::LetValue { name, id, body } => {
                let blocks = matches_target(name, id.get());
                if blocks {
                    blocked_depth += 1;
                }
                stack.push(Step::Unblock { blocks });
                stack.push(Step::Enter(body));
            }
            Step::WhenNext {
                subject_name,
                clauses,
                idx,
            } => {
                if idx >= clauses.len() {
                    continue;
                }
                let clause = &clauses[idx];
                stack.push(Step::WhenClauseBody {
                    subject_name,
                    clauses,
                    idx,
                });
                if let WhenPattern::Literal(lit) = &clause.pattern {
                    stack.push(Step::Enter(lit));
                }
            }
            Step::WhenClauseBody {
                subject_name,
                clauses,
                idx,
            } => {
                let clause = &clauses[idx];
                let blocks = when_clause_blocks_target(subject_name, clause);
                if blocks {
                    blocked_depth += 1;
                }
                stack.push(Step::WhenNext {
                    subject_name,
                    clauses,
                    idx: idx + 1,
                });
                stack.push(Step::Unblock { blocks });
                stack.push(Step::Enter(&clause.body));
                if let Some(guard) = &clause.guard {
                    stack.push(Step::Enter(guard));
                }
            }
        }
    }

    (force_uses, total_uses)
}
