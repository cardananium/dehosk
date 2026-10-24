//! Collapse UPLC's `Bool ↔ Constr<0|1>` round-trip (`True` is
//! `Constr<1>`, `False` is `Constr<0>`).
//!
//! When `X` is `Bool` in `FinalTypeTable`, or a structural Bool
//! (`==` / `<` / `&&` / `||` / `!` / literal), rewrite
//! `when X is { Constr<1> -> T; _ -> E }` to `if X { T } else { E }`
//! and the tag-0 arm to `if !X`. The Constr arm must come first:
//! a leading wildcard makes the other body unreachable.
//!
//! After `solve_type_constraints_with_final_table`, before
//! `PropagateTypesFinal`. A bare `Var` needs a Bool table entry or
//! a structurally-Bool let-value; structural subjects fire without
//! the table.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::decompile::final_type_table::FinalTypeTable;
use crate::pseudo::ast::{BinaryOp, PseudoExpr, PseudoType, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

/// Entry point: walk `expr` and collapse Bool↔Constr<0|1> round-
/// trip Whens into `If` shapes. `final_types` classifies opaque
/// `Var` subjects; a let-value scope tracker built during the
/// walk also accepts a `Var` whose let-binding value is
/// structurally Bool-producing (`let ok = a == X && b == Y; when
/// ok is { ... }`), which the type table may not yet call Bool.
pub(crate) fn bool_constr_collapse(expr: PseudoExpr, final_types: &FinalTypeTable) -> PseudoExpr {
    let mut env = LetBoolEnv::default();
    walk(expr, final_types, &mut env)
}

/// Lexical-scope map: `VarId` → true iff the let-binding value was
/// structurally Bool-producing (BinOp comparison/logical, UnOp::Not,
/// Bool literal). Built during the walk so a `Var` subject can be
/// detected as Bool without `FinalTypeTable` cooperation.
#[derive(Debug, Default)]
struct LetBoolEnv {
    bool_let_ids: HashMap<VarId, bool>,
}

impl LetBoolEnv {
    fn enter_binding(&mut self, id: Option<VarId>, value: &PseudoExpr) {
        if let Some(vid) = id
            && value_is_structurally_bool(value)
        {
            self.bool_let_ids.insert(vid, true);
        }
    }
    fn lookup(&self, id: VarId) -> bool {
        self.bool_let_ids.get(&id).copied().unwrap_or(false)
    }
}

fn value_is_structurally_bool(expr: &PseudoExpr) -> bool {
    // Peer through leading `Let` bindings: a `let a = …; let b = …;
    // <bool-producing tail>` chain has the type of its tail. The
    // auxiliary bindings are pure projections (`.fields[i]`,
    // `un_i_data`, …) that only feed the tail comparison/logical op.
    let mut cursor = expr;
    while let PseudoExpr::Let { body, .. } = cursor {
        cursor = body;
    }
    matches!(
        cursor,
        PseudoExpr::Bool(_)
            | PseudoExpr::BinOp {
                op: BinaryOp::Eq
                    | BinaryOp::Neq
                    | BinaryOp::Lt
                    | BinaryOp::Lte
                    | BinaryOp::Gt
                    | BinaryOp::Gte
                    | BinaryOp::And
                    | BinaryOp::Or,
                ..
            }
            | PseudoExpr::UnOp {
                op: UnaryOp::Not,
                ..
            }
    )
}

/// One pending step of [`walk`].
enum WalkStep {
    /// Walk this subtree.
    Visit(PseudoExpr),
    /// The `let` value is walked and on top of `done`: register the binding
    /// for the body's scope, then walk the body.
    LetBody {
        name: String,
        id: Option<VarId>,
        body: PBox,
    },
    /// The `let` value and body are on `done`: reassemble the `Let`.
    LetBuild { name: String, id: Option<VarId> },
    /// Every other node: its walked children are on `done`; put them back
    /// into the shell they were taken out of, then try the collapse.
    Rebuild { shell: PseudoExpr, count: usize },
}

/// Bottom-up walk: children first, then the When→If collapse at the node.
/// Let-binding awareness is threaded through `env` so nested Whens can see
/// outer let scopes.
///
/// Runs on a heap stack: nesting depth is script-controlled, and on
/// `wasm32` the engine's call stack cannot be grown to match. Children are
/// visited in `map_children` order — a `let` value before its body, a
/// clause's guard before its body, literal patterns never — and the binding
/// registers between the value and the body, as a recursive descent would.
fn walk(expr: PseudoExpr, final_types: &FinalTypeTable, env: &mut LetBoolEnv) -> PseudoExpr {
    let mut steps: Vec<WalkStep> = vec![WalkStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            WalkStep::Visit(PseudoExpr::Let {
                name,
                id,
                value,
                body,
            }) => {
                // Walk the value first (in the OUTER scope).
                steps.push(WalkStep::LetBody { name, id, body });
                steps.push(WalkStep::Visit(value.into_inner()));
            }
            WalkStep::Visit(other) => {
                let (shell, kids) = split_children(other);
                steps.push(WalkStep::Rebuild {
                    shell,
                    count: kids.len(),
                });
                // Reversed so they pop — and so land on `done` — in order.
                for kid in kids.into_iter().rev() {
                    steps.push(WalkStep::Visit(kid));
                }
            }
            WalkStep::LetBody { name, id, body } => {
                // Register the binding for the body's scope; the walked
                // value keeps its shape, since `walk` rewrites When→If
                // only, never BinOp / UnOp.
                env.enter_binding(id, done.last().expect("let value"));
                steps.push(WalkStep::LetBuild { name, id });
                steps.push(WalkStep::Visit(body.into_inner()));
            }
            WalkStep::LetBuild { name, id } => {
                let body = done.pop().expect("let body");
                let value = done.pop().expect("let value");
                // No deregistration: a shadowing let inside the body
                // overwrites the entry, and a valid program never
                // re-enters the same `VarId` in another scope.
                done.push(PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(body),
                });
            }
            WalkStep::Rebuild { shell, count } => {
                let at = done.len() - count;
                let kids = done.split_off(at);
                let rebuilt = join_children(shell, kids);
                done.push(collapse_bool_when(rebuilt, final_types, env));
            }
        }
    }

    done.pop().expect("walk leaves exactly one result")
}

/// Split a node into a SHELL — every immediate child replaced by a `Unit`
/// placeholder — plus those children in `map_children` order.
fn split_children(expr: PseudoExpr) -> (PseudoExpr, Vec<PseudoExpr>) {
    let mut kids: Vec<PseudoExpr> = Vec::new();
    let shell = crate::decompile::render_prep::scope_recurse::map_children(expr, |c| {
        kids.push(c);
        PseudoExpr::Unit
    });
    (shell, kids)
}

/// Put walked children back into a shell from [`split_children`].
fn join_children(shell: PseudoExpr, kids: Vec<PseudoExpr>) -> PseudoExpr {
    let mut kids = kids.into_iter();
    crate::decompile::render_prep::scope_recurse::map_children(shell, |_| {
        kids.next().expect("split_children left one child per slot")
    })
}

/// The When→If collapse at one node whose children are already walked.
fn collapse_bool_when(
    expr: PseudoExpr,
    final_types: &FinalTypeTable,
    env: &LetBoolEnv,
) -> PseudoExpr {
    match expr {
        PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } if clauses.len() == 2 => {
            // Soundness: with `when x as y is …`, branches may
            // reference `y`, left unbound by the When→If rewrite,
            // so refuse the collapse when `subject_name` is set.
            if subject_name.is_some() {
                return PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                };
            }
            // Soundness: `when` clauses are ORDERED. If the first
            // clause is `Wildcard` it matches everything and the
            // second-clause body is unreachable, so the Constr arm
            // must come FIRST and the Wildcard arm SECOND.
            let Some(constr_tag) = identify_bool_constr_arm(&clauses[0]) else {
                return PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                };
            };
            let other = &clauses[1];
            if !matches!(other.pattern, WhenPattern::Wildcard) || other.guard.is_some() {
                return PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                };
            }
            if !subject_is_bool(&subject, final_types, env) {
                return PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                };
            }
            // The arms move into the `If`: copying them would cost the
            // size of the subtree at every collapsed level.
            let mut arms = clauses.into_iter();
            let then_body = arms.next().expect("bool arm").body;
            let else_body = arms.next().expect("wildcard arm").body;
            // Tag 1 → `If { subject, T, E }`; Tag 0 → `If { Not(subject), T, E }`.
            let condition: PBox = match constr_tag {
                1 => subject,
                0 => PBox::new(PseudoExpr::UnOp {
                    op: UnaryOp::Not,
                    operand: subject,
                }),
                _ => unreachable!(),
            };
            PseudoExpr::If {
                condition,
                then_branch: PBox::new(then_body),
                else_branch: PBox::new(else_body),
            }
        }
        other => other,
    }
}

/// Returns `Some(tag)` if the clause has the church-Bool arm shape —
/// `Constructor { tag: 0|1, fields: [], shape: Unknown { ... } |
/// Known(True|False) }` with no guard. Otherwise `None`.
fn identify_bool_constr_arm(clause: &WhenClause) -> Option<usize> {
    if clause.guard.is_some() {
        return None;
    }
    let WhenPattern::Constructor {
        tag, fields, shape, ..
    } = &clause.pattern
    else {
        return None;
    };
    if !fields.is_empty() {
        return None;
    }
    let tag_ok = match shape {
        ConstructorShape::Unknown {
            tag: t, arity: 0, ..
        } => *t == 0 || *t == 1,
        ConstructorShape::Known(KnownConstructor::True) => *tag == 1,
        ConstructorShape::Known(KnownConstructor::False) => *tag == 0,
        _ => false,
    };
    if !tag_ok {
        return None;
    }
    if *tag > 1 {
        return None;
    }
    Some(*tag)
}

/// Returns true when `subject` is provably Bool: structural
/// evidence (Bool-producing binary/unary operators), the
/// `FinalTypeTable`'s resolved type, or the let-binding scope
/// (`let X = <bool-producing>; when X is { ... }`).
fn subject_is_bool(subject: &PseudoExpr, final_types: &FinalTypeTable, env: &LetBoolEnv) -> bool {
    if value_is_structurally_bool(subject) {
        return true;
    }
    if let PseudoExpr::Var { id: Some(vid), .. } = subject
        && (var_resolves_to_bool(*vid, final_types) || env.lookup(*vid))
    {
        return true;
    }
    false
}

fn var_resolves_to_bool(vid: VarId, final_types: &FinalTypeTable) -> bool {
    final_types
        .type_of_var(vid)
        .is_some_and(|ty| matches!(&*ty, PseudoType::Bool))
}

#[cfg(test)]
mod tests;
