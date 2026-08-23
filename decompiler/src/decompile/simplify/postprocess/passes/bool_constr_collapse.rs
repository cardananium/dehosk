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

fn walk(expr: PseudoExpr, final_types: &FinalTypeTable, env: &mut LetBoolEnv) -> PseudoExpr {
    // Recurse first (bottom-up). Let-binding awareness is threaded
    // through `env` so nested Whens can see outer let scopes.
    let expr = recurse_children(expr, final_types, env);
    // Then try the When→If collapse at this node.
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
            let Some((constr_tag, then_body)) = identify_bool_constr_arm(&clauses[0]) else {
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
            let else_body = other.body.clone();
            if !subject_is_bool(&subject, final_types, env) {
                return PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                };
            }
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

/// Returns `Some((tag, body))` if the clause has the church-Bool
/// arm shape — `Constructor { tag: 0|1, fields: [], shape: Unknown
/// { ... } | Known(True|False) }` with no guard. Otherwise `None`.
fn identify_bool_constr_arm(clause: &WhenClause) -> Option<(usize, PseudoExpr)> {
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
    Some((*tag, clause.body.clone()))
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

fn recurse_children(
    expr: PseudoExpr,
    final_types: &FinalTypeTable,
    env: &mut LetBoolEnv,
) -> PseudoExpr {
    match expr {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } => {
            // Walk the value first (in the OUTER scope).
            let value = walk(value.into_inner(), final_types, env);
            // Register the binding for the body's scope; the walked
            // value keeps its shape, since `walk` rewrites When→If
            // only, never BinOp / UnOp.
            env.enter_binding(id, &value);
            let body = walk(body.into_inner(), final_types, env);
            // No deregistration: a shadowing let inside the body
            // overwrites the entry, and a valid program never
            // re-enters the same `VarId` in another scope.
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }
        PseudoExpr::Lambda { params, body } => PseudoExpr::Lambda {
            params,
            body: PBox::new(walk(body.into_inner(), final_types, env)),
        },
        PseudoExpr::RecFn { name, params, body } => PseudoExpr::RecFn {
            name,
            params,
            body: PBox::new(walk(body.into_inner(), final_types, env)),
        },
        PseudoExpr::Apply { function, args } => {
            let function = PBox::new(walk(function.into_inner(), final_types, env));
            let mut new_args = Vec::with_capacity(args.len());
            for a in args {
                new_args.push(walk(a, final_types, env));
            }
            PseudoExpr::Apply {
                function,
                args: new_args.into(),
            }
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => PseudoExpr::If {
            condition: PBox::new(walk(condition.into_inner(), final_types, env)),
            then_branch: PBox::new(walk(then_branch.into_inner(), final_types, env)),
            else_branch: PBox::new(walk(else_branch.into_inner(), final_types, env)),
        },
        PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } => {
            let subject = PBox::new(walk(subject.into_inner(), final_types, env));
            let mut new_clauses = Vec::with_capacity(clauses.len());
            for c in clauses {
                let guard = c.guard.map(|g| walk(g, final_types, env));
                let body = walk(c.body, final_types, env);
                new_clauses.push(WhenClause {
                    pattern: c.pattern,
                    guard,
                    body,
                });
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses: new_clauses,
            }
        }
        PseudoExpr::List { elements, tail } => {
            let mut new_elements = Vec::with_capacity(elements.len());
            for e in elements {
                new_elements.push(walk(e, final_types, env));
            }
            let new_tail = tail.map(|t| PBox::new(walk(t.into_inner(), final_types, env)));
            PseudoExpr::List {
                elements: new_elements.into(),
                tail: new_tail,
            }
        }
        PseudoExpr::Tuple(items) => {
            let mut new_items = Vec::with_capacity(items.len());
            for i in items {
                new_items.push(walk(i, final_types, env));
            }
            PseudoExpr::Tuple(new_items.into())
        }
        PseudoExpr::Pair(a, b) => PseudoExpr::Pair(
            PBox::new(walk(a.into_inner(), final_types, env)),
            PBox::new(walk(b.into_inner(), final_types, env)),
        ),
        PseudoExpr::Constr {
            type_hint,
            tag,
            fields,
            shape,
        } => {
            let mut new_fields = Vec::with_capacity(fields.len());
            for f in fields {
                new_fields.push(walk(f, final_types, env));
            }
            PseudoExpr::Constr {
                type_hint,
                tag,
                fields: new_fields.into(),
                shape,
            }
        }
        PseudoExpr::FieldAccess { record, selector } => PseudoExpr::FieldAccess {
            record: PBox::new(walk(record.into_inner(), final_types, env)),
            selector,
        },
        PseudoExpr::IndexAccess { collection, index } => PseudoExpr::IndexAccess {
            collection: PBox::new(walk(collection.into_inner(), final_types, env)),
            index,
        },
        PseudoExpr::BinOp { op, left, right } => PseudoExpr::BinOp {
            op,
            left: PBox::new(walk(left.into_inner(), final_types, env)),
            right: PBox::new(walk(right.into_inner(), final_types, env)),
        },
        PseudoExpr::UnOp { op, operand } => PseudoExpr::UnOp {
            op,
            operand: PBox::new(walk(operand.into_inner(), final_types, env)),
        },
        PseudoExpr::BuiltinCall { name, args } => {
            let mut new_args = Vec::with_capacity(args.len());
            for a in args {
                new_args.push(walk(a, final_types, env));
            }
            PseudoExpr::BuiltinCall {
                name,
                args: new_args.into(),
            }
        }
        PseudoExpr::Delay(inner) => {
            PseudoExpr::Delay(PBox::new(walk(inner.into_inner(), final_types, env)))
        }
        PseudoExpr::Force(inner) => {
            PseudoExpr::Force(PBox::new(walk(inner.into_inner(), final_types, env)))
        }
        PseudoExpr::Trace { message, value } => PseudoExpr::Trace {
            message: PBox::new(walk(message.into_inner(), final_types, env)),
            value: PBox::new(walk(value.into_inner(), final_types, env)),
        },
        other @ (PseudoExpr::Int(_)
        | PseudoExpr::ByteArray(_)
        | PseudoExpr::String(_)
        | PseudoExpr::Bool(_)
        | PseudoExpr::Unit
        | PseudoExpr::Var { .. }
        | PseudoExpr::Error { .. }
        | PseudoExpr::Raw { .. }
        | PseudoExpr::Data(_)
        | PseudoExpr::HelperSymbol(_)) => other,
    }
}

#[cfg(test)]
mod tests;
