use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, PseudoType, UnaryOp};
use crate::pseudo::var_id::VarId;
use crate::pseudo::walker::{FoldAction, Walker};

use super::analysis::{ClassifiedBindings, KnownBindings, selector_bool_value};

pub(super) fn rewrite_cps_bodies(
    expr: PseudoExpr,
    classifications: &ClassifiedBindings,
    fst_names: &KnownBindings,
    snd_names: &KnownBindings,
) -> PseudoExpr {
    RewriteBodies {
        classifications,
        fst_names,
        snd_names,
    }
    .fold(expr)
}

struct RewriteBodies<'a> {
    classifications: &'a ClassifiedBindings,
    fst_names: &'a KnownBindings,
    snd_names: &'a KnownBindings,
}

impl Walker for RewriteBodies<'_> {
    fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
        if let PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } = expr
            && self.classifications.contains_binding(name, *id)
        {
            // Rewrite the lambda value: replace selector vars with Bool.
            let new_value = rewrite_selector_body(value, self.fst_names, self.snd_names);
            // Continue folding the body normally.
            let new_body = self.fold((**body).clone());
            return FoldAction::Replace(PseudoExpr::Let {
                name: name.clone(),
                id: *id,
                value: PBox::new(new_value),
                body: PBox::new(new_body),
            });
        }
        FoldAction::Walk
    }
}

/// Transform a lambda value by replacing selector variable references
/// with Bool literals and simplifying resulting boolean expressions.
pub(super) fn rewrite_selector_body(
    expr: &PseudoExpr,
    fst_names: &KnownBindings,
    snd_names: &KnownBindings,
) -> PseudoExpr {
    fn can_collapse_to_boolean(expr: &PseudoExpr) -> bool {
        fn has_known_non_boolean_type(expr: &PseudoExpr) -> bool {
            matches!(
                expr.type_resolution().as_deref(),
                Some(
                    PseudoType::Int
                        | PseudoType::ByteArray
                        | PseudoType::String
                        | PseudoType::Unit
                        | PseudoType::List(_)
                        | PseudoType::Tuple(_)
                        | PseudoType::Pair(_, _)
                        | PseudoType::Option(_)
                        | PseudoType::Result(_, _)
                        | PseudoType::Function { .. }
                        | PseudoType::Data
                        | PseudoType::G1Element
                        | PseudoType::G2Element
                        | PseudoType::MillerLoopResult
                        | PseudoType::Named(_)
                )
            )
        }

        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            if has_known_non_boolean_type(current) {
                return false;
            }

            match current {
                PseudoExpr::Bool(_) => {}
                PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Unit
                | PseudoExpr::Data(_)
                | PseudoExpr::List { .. }
                | PseudoExpr::Tuple(_)
                | PseudoExpr::Pair(_, _)
                | PseudoExpr::Raw { .. }
                | PseudoExpr::Lambda { .. }
                | PseudoExpr::RecFn { .. }
                | PseudoExpr::HelperSymbol(_)
                | PseudoExpr::Error { .. } => return false,
                PseudoExpr::Var { .. } => {}
                PseudoExpr::Let { body, .. } => pending.push(body),
                PseudoExpr::Constr { fields, .. } => {
                    if !fields.is_empty() {
                        return false;
                    }
                }
                PseudoExpr::BuiltinCall { name, .. } if name.is_data_constructor() => {
                    return false;
                }
                PseudoExpr::BuiltinCall { .. } => return false,
                PseudoExpr::Apply { .. } => return false,
                PseudoExpr::FieldAccess { .. } => return false,
                PseudoExpr::IndexAccess { .. } => return false,
                PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
                PseudoExpr::Trace { value, .. } => pending.push(value),
                PseudoExpr::BinOp { op, left, right } => match op {
                    BinaryOp::Eq
                    | BinaryOp::Neq
                    | BinaryOp::Lt
                    | BinaryOp::Lte
                    | BinaryOp::Gt
                    | BinaryOp::Gte => {}
                    BinaryOp::And | BinaryOp::Or => {
                        pending.push(left);
                        pending.push(right);
                    }
                    _ => return false,
                },
                PseudoExpr::UnOp {
                    op: UnaryOp::Not,
                    operand,
                } => pending.push(operand),
                PseudoExpr::UnOp { .. } => return false,
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.push(condition);
                    pending.push(then_branch);
                    pending.push(else_branch);
                }
                PseudoExpr::When { clauses, .. } => {
                    pending.extend(clauses.iter().map(|clause| &clause.body));
                }
            }
        }
        true
    }

    struct SelectorToBool<'a> {
        fst_names: &'a KnownBindings,
        snd_names: &'a KnownBindings,
    }

    impl Walker for SelectorToBool<'_> {
        fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
            if self.fst_names.contains_var(&name, id) {
                PseudoExpr::Bool(true)
            } else if self.snd_names.contains_var(&name, id) {
                PseudoExpr::Bool(false)
            } else {
                PseudoExpr::Var { name, id }
            }
        }

        fn post_lambda(&mut self, params: Vec<Binder>, body: PseudoExpr) -> PseudoExpr {
            let lambda = PseudoExpr::Lambda {
                params,
                body: PBox::new(body),
            };
            match selector_bool_value(&lambda, self.fst_names, self.snd_names) {
                Some(value) => PseudoExpr::Bool(value),
                None => lambda,
            }
        }

        fn post_delay(&mut self, inner: PseudoExpr) -> PseudoExpr {
            // Strip delay around Bool values (they don't need thunking).
            if matches!(&inner, PseudoExpr::Bool(_)) {
                inner
            } else {
                PseudoExpr::Delay(PBox::new(inner))
            }
        }

        fn post_force(&mut self, inner: PseudoExpr) -> PseudoExpr {
            if matches!(&inner, PseudoExpr::Bool(_)) {
                inner
            } else {
                PseudoExpr::Force(PBox::new(inner))
            }
        }

        fn post_if(
            &mut self,
            condition: PseudoExpr,
            then_branch: PseudoExpr,
            else_branch: PseudoExpr,
        ) -> PseudoExpr {
            // if cond { True } else { False } -> cond
            if matches!(&then_branch, PseudoExpr::Bool(true))
                && matches!(&else_branch, PseudoExpr::Bool(false))
                && can_collapse_to_boolean(&condition)
            {
                return condition;
            }
            // if cond { False } else { True } -> !cond
            if matches!(&then_branch, PseudoExpr::Bool(false))
                && matches!(&else_branch, PseudoExpr::Bool(true))
                && can_collapse_to_boolean(&condition)
            {
                // Try to invert comparison operator directly.
                if let PseudoExpr::BinOp { op, left, right } = &condition {
                    let inverted = match op {
                        BinaryOp::Eq => Some(BinaryOp::Neq),
                        BinaryOp::Neq => Some(BinaryOp::Eq),
                        BinaryOp::Lt => Some(BinaryOp::Gte),
                        BinaryOp::Lte => Some(BinaryOp::Gt),
                        BinaryOp::Gt => Some(BinaryOp::Lte),
                        BinaryOp::Gte => Some(BinaryOp::Lt),
                        _ => None,
                    };
                    if let Some(new_op) = inverted {
                        return PseudoExpr::BinOp {
                            op: new_op,
                            left: left.clone(),
                            right: right.clone(),
                        };
                    }
                }
                return PseudoExpr::UnOp {
                    op: UnaryOp::Not,
                    operand: PBox::new(condition),
                };
            }
            // if cond { True } else { expr } -> cond || expr
            if matches!(&then_branch, PseudoExpr::Bool(true))
                && can_collapse_to_boolean(&condition)
                && can_collapse_to_boolean(&else_branch)
            {
                return PseudoExpr::BinOp {
                    op: BinaryOp::Or,
                    left: PBox::new(condition),
                    right: PBox::new(else_branch),
                };
            }
            // if cond { expr } else { False } -> cond && expr
            if matches!(&else_branch, PseudoExpr::Bool(false))
                && can_collapse_to_boolean(&condition)
                && can_collapse_to_boolean(&then_branch)
            {
                return PseudoExpr::BinOp {
                    op: BinaryOp::And,
                    left: PBox::new(condition),
                    right: PBox::new(then_branch),
                };
            }
            PseudoExpr::If {
                condition: PBox::new(condition),
                then_branch: PBox::new(then_branch),
                else_branch: PBox::new(else_branch),
            }
        }
    }

    SelectorToBool {
        fst_names,
        snd_names,
    }
    .fold(expr.clone())
}
