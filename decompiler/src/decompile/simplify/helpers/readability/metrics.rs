use crate::pseudo::ast::{PseudoData, PseudoExpr};

use super::Simplifier;

impl Simplifier {
    pub(crate) fn static_data_expr_node_count(expr: &PseudoExpr) -> Option<usize> {
        let mut count = 0usize;
        let mut pending = vec![expr];
        while let Some(cur) = pending.pop() {
            match cur {
                PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::Unit => count += 1,

                PseudoExpr::Data(data) => count += 1 + Self::data_node_count(data),

                PseudoExpr::List { elements, tail } => {
                    if tail.is_some() {
                        return None;
                    }
                    count += 1;
                    pending.extend(elements.iter().rev());
                }
                PseudoExpr::Tuple(items) => {
                    count += 1;
                    pending.extend(items.iter().rev());
                }
                PseudoExpr::Pair(a, b) => {
                    count += 1;
                    pending.push(b.as_ref());
                    pending.push(a.as_ref());
                }
                PseudoExpr::Constr { fields, .. } => {
                    count += 1;
                    pending.extend(fields.iter().rev());
                }
                PseudoExpr::BuiltinCall { name, args } if *name == crate::BuiltinId::DataConstr => {
                    count += 1;
                    pending.extend(args.iter().rev());
                }

                _ => return None,
            }
        }
        Some(count)
    }

    pub(crate) fn is_static_data_expr(expr: &PseudoExpr) -> bool {
        Self::static_data_expr_node_count(expr).is_some()
    }

    pub(crate) fn expr_node_count(expr: &PseudoExpr) -> usize {
        let mut count = 0usize;
        let mut pending = vec![expr];
        while let Some(cur) = pending.pop() {
            count += 1;
            match cur {
                PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::Unit
                | PseudoExpr::Var { .. }
                | PseudoExpr::Error { .. }
                | PseudoExpr::Raw { .. }
                | PseudoExpr::HelperSymbol(_) => {}

                PseudoExpr::Lambda { body, .. }
                | PseudoExpr::RecFn { body, .. }
                | PseudoExpr::Delay(body)
                | PseudoExpr::Force(body) => pending.push(body.as_ref()),

                PseudoExpr::Apply { function, args } => {
                    pending.extend(args.iter().rev());
                    pending.push(function.as_ref());
                }
                PseudoExpr::Let { value, body, .. } => {
                    pending.push(body.as_ref());
                    pending.push(value.as_ref());
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.push(else_branch.as_ref());
                    pending.push(then_branch.as_ref());
                    pending.push(condition.as_ref());
                }
                PseudoExpr::When {
                    subject, clauses, ..
                } => {
                    for c in clauses.iter().rev() {
                        pending.push(&c.body);
                    }
                    pending.push(subject.as_ref());
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail {
                        pending.push(t.as_ref());
                    }
                    pending.extend(elements.iter().rev());
                }
                PseudoExpr::Tuple(items) => pending.extend(items.iter().rev()),
                PseudoExpr::Pair(a, b) => {
                    pending.push(b.as_ref());
                    pending.push(a.as_ref());
                }
                PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter().rev()),
                PseudoExpr::Data(data) => count += Self::data_node_count(data),
                PseudoExpr::FieldAccess { record, .. } => pending.push(record.as_ref()),
                PseudoExpr::IndexAccess { collection, .. } => pending.push(collection.as_ref()),
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(right.as_ref());
                    pending.push(left.as_ref());
                }
                PseudoExpr::UnOp { operand, .. } => pending.push(operand.as_ref()),
                PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter().rev()),
                PseudoExpr::Trace { message, value } => {
                    pending.push(value.as_ref());
                    pending.push(message.as_ref());
                }
            }
        }
        count
    }

    fn data_node_count(data: &PseudoData) -> usize {
        match data {
            PseudoData::Integer(_) | PseudoData::ByteString(_) => 1,
            PseudoData::List(items) => 1 + items.iter().map(Self::data_node_count).sum::<usize>(),
            PseudoData::Map(entries) => {
                1 + entries
                    .iter()
                    .map(|(k, v)| Self::data_node_count(k) + Self::data_node_count(v))
                    .sum::<usize>()
            }
            PseudoData::Constr(_, fields) => {
                1 + fields.iter().map(Self::data_node_count).sum::<usize>()
            }
        }
    }
}
