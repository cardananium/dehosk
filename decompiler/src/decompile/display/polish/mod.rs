use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoData, PseudoExpr};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;
use std::collections::HashSet;

/// Extract visually heavy static literals into named bindings late in the
/// pipeline, so they show up in pass snapshots and remain debugger-visible.
pub(crate) fn extract_heavy_constants(expr: PseudoExpr) -> PseudoExpr {
    let mut used_names = HashSet::new();
    crate::decompile::simplify::Simplifier::collect_var_names(&expr, &mut used_names);
    let mut extractor = HeavyConstantExtractor {
        counter: 0,
        used_names,
    };
    extractor.fold(expr)
}

struct HeavyConstantExtractor {
    counter: usize,
    used_names: HashSet<String>,
}

impl HeavyConstantExtractor {
    fn next_name(&mut self, expr: &PseudoExpr) -> String {
        let prefix = match expr {
            PseudoExpr::ByteArray(_) => "bytes_const",
            _ => "data_const",
        };
        loop {
            let name = format!("{}_{}", prefix, self.counter);
            self.counter += 1;
            if self.used_names.insert(name.clone()) {
                return name;
            }
        }
    }

    fn wrap_side(
        &mut self,
        op: BinaryOp,
        literal: PseudoExpr,
        other: PseudoExpr,
        literal_on_left: bool,
    ) -> PseudoExpr {
        let binder = Binder::new(self.next_name(&literal), VarId::fresh_binding());
        let replacement = PseudoExpr::var_with_id(binder.name.clone(), binder.id);
        let rebuilt = if literal_on_left {
            PseudoExpr::BinOp {
                op,
                left: PBox::new(replacement),
                right: PBox::new(other),
            }
        } else {
            PseudoExpr::BinOp {
                op,
                left: PBox::new(other),
                right: PBox::new(replacement),
            }
        };

        PseudoExpr::let_bind_with_id(binder.name, binder.id, literal, rebuilt)
    }
}

impl ExprFolder for HeavyConstantExtractor {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn post_binop(&mut self, op: BinaryOp, left: PseudoExpr, right: PseudoExpr) -> PseudoExpr {
        if is_heavy_static_expr(&left) {
            return self.wrap_side(op, left, right, true);
        }
        if is_heavy_static_expr(&right) {
            return self.wrap_side(op, right, left, false);
        }

        PseudoExpr::BinOp {
            op,
            left: PBox::new(left),
            right: PBox::new(right),
        }
    }
}

fn is_heavy_static_expr(expr: &PseudoExpr) -> bool {
    is_static_data_expr(expr) && (expr_node_count(expr) >= 6 || contains_long_bytearray(expr))
}

fn is_static_data_expr(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit => {}
            PseudoExpr::Data(data) => {
                if !is_static_data_value(data) {
                    return false;
                }
            }
            PseudoExpr::List { elements, tail } => {
                if tail.is_some() {
                    return false;
                }
                pending.extend(elements);
            }
            PseudoExpr::Tuple(items) => pending.extend(items),
            PseudoExpr::Pair(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields),
            PseudoExpr::BuiltinCall { name, args } => {
                if *name != crate::BuiltinId::DataConstr {
                    return false;
                }
                pending.extend(args);
            }
            _ => return false,
        }
    }
    true
}

fn is_static_data_value(data: &PseudoData) -> bool {
    match data {
        PseudoData::Integer(_) | PseudoData::ByteString(_) => true,
        PseudoData::List(items) => items.iter().all(is_static_data_value),
        PseudoData::Map(entries) => entries
            .iter()
            .all(|(key, value)| is_static_data_value(key) && is_static_data_value(value)),
        PseudoData::Constr(_, fields) => fields.iter().all(is_static_data_value),
    }
}

fn expr_node_count(expr: &PseudoExpr) -> usize {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    let mut count = 0usize;
    while let Some(current) = pending.pop() {
        count += 1;
        match current {
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
            | PseudoExpr::Force(body) => pending.push(body),
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args);
            }
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
                pending.extend(clauses.iter().map(|clause| &clause.body));
            }
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements);
                if let Some(tail) = tail {
                    pending.push(tail);
                }
            }
            PseudoExpr::Tuple(items) => pending.extend(items),
            PseudoExpr::Pair(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields),
            PseudoExpr::Data(data) => count += data_node_count(data),
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args),
            PseudoExpr::Trace { message, value } => {
                pending.push(message);
                pending.push(value);
            }
        }
    }
    count
}

fn data_node_count(data: &PseudoData) -> usize {
    match data {
        PseudoData::Integer(_) | PseudoData::ByteString(_) => 1,
        PseudoData::List(items) => 1 + items.iter().map(data_node_count).sum::<usize>(),
        PseudoData::Map(entries) => {
            1 + entries
                .iter()
                .map(|(key, value)| data_node_count(key) + data_node_count(value))
                .sum::<usize>()
        }
        PseudoData::Constr(_, fields) => 1 + fields.iter().map(data_node_count).sum::<usize>(),
    }
}

fn contains_long_bytearray(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::ByteArray(bytes) => {
                if bytes.len() >= 20 {
                    return true;
                }
            }
            PseudoExpr::Data(data) => {
                if data_contains_long_bytearray(data) {
                    return true;
                }
            }
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements);
                if let Some(tail) = tail {
                    pending.push(tail);
                }
            }
            PseudoExpr::Tuple(items) => pending.extend(items),
            PseudoExpr::Pair(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields),
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args),
            _ => {}
        }
    }
    false
}

fn data_contains_long_bytearray(data: &PseudoData) -> bool {
    match data {
        PseudoData::ByteString(bytes) => bytes.len() >= 20,
        PseudoData::List(items) => items.iter().any(data_contains_long_bytearray),
        PseudoData::Map(entries) => entries.iter().any(|(key, value)| {
            data_contains_long_bytearray(key) || data_contains_long_bytearray(value)
        }),
        PseudoData::Constr(_, fields) => fields.iter().any(data_contains_long_bytearray),
        PseudoData::Integer(_) => false,
    }
}

#[cfg(test)]
mod tests;
