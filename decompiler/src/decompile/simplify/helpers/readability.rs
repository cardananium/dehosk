use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{BinaryOp, PseudoExpr};

mod data_conversion_cse;
mod metrics;
mod names;

use super::Simplifier;

impl Simplifier {
    /// Flatten nested && into a flat list, then combine.
    pub(crate) fn flatten_and(expr: PseudoExpr) -> PseudoExpr {
        let mut parts = Vec::new();
        Self::collect_and_parts(&expr, &mut parts);

        if parts.len() <= 1 {
            return expr;
        }

        let mut result = parts.remove(0);
        for part in parts {
            result = PseudoExpr::BinOp {
                op: BinaryOp::And,
                left: PBox::new(result),
                right: PBox::new(part),
            };
        }
        result
    }

    /// Collect all parts of a nested && expression.
    pub(crate) fn collect_and_parts(expr: &PseudoExpr, parts: &mut Vec<PseudoExpr>) {
        let mut pending = vec![expr];
        while let Some(cur) = pending.pop() {
            if let PseudoExpr::BinOp {
                op: BinaryOp::And,
                left,
                right,
            } = cur
            {
                pending.push(right);
                pending.push(left);
            } else {
                parts.push(cur.clone());
            }
        }
    }

    /// Readability pipeline for long && chains, applied in order:
    /// 1. CSE for repeated Data.to_* conversions in strict conjunction parts.
    /// 2. Extraction of large Data.Constr literals into expected_data_N lets.
    /// 3. Naming of complex boolean checks into *_ok lets (short-circuit preserving).
    pub(crate) fn improve_and_chain_readability(&mut self, expr: PseudoExpr) -> PseudoExpr {
        let flattened = Self::flatten_and(expr);

        let mut parts = Vec::new();
        Self::collect_and_parts_owned(flattened, &mut parts);

        if parts.is_empty() {
            return PseudoExpr::Bool(true);
        }
        if parts.len() == 1 {
            return parts.remove(0);
        }

        let parts = self.cse_repeated_data_conversions_in_and_parts(parts);
        let extracted = self.extract_large_data_literals_from_and(Self::build_and_chain(parts));
        self.name_long_and_conditions(extracted)
    }

    /// Extract a large static Data.Constr literal from a standalone equality:
    /// the `&&`-chain extraction's counterpart for if/expect conditions.
    pub(crate) fn extract_large_data_literal_from_eq(&mut self, expr: PseudoExpr) -> PseudoExpr {
        let PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            mut left,
            mut right,
        } = expr
        else {
            return expr;
        };

        let mut used_names = HashSet::new();
        Self::collect_var_names(left.as_ref(), &mut used_names);
        Self::collect_var_names(right.as_ref(), &mut used_names);

        if Self::should_extract_data_literal(right.as_ref(), left.as_ref()) {
            let fresh = Self::fresh_readability_name(&mut used_names, "expected_data".to_string());
            let binder = self.fresh_synthetic_binder(&fresh);
            let literal = (*right).clone();
            right = PBox::new(self.make_var_for_binder(&binder));
            return self.make_let_for_binder(
                binder,
                literal,
                PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left,
                    right,
                },
            );
        }

        if Self::should_extract_data_literal(left.as_ref(), right.as_ref()) {
            let fresh = Self::fresh_readability_name(&mut used_names, "expected_data".to_string());
            let binder = self.fresh_synthetic_binder(&fresh);
            let literal = (*left).clone();
            left = PBox::new(self.make_var_for_binder(&binder));
            return self.make_let_for_binder(
                binder,
                literal,
                PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left,
                    right,
                },
            );
        }

        PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left,
            right,
        }
    }

    fn name_long_and_conditions(&mut self, expr: PseudoExpr) -> PseudoExpr {
        let mut parts = Vec::new();
        Self::collect_and_parts_owned(expr, &mut parts);

        if parts.len() < 4 {
            return Self::build_and_chain(parts);
        }

        let mut used_names = HashSet::new();
        for part in &parts {
            Self::collect_var_names(part, &mut used_names);
        }

        let mut bindings: HashMap<usize, (crate::pseudo::ast::Binder, PseudoExpr)> = HashMap::new();
        for (idx, part) in parts.iter_mut().enumerate().skip(1) {
            if !Self::should_name_and_condition(part) {
                continue;
            }

            let base = self
                .condition_name_stem(part)
                .unwrap_or_else(|| format!("condition_{}", idx + 1));
            let binding_name =
                Self::fresh_readability_name(&mut used_names, format!("{}_ok", base));
            let binder = self.fresh_synthetic_binder(&binding_name);
            let replacement = self.make_var_for_binder(&binder);
            let original = std::mem::replace(part, replacement);
            bindings.insert(idx, (binder, original));
        }

        if bindings.is_empty() {
            return Self::build_and_chain(parts);
        }

        let last_idx = parts.len() - 1;
        let mut suffix = parts
            .pop()
            .expect("parts cannot be empty after len() guard");

        if let Some((binder, binding_value)) = bindings.remove(&last_idx) {
            suffix = self.make_let_for_binder(binder, binding_value, suffix);
        }

        for idx in (1..parts.len()).rev() {
            let chain = PseudoExpr::BinOp {
                op: BinaryOp::And,
                left: PBox::new(parts[idx].clone()),
                right: PBox::new(suffix),
            };
            if let Some((binder, binding_value)) = bindings.remove(&idx) {
                suffix = self.make_let_for_binder(binder, binding_value, chain);
            } else {
                suffix = chain;
            }
        }

        PseudoExpr::BinOp {
            op: BinaryOp::And,
            left: PBox::new(parts[0].clone()),
            right: PBox::new(suffix),
        }
    }

    fn should_name_and_condition(expr: &PseudoExpr) -> bool {
        if matches!(
            expr,
            PseudoExpr::Var { .. }
                | PseudoExpr::Bool(_)
                | PseudoExpr::Int(_)
                | PseudoExpr::FieldAccess { .. }
                | PseudoExpr::IndexAccess { .. }
        ) {
            return false;
        }

        if Self::expr_node_count(expr) >= 8 {
            return true;
        }

        if let PseudoExpr::BinOp {
            op:
                BinaryOp::Eq
                | BinaryOp::Neq
                | BinaryOp::Lt
                | BinaryOp::Lte
                | BinaryOp::Gt
                | BinaryOp::Gte,
            left,
            right,
        } = expr
        {
            return Self::expr_node_count(left) >= 4 || Self::expr_node_count(right) >= 4;
        }

        Self::contains_call(expr)
    }

    fn condition_name_stem(&self, expr: &PseudoExpr) -> Option<String> {
        enum Task<'a> {
            Eval(&'a PseudoExpr),
            OrElse(&'a PseudoExpr),
            WrapIndex(usize),
        }

        let mut tasks = vec![Task::Eval(expr)];
        let mut values: Vec<Option<String>> = Vec::new();

        while let Some(task) = tasks.pop() {
            match task {
                Task::Eval(e) => match e {
                    PseudoExpr::BinOp { left, right, .. } => {
                        tasks.push(Task::OrElse(right));
                        tasks.push(Task::Eval(left));
                    }
                    PseudoExpr::Var { name, .. } => {
                        values.push(if Self::is_generated_temp_name(name) {
                            None
                        } else {
                            Some(Self::sanitize_name_stem(name))
                        });
                    }
                    PseudoExpr::FieldAccess { selector, .. } => {
                        values.push(Some(Self::sanitize_name_stem(selector.as_pretty_name())));
                    }
                    PseudoExpr::IndexAccess { collection, index } => {
                        tasks.push(Task::WrapIndex(*index));
                        tasks.push(Task::Eval(collection));
                    }
                    PseudoExpr::BuiltinCall { name, .. } => {
                        values.push(Self::builtin_name_stem(name));
                    }
                    PseudoExpr::Apply { function, .. } => {
                        tasks.push(Task::Eval(function));
                    }
                    _ => values.push(None),
                },
                Task::OrElse(right) => {
                    let left_val = values.pop().expect("left result missing");
                    if left_val.is_some() {
                        values.push(left_val);
                    } else {
                        tasks.push(Task::Eval(right));
                    }
                }
                Task::WrapIndex(index) => {
                    let base = values.pop().expect("collection result missing");
                    values.push(base.map(|b| format!("{}_{}", b, index)));
                }
            }
        }

        values
            .pop()
            .expect("condition_name_stem produced no result")
    }

    pub(crate) fn builtin_name_stem(name: &str) -> Option<String> {
        let stem = match name {
            "Hash.blake2b_256" => "hash".to_string(),
            "Data.to_map" | "Data.un_map" => "map".to_string(),
            "Data.to_list" | "Data.un_list" => "list".to_string(),
            "Data.to_bytes" | "Data.un_bytearray" => "bytes".to_string(),
            "Data.to_int" | "Data.un_int" => "int".to_string(),
            _ => {
                let raw = name.rsplit('.').next().unwrap_or(name);
                Self::sanitize_name_stem(raw)
            }
        };
        if stem.is_empty() { None } else { Some(stem) }
    }

    fn contains_call(expr: &PseudoExpr) -> bool {
        let mut pending = vec![expr];
        while let Some(cur) = pending.pop() {
            match cur {
                PseudoExpr::Apply { .. } | PseudoExpr::BuiltinCall { .. } => return true,
                PseudoExpr::Lambda { body, .. }
                | PseudoExpr::RecFn { body, .. }
                | PseudoExpr::Delay(body)
                | PseudoExpr::Force(body) => pending.push(body),
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
                    for c in clauses.iter().rev() {
                        pending.push(&c.body);
                        if let Some(guard) = c.guard.as_ref() {
                            pending.push(guard);
                        }
                    }
                    pending.push(subject);
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail.as_ref() {
                        pending.push(t);
                    }
                    for e in elements.iter().rev() {
                        pending.push(e);
                    }
                }
                PseudoExpr::Tuple(items) => {
                    for item in items.iter().rev() {
                        pending.push(item);
                    }
                }
                PseudoExpr::Pair(a, b)
                | PseudoExpr::BinOp {
                    left: a, right: b, ..
                } => {
                    pending.push(b);
                    pending.push(a);
                }
                PseudoExpr::UnOp { operand, .. }
                | PseudoExpr::FieldAccess {
                    record: operand, ..
                }
                | PseudoExpr::IndexAccess {
                    collection: operand,
                    ..
                } => pending.push(operand),
                PseudoExpr::Constr { fields, .. } => {
                    for f in fields.iter().rev() {
                        pending.push(f);
                    }
                }
                PseudoExpr::Trace { message, value } => {
                    pending.push(value);
                    pending.push(message);
                }
                _ => {}
            }
        }
        false
    }

    /// Extract large static Data.Constr literals from && comparisons into let-bindings.
    /// Example:
    ///   p == Data.Constr(...) && q
    /// becomes:
    ///   let expected_data_1 = Data.Constr(...)
    ///   p == expected_data_1 && q
    pub(crate) fn extract_large_data_literals_from_and(&mut self, expr: PseudoExpr) -> PseudoExpr {
        let mut parts = Vec::new();
        Self::collect_and_parts_owned(expr, &mut parts);

        if parts.is_empty() {
            return PseudoExpr::Bool(true);
        }
        if parts.len() == 1 {
            return parts.remove(0);
        }

        let mut bindings: Vec<(crate::pseudo::ast::Binder, PseudoExpr)> = Vec::new();
        let mut next_name_idx = 1usize;
        let mut used_names = HashSet::new();
        for part in &parts {
            Self::collect_var_names(part, &mut used_names);
        }

        for part in parts.iter_mut() {
            let PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left,
                right,
            } = part
            else {
                continue;
            };

            if Self::should_extract_data_literal(right.as_ref(), left.as_ref()) {
                let fresh = loop {
                    let candidate = format!("expected_data_{}", next_name_idx);
                    next_name_idx += 1;
                    if !used_names.contains(&candidate) {
                        break candidate;
                    }
                };
                used_names.insert(fresh.clone());
                let binder = self.fresh_synthetic_binder(&fresh);
                let literal = (**right).clone();
                **right = self.make_var_for_binder(&binder);
                bindings.push((binder, literal));
            } else if Self::should_extract_data_literal(left.as_ref(), right.as_ref()) {
                let fresh = loop {
                    let candidate = format!("expected_data_{}", next_name_idx);
                    next_name_idx += 1;
                    if !used_names.contains(&candidate) {
                        break candidate;
                    }
                };
                used_names.insert(fresh.clone());
                let binder = self.fresh_synthetic_binder(&fresh);
                let literal = (**left).clone();
                **left = self.make_var_for_binder(&binder);
                bindings.push((binder, literal));
            }
        }

        let mut rebuilt = Self::build_and_chain(parts);
        for (binder, value) in bindings.into_iter().rev() {
            rebuilt = self.make_let_for_binder(binder, value, rebuilt);
        }
        rebuilt
    }

    fn collect_and_parts_owned(expr: PseudoExpr, parts: &mut Vec<PseudoExpr>) {
        let mut pending = vec![expr];
        while let Some(expr) = pending.pop() {
            if let PseudoExpr::BinOp {
                op: BinaryOp::And,
                left,
                right,
            } = expr
            {
                pending.push(right.into_inner());
                pending.push(left.into_inner());
            } else {
                parts.push(expr);
            }
        }
    }

    fn build_and_chain(mut parts: Vec<PseudoExpr>) -> PseudoExpr {
        let mut iter = parts.drain(..);
        let mut acc = iter
            .next()
            .expect("build_and_chain requires at least one element");
        for part in iter {
            acc = PseudoExpr::BinOp {
                op: BinaryOp::And,
                left: PBox::new(acc),
                right: PBox::new(part),
            };
        }
        acc
    }

    fn should_extract_data_literal(candidate: &PseudoExpr, peer: &PseudoExpr) -> bool {
        let is_root_data = matches!(candidate, PseudoExpr::BuiltinCall { name, .. } if *name == crate::BuiltinId::DataConstr)
            || matches!(candidate, PseudoExpr::Data(_));

        is_root_data
            && Self::static_data_expr_node_count(candidate).is_some_and(|count| count >= 12)
            && !Self::is_static_data_expr(peer)
    }
}
