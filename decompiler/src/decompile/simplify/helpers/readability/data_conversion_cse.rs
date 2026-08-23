use std::collections::HashSet;

use crate::pseudo::ast::{BinaryOp, PseudoExpr, WhenPattern};
use crate::pseudo::fold::{ExprFolder, FoldAction};

use super::Simplifier;

impl Simplifier {
    pub(super) fn cse_repeated_data_conversions_in_and_parts(
        &mut self,
        mut parts: Vec<PseudoExpr>,
    ) -> Vec<PseudoExpr> {
        loop {
            #[derive(Clone)]
            struct Occurrence {
                expr: PseudoExpr,
                part_indices: Vec<usize>,
            }

            let mut occurrences: Vec<Occurrence> = Vec::new();

            for (idx, part) in parts.iter().enumerate() {
                if Self::contains_short_circuit_binop(part) {
                    continue;
                }

                let mut candidates = Vec::new();
                Self::collect_data_conversion_candidates(part, &mut candidates);
                for candidate in candidates {
                    if let Some(existing) = occurrences
                        .iter_mut()
                        .find(|o| Self::exprs_equal(&o.expr, &candidate))
                    {
                        if !existing.part_indices.contains(&idx) {
                            existing.part_indices.push(idx);
                        }
                    } else {
                        occurrences.push(Occurrence {
                            expr: candidate,
                            part_indices: vec![idx],
                        });
                    }
                }
            }

            let mut repeated: Vec<Occurrence> = occurrences
                .into_iter()
                .filter(|o| o.part_indices.len() >= 2)
                .collect();

            repeated.sort_by(|a, b| {
                let a_first = a.part_indices.iter().min().copied().unwrap_or(usize::MAX);
                let b_first = b.part_indices.iter().min().copied().unwrap_or(usize::MAX);
                a_first
                    .cmp(&b_first)
                    .then_with(|| b.part_indices.len().cmp(&a.part_indices.len()))
            });

            let mut applied = false;
            for chosen in repeated {
                let appears_in_short_circuit_part = parts.iter().any(|part| {
                    Self::contains_short_circuit_binop(part)
                        && Self::contains_expr(part, &chosen.expr)
                });
                if appears_in_short_circuit_part {
                    continue;
                }

                let Some(first_idx) = chosen.part_indices.iter().min().copied() else {
                    continue;
                };

                let mut used_names = HashSet::new();
                for part in &parts {
                    Self::collect_var_names(part, &mut used_names);
                }

                let stem =
                    Self::data_conversion_stem(&chosen.expr).unwrap_or_else(|| "value".to_string());
                let binding_name =
                    Self::fresh_readability_name(&mut used_names, format!("{}_cache", stem));
                let binder = self.fresh_synthetic_binder(&binding_name);
                let replacement = self.make_var_for_binder(&binder);

                for part in parts.iter_mut().skip(first_idx) {
                    *part =
                        Self::replace_expr_occurrences(part.clone(), &chosen.expr, &replacement);
                }

                let suffix_parts = parts.split_off(first_idx);
                let suffix_expr = Self::build_and_chain(suffix_parts);

                parts.push(self.make_let_for_binder(binder, chosen.expr, suffix_expr));

                applied = true;
                break;
            }

            if !applied {
                break;
            }
        }

        parts
    }

    fn data_conversion_stem(expr: &PseudoExpr) -> Option<String> {
        if let PseudoExpr::BuiltinCall { name, args } = expr
            && args.len() == 1
        {
            return match name.as_str() {
                "Data.to_map" | "Data.un_map" => Some("map".to_string()),
                "Data.to_list" | "Data.un_list" => Some("list".to_string()),
                "Data.to_bytes" | "Data.un_bytearray" => Some("bytes".to_string()),
                "Data.to_int" | "Data.un_int" => Some("int".to_string()),
                _ => None,
            };
        }
        None
    }

    fn collect_data_conversion_candidates(expr: &PseudoExpr, out: &mut Vec<PseudoExpr>) {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(cur) = pending.pop() {
            if Self::is_data_conversion_candidate(cur) {
                out.push(cur.clone());
            }

            match cur {
                PseudoExpr::Lambda { body, .. }
                | PseudoExpr::RecFn { body, .. }
                | PseudoExpr::Delay(body)
                | PseudoExpr::Force(body) => pending.push(body),
                PseudoExpr::Apply { function, args } => {
                    for arg in args.iter().rev() {
                        pending.push(arg);
                    }
                    pending.push(function);
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
                PseudoExpr::List { elements, tail } => {
                    if let Some(tail) = tail {
                        pending.push(tail);
                    }
                    for element in elements.iter().rev() {
                        pending.push(element);
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
                PseudoExpr::BuiltinCall { args, .. } | PseudoExpr::Constr { fields: args, .. } => {
                    for arg in args.iter().rev() {
                        pending.push(arg);
                    }
                }
                PseudoExpr::Trace { message, value } => {
                    pending.push(value);
                    pending.push(message);
                }
                _ => {}
            }
        }
    }

    fn is_data_conversion_candidate(expr: &PseudoExpr) -> bool {
        matches!(
            expr,
            PseudoExpr::BuiltinCall { name, args }
                if args.len() == 1
                    && matches!(
                        name.as_str(),
                        "Data.to_map"
                            | "Data.un_map"
                            | "Data.to_list"
                            | "Data.un_list"
                            | "Data.to_bytes"
                            | "Data.un_bytearray"
                            | "Data.to_int"
                            | "Data.un_int"
                    )
                    && Self::expr_node_count(expr) >= 3
        )
    }

    fn contains_short_circuit_binop(expr: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(cur) = pending.pop() {
            if let PseudoExpr::BinOp {
                op: BinaryOp::And | BinaryOp::Or,
                ..
            } = cur
            {
                return true;
            }

            match cur {
                PseudoExpr::Lambda { body, .. }
                | PseudoExpr::RecFn { body, .. }
                | PseudoExpr::Delay(body)
                | PseudoExpr::Force(body) => pending.push(body),
                PseudoExpr::Apply { function, args } => {
                    for arg in args.iter().rev() {
                        pending.push(arg);
                    }
                    pending.push(function);
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
                PseudoExpr::List { elements, tail } => {
                    if let Some(tail) = tail {
                        pending.push(tail);
                    }
                    for element in elements.iter().rev() {
                        pending.push(element);
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
                PseudoExpr::BuiltinCall { args, .. } | PseudoExpr::Constr { fields: args, .. } => {
                    for arg in args.iter().rev() {
                        pending.push(arg);
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

    fn contains_expr(haystack: &PseudoExpr, needle: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![haystack];
        while let Some(cur) = pending.pop() {
            if Self::exprs_equal(cur, needle) {
                return true;
            }

            match cur {
                PseudoExpr::Lambda { body, .. }
                | PseudoExpr::RecFn { body, .. }
                | PseudoExpr::Delay(body)
                | PseudoExpr::Force(body) => pending.push(body),
                PseudoExpr::Apply { function, args } => {
                    for arg in args.iter().rev() {
                        pending.push(arg);
                    }
                    pending.push(function);
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
                PseudoExpr::List { elements, tail } => {
                    if let Some(tail) = tail {
                        pending.push(tail);
                    }
                    for element in elements.iter().rev() {
                        pending.push(element);
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
                PseudoExpr::BuiltinCall { args, .. } | PseudoExpr::Constr { fields: args, .. } => {
                    for arg in args.iter().rev() {
                        pending.push(arg);
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

    fn replace_expr_occurrences(
        expr: PseudoExpr,
        target: &PseudoExpr,
        replacement: &PseudoExpr,
    ) -> PseudoExpr {
        struct Replacer<'a> {
            target: &'a PseudoExpr,
            replacement: &'a PseudoExpr,
        }

        impl ExprFolder for Replacer<'_> {
            fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
                if Simplifier::exprs_equal(expr, self.target) {
                    FoldAction::Replace(self.replacement.clone())
                } else {
                    FoldAction::Walk
                }
            }

            fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
                pattern
            }
        }

        Replacer {
            target,
            replacement,
        }
        .fold(expr)
    }
}
