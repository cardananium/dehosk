use std::collections::HashSet;

use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenPattern};

use super::Simplifier;

impl Simplifier {
    /// Fresh name colliding with neither `used` nor an assigned rename:
    /// appends `_1`, `_2`, etc. to `base` until one is free.
    pub(crate) fn fresh_name_for_scope(&self, used: &mut HashSet<String>, base: String) -> String {
        if !used.contains(&base) && !self.naming.renames.values().any(|v| v == &base) {
            used.insert(base.clone());
            return base;
        }
        let mut i = 1u32;
        loop {
            let candidate = format!("{}_{}", base, i);
            if !used.contains(&candidate) && !self.naming.renames.values().any(|v| v == &candidate)
            {
                used.insert(candidate.clone());
                return candidate;
            }
            i += 1;
            if i > 1000 {
                // Safety valve
                return format!("{}_{}", base, i);
            }
        }
    }

    /// Suggest a short boolean-ish name (`is_equal`, `cmp_ok`, `{fn}_result`)
    /// for an expression used as a condition; `None` if unrecognized.
    pub(crate) fn suggest_boolish_name_from_expr(expr: &PseudoExpr) -> Option<String> {
        let mut not_depth = 0usize;
        let mut cur = expr;
        while let PseudoExpr::UnOp {
            op: UnaryOp::Not,
            operand,
        } = cur
        {
            not_depth += 1;
            cur = operand;
        }
        let base = match cur {
            PseudoExpr::BinOp { op, left, .. } => {
                let prefix = match op {
                    BinaryOp::Eq | BinaryOp::Neq => "is_equal",
                    BinaryOp::Lt | BinaryOp::Lte | BinaryOp::Gt | BinaryOp::Gte => "cmp_ok",
                    _ => return None,
                };
                if let PseudoExpr::Var { name, .. } = left.as_ref() {
                    format!("{}_{}", name, prefix)
                } else {
                    prefix.to_string()
                }
            }
            PseudoExpr::Apply { function, .. } => {
                if let PseudoExpr::Var { name, .. } = function.as_ref() {
                    if name.starts_with("is_") || name.starts_with("has_") {
                        name.clone()
                    } else {
                        format!("{}_result", name)
                    }
                } else {
                    return None;
                }
            }
            PseudoExpr::When { .. } | PseudoExpr::If { .. } => "condition_ok".to_string(),
            _ => return None,
        };
        let mut name = base;
        for _ in 0..not_depth {
            name = format!("not_{}", name);
        }
        Some(name)
    }

    /// Suggest a prettier name for a generated temporary binding, inferred
    /// from the value expression; `None` when the current name is fine.
    pub(crate) fn suggest_generated_binding_name(
        &self,
        name: &str,
        value: &PseudoExpr,
        body: &PseudoExpr,
    ) -> Option<String> {
        if !Self::is_generated_temp_name(name) {
            return None;
        }

        match value {
            PseudoExpr::BinOp {
                op:
                    BinaryOp::Eq
                    | BinaryOp::Neq
                    | BinaryOp::Lt
                    | BinaryOp::Lte
                    | BinaryOp::Gt
                    | BinaryOp::Gte,
                left,
                ..
            } => {
                if let PseudoExpr::Var { name: var_name, .. } = left.as_ref() {
                    Some(format!("{}_ok", Self::sanitize_name_stem(var_name)))
                } else {
                    Some("cond_ok".to_string())
                }
            }
            PseudoExpr::BinOp { op: BinaryOp::And | BinaryOp::Or, left, .. } => {
                if let PseudoExpr::Var { name: var_name, .. } = left.as_ref() {
                    Some(format!("{}_ok", Self::sanitize_name_stem(var_name)))
                } else {
                    Some("cond_ok".to_string())
                }
            }
            PseudoExpr::FieldAccess { selector, .. } => {
                Some(Self::sanitize_name_stem(selector.as_pretty_name()))
            }
            PseudoExpr::IndexAccess { collection, index } => {
                if let PseudoExpr::Var { name: var_name, .. } = collection.as_ref() {
                    Some(format!("{}_{}", Self::sanitize_name_stem(var_name), index))
                } else {
                    Some(format!("item_{}", index))
                }
            }
            PseudoExpr::BuiltinCall { name: bname, args } => {
                Self::builtin_name_stem(bname).map(|stem| {
                    if args.len() == 1
                        && let PseudoExpr::Var { name: ref arg_name, .. } = args[0] {
                            // Skip prepending when the source var is a
                            // synthetic alias (`field_N`, `fields_N`,
                            // `item_N`, `payload`): Cardano-naming resolves
                            // those *after* this stem locks in, so
                            // `field_2_list` would not match the rendered
                            // subject (`outputs`). The bare stem (`list`)
                            // lets the dedup pass below assign a unique
                            // semantic name, as `inputs_list` does.
                            if Self::is_synthetic_alias_name(arg_name) {
                                return stem;
                            }
                            return format!("{}_{}", arg_name, stem);
                        }
                    stem
                })
            }
            PseudoExpr::Apply { function, .. } => {
                if let PseudoExpr::Var { name: fn_name, .. } = function.as_ref() {
                    if fn_name.starts_with("expect!") {
                        return None;
                    }
                    // Mirror `rename.rs::hint_from_value` — no `{fn}_result`
                    // for bare generic helper names like `f` / `f_2`. Helper
                    // hoisting promotes `f_N` to top level and rearranges its
                    // scope, while an `f_N_result_M` binding stays in the inner
                    // scope and can be left dangling in the render.
                    if Self::is_bare_generic_fn_name(fn_name) {
                        return None;
                    }
                    Some(format!("{}_result", Self::sanitize_name_stem(fn_name)))
                } else {
                    None
                }
            }
            PseudoExpr::Lambda { params, .. } if params.len() == 2 => {
                if Self::is_fst_selector(value) {
                    Some("choose_fst".to_string())
                } else if Self::is_snd_selector(value) {
                    Some("choose_snd".to_string())
                } else {
                    None
                }
            }
            PseudoExpr::Delay(inner) => {
                if let PseudoExpr::Lambda { params, .. } = inner.as_ref()
                    && params.len() == 2 {
                        if Self::is_fst_selector(inner) {
                            return Some("choose_fst".to_string());
                        }
                        if Self::is_snd_selector(inner) {
                            return Some("choose_snd".to_string());
                        }
                    }
                None
            }
            _ => None,
        }
        .or_else(|| {
            if let PseudoExpr::Lambda { params, body: lam_body } = value {
                if params.len() == 1 && params[0] != "_" {
                    match lam_body.as_ref() {
                        PseudoExpr::FieldAccess { record, selector, .. } => {
                            if matches!(record.as_ref(), PseudoExpr::Var { name: n, .. } if n == &params[0]) {
                                return Some(format!(
                                    "get_{}",
                                    Self::sanitize_name_stem(selector.as_pretty_name())
                                ));
                            }
                        }
                        PseudoExpr::IndexAccess { collection, index } => {
                            if matches!(collection.as_ref(), PseudoExpr::Var { name: n, .. } if n == &params[0]) {
                                return Some(format!("get_field_{}", index));
                            }
                        }
                        PseudoExpr::BuiltinCall { name: bname, args } if args.len() == 1 => {
                            if matches!(&args[0], PseudoExpr::Var { name: n, .. } if n == &params[0])
                                && let Some(stem) = Self::builtin_name_stem(bname) {
                                    return Some(stem);
                                }
                        }
                        _ => {}
                    }
                }

                if params.len() == 2 && params.iter().all(|p| p != "_")
                    && let PseudoExpr::BinOp { op, left, right } = lam_body.as_ref() {
                        let left_is_param = matches!(left.as_ref(), PseudoExpr::Var { name: n, .. } if params.iter().any(|p| p == n.as_str()));
                        let right_is_param = matches!(right.as_ref(), PseudoExpr::Var { name: n, .. } if params.iter().any(|p| p == n.as_str()));
                        if left_is_param && right_is_param {
                            match op {
                                BinaryOp::Eq | BinaryOp::Neq => return Some("eq".to_string()),
                                BinaryOp::Lt | BinaryOp::Lte | BinaryOp::Gt | BinaryOp::Gte => {
                                    return Some("compare".to_string());
                                }
                                _ => {}
                            }
                        }
                    }

                if Self::body_ends_in_fail(lam_body) {
                    return Some("assert_valid".to_string());
                }
            }

            if Self::is_used_as_if_condition(body, name)
                && let PseudoExpr::BinOp {
                    op:
                        BinaryOp::Eq
                        | BinaryOp::Neq
                        | BinaryOp::Lt
                        | BinaryOp::Lte
                        | BinaryOp::Gt
                        | BinaryOp::Gte,
                    ..
                } = value
                {
                    return Some("condition_ok".to_string());
                }

            None
        })
    }

    /// Check if `name` appears as the condition of an `If` expression in `body`.
    fn is_used_as_if_condition(body: &PseudoExpr, name: &str) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![body];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    if matches!(condition.as_ref(), PseudoExpr::Var { name: n, .. } if n == name) {
                        return true;
                    }
                    pending.push(condition);
                    pending.push(then_branch);
                    pending.push(else_branch);
                }
                PseudoExpr::Let { value, body, .. } => {
                    pending.push(value);
                    pending.push(body);
                }
                PseudoExpr::When {
                    subject, clauses, ..
                } => {
                    pending.push(subject);
                    for c in clauses {
                        pending.push(&c.body);
                    }
                }
                _ => {}
            }
        }
        false
    }

    /// Synthetic placeholder names introduced by simplify aliases:
    /// `field_N`, `fields_N`, `item_N`, `payload`. These are not stable
    /// across the Cardano-context renaming step, so they must not be
    /// used as stems for derived names like `{src}_list`.
    fn is_synthetic_alias_name(name: &str) -> bool {
        if name == "payload" {
            return true;
        }
        if let Some(suffix) = name
            .strip_prefix("field_")
            .or_else(|| name.strip_prefix("fields_"))
            .or_else(|| name.strip_prefix("item_"))
        {
            return !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit());
        }
        false
    }

    /// Match the decompiler's bare generic-helper names: `f`, `f_2`, `f_3`, …
    /// and the recursive variants `rec_fn_N` / `self_fn_N`.
    ///
    /// These are early-rename placeholders for top-level helpers. Helper
    /// hoisting later promotes them and rearranges scopes, so a
    /// `{fn}_result_M` alias tied to an inner scope can be left dangling.
    pub(crate) fn is_bare_generic_fn_name(name: &str) -> bool {
        if name == "f" {
            return true;
        }
        if name.starts_with("f_") && name.len() > 2 && name[2..].chars().all(|c| c.is_ascii_digit())
        {
            return true;
        }
        if let Some(suffix) = name
            .strip_prefix("rec_fn_")
            .or_else(|| name.strip_prefix("self_fn_"))
        {
            return !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit());
        }
        false
    }

    /// Check if a lambda body ends in fail/error (assertion pattern).
    fn body_ends_in_fail(body: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![body];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Error { .. } => return true,
                PseudoExpr::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    pending.push(then_branch);
                    pending.push(else_branch);
                }
                PseudoExpr::Let { body, .. } => pending.push(body),
                _ => {}
            }
        }
        false
    }

    /// Collect all variable names bound by a when pattern.
    pub(crate) fn pattern_bound_vars(pattern: &WhenPattern) -> Vec<String> {
        let mut vars = Vec::new();
        match pattern {
            WhenPattern::Constructor { fields, .. } => {
                for f in fields {
                    if f != "_" {
                        vars.push(f.to_string());
                    }
                }
            }
            WhenPattern::List { elements, tail } => {
                for e in elements {
                    if e != "_" {
                        vars.push(e.to_string());
                    }
                }
                if let Some(t) = tail
                    && t != "_"
                {
                    vars.push(t.to_string());
                }
            }
            WhenPattern::Var(name) => {
                if name != "_" {
                    vars.push(name.to_string());
                }
            }
            WhenPattern::Tuple(fields) => {
                for f in fields {
                    if f != "_" {
                        vars.push(f.to_string());
                    }
                }
            }
            WhenPattern::Pair(a, b) => {
                if a != "_" {
                    vars.push(a.to_string());
                }
                if b != "_" {
                    vars.push(b.to_string());
                }
            }
            WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
        }
        vars
    }

    pub(crate) fn pattern_binder_named(pattern: &WhenPattern, target: &str) -> Option<Binder> {
        match pattern {
            WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => fields
                .iter()
                .find(|binder| binder.as_str() == target)
                .cloned(),
            WhenPattern::List { elements, tail } => elements
                .iter()
                .chain(tail.iter())
                .find(|binder| binder.as_str() == target)
                .cloned(),
            WhenPattern::Var(binder) if binder.as_str() == target => Some(binder.clone()),
            WhenPattern::Pair(a, b) => [a, b]
                .into_iter()
                .find(|binder| binder.as_str() == target)
                .cloned(),
            WhenPattern::Wildcard | WhenPattern::Literal(_) | WhenPattern::Var(_) => None,
        }
    }

    /// Rename a variable in a when pattern.
    pub(crate) fn rename_in_pattern(pattern: &WhenPattern, old: &str, new: &str) -> WhenPattern {
        match pattern {
            WhenPattern::Constructor {
                type_hint,
                tag,
                fields,
                shape,
            } => WhenPattern::Constructor {
                type_hint: type_hint.clone(),
                tag: *tag,
                fields: fields
                    .iter()
                    .map(|f| if f == old { f.renamed(new) } else { f.clone() })
                    .collect(),
                shape: *shape,
            },
            WhenPattern::List { elements, tail } => WhenPattern::List {
                elements: elements
                    .iter()
                    .map(|e| if e == old { e.renamed(new) } else { e.clone() })
                    .collect(),
                tail: tail
                    .as_ref()
                    .map(|t| if t == old { t.renamed(new) } else { t.clone() }),
            },
            WhenPattern::Var(name) => {
                if name == old {
                    WhenPattern::Var(name.renamed(new))
                } else {
                    pattern.clone()
                }
            }
            WhenPattern::Tuple(fields) => WhenPattern::Tuple(
                fields
                    .iter()
                    .map(|f| if f == old { f.renamed(new) } else { f.clone() })
                    .collect(),
            ),
            WhenPattern::Pair(a, b) => WhenPattern::Pair(
                if a == old { a.renamed(new) } else { a.clone() },
                if b == old { b.renamed(new) } else { b.clone() },
            ),
            WhenPattern::Wildcard | WhenPattern::Literal(_) => pattern.clone(),
        }
    }
}
