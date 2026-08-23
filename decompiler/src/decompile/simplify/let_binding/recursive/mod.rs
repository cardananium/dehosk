use crate::pseudo::ast::PBox;
use std::rc::Rc;

use super::Simplifier;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum FreeCaptureKey {
    Id(VarId),
    CompatName(String),
}

impl Simplifier {
    pub(super) fn reorder_promoted_rec_call_args(
        expr: &PseudoExpr,
        fn_name: &str,
        fn_id: VarId,
        expected_arity: usize,
        outer_params: &[Binder],
        mapped_outer_params: &[String],
        extra_outer_params: &[Binder],
    ) -> PseudoExpr {
        if outer_params.len() == expected_arity || mapped_outer_params.len() != expected_arity {
            return expr.clone();
        }

        struct ReorderPromotedRecCallArgs<'a> {
            fn_name: &'a str,
            fn_id: VarId,
            expected_arity: usize,
            outer_params: &'a [Binder],
            mapped_outer_params: &'a [String],
            extra_outer_params: &'a [Binder],
            blocked_depth: usize,
        }

        impl ExprFolder for ReorderPromotedRecCallArgs<'_> {
            // Folded flat: this implementation overrides none of
            // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
            // can reassemble a `when` itself instead of recursing through
            // the hook once per nesting level.
            fn machine_folds_when(&self) -> bool {
                true
            }
            fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
                if params.iter().any(|param| param == self.fn_name) {
                    self.blocked_depth += 1;
                }
                params.to_vec()
            }

            fn exit_lambda(&mut self, params: &[Binder]) {
                if params.iter().any(|param| param == self.fn_name) {
                    self.blocked_depth -= 1;
                }
            }

            fn enter_recfn(
                &mut self,
                name: &crate::pseudo::ast::Binder,
                params: &[crate::pseudo::ast::Binder],
            ) -> (crate::pseudo::ast::Binder, Vec<crate::pseudo::ast::Binder>) {
                if name == self.fn_name || params.iter().any(|param| param == self.fn_name) {
                    self.blocked_depth += 1;
                }
                (name.clone(), params.to_vec())
            }

            fn exit_recfn(
                &mut self,
                name: &crate::pseudo::ast::Binder,
                params: &[crate::pseudo::ast::Binder],
            ) {
                if name == self.fn_name || params.iter().any(|param| param == self.fn_name) {
                    self.blocked_depth -= 1;
                }
            }

            fn enter_let(
                &mut self,
                name: &str,
                _id: &Option<VarId>,
                _value: &PseudoExpr,
            ) -> String {
                if name == self.fn_name {
                    self.blocked_depth += 1;
                }
                name.to_string()
            }

            fn exit_let(&mut self, name: &str) {
                if name == self.fn_name {
                    self.blocked_depth -= 1;
                }
            }

            fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
                if self.blocked_depth == 0
                    && matches!(&function, PseudoExpr::Var { name, id, .. } if Simplifier::promoted_rec_ref_matches(name, *id, self.fn_name, self.fn_id))
                    && args.len() == self.expected_arity
                {
                    enum ArgSource {
                        Existing(usize),
                        Extra(Binder),
                    }

                    let mut arg_plan = Vec::with_capacity(self.outer_params.len());
                    let mut used_inner_indices = std::collections::HashSet::new();

                    for outer_param in self.outer_params {
                        if let Some(inner_idx) = self
                            .mapped_outer_params
                            .iter()
                            .position(|mapped| mapped == outer_param.as_str())
                        {
                            if !used_inner_indices.insert(inner_idx) {
                                return PseudoExpr::Apply {
                                    function: PBox::new(function),
                                    args: args.into(),
                                };
                            }
                            arg_plan.push(ArgSource::Existing(inner_idx));
                            continue;
                        }

                        if let Some(extra_param) = self
                            .extra_outer_params
                            .iter()
                            .find(|extra| extra.as_str() == outer_param.as_str())
                        {
                            arg_plan.push(ArgSource::Extra(extra_param.clone()));
                            continue;
                        }

                        return PseudoExpr::Apply {
                            function: PBox::new(function),
                            args: args.into(),
                        };
                    }

                    let mut arg_slots = args.into_iter().map(Some).collect::<Vec<_>>();
                    let mut reordered_args = Vec::with_capacity(self.outer_params.len());

                    for arg_source in arg_plan {
                        match arg_source {
                            ArgSource::Existing(inner_idx) => reordered_args.push(
                                arg_slots[inner_idx]
                                    .take()
                                    .expect("promoted recursive call arg should be available"),
                            ),
                            ArgSource::Extra(extra_param) => reordered_args.push(
                                PseudoExpr::var_with_id(extra_param.as_str(), extra_param.id),
                            ),
                        }
                    }

                    PseudoExpr::Apply {
                        function: PBox::new(function),
                        args: reordered_args.into(),
                    }
                } else {
                    PseudoExpr::Apply {
                        function: PBox::new(function),
                        args: args.into(),
                    }
                }
            }
        }

        ReorderPromotedRecCallArgs {
            fn_name,
            fn_id,
            expected_arity,
            outer_params,
            mapped_outer_params,
            extra_outer_params,
            blocked_depth: 0,
        }
        .fold(expr.clone())
    }

    fn promoted_rec_ref_matches(
        name: &str,
        id: Option<VarId>,
        fn_name: &str,
        fn_id: VarId,
    ) -> bool {
        // Strip compat ids on the ref-id side with `.get()` so a Var
        // carrying a compat call-id reads as "no specific binder" and
        // falls back to name matching; unstripped,
        // `(Some(compat), Some(auth))` compares as unequal ids and the
        // call site never matches.
        crate::decompile::var_match::refs_match(name, id.get(), fn_name, fn_id.get())
    }

    fn promoted_rec_binding_ref_matches(
        name: &str,
        id: Option<VarId>,
        fn_name: &str,
        let_id: Option<VarId>,
        rec_id: VarId,
    ) -> bool {
        // Strip compat ids via `.get()` on the ref-id
        // side, same as `promoted_rec_ref_matches`.
        crate::decompile::var_match::refs_match(name, id.get(), fn_name, let_id.get())
            || crate::decompile::var_match::refs_match(name, id.get(), fn_name, rec_id.get())
    }

    fn insert_free_capture_key(
        keys: &mut std::collections::HashSet<FreeCaptureKey>,
        name: &str,
        id: VarId,
    ) {
        if name == "_" {
            return;
        }

        if let Some(id) = id.get() {
            keys.insert(FreeCaptureKey::Id(id));
        }
        keys.insert(FreeCaptureKey::CompatName(name.to_string()));
    }

    fn collect_pattern_free_capture_keys(
        pattern: &WhenPattern,
        keys: &mut std::collections::HashSet<FreeCaptureKey>,
    ) {
        match pattern {
            WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                for binder in fields {
                    Self::insert_free_capture_key(keys, binder.as_str(), binder.id);
                }
            }
            WhenPattern::List { elements, tail } => {
                for binder in elements {
                    Self::insert_free_capture_key(keys, binder.as_str(), binder.id);
                }
                if let Some(binder) = tail {
                    Self::insert_free_capture_key(keys, binder.as_str(), binder.id);
                }
            }
            WhenPattern::Pair(first, second) => {
                Self::insert_free_capture_key(keys, first.as_str(), first.id);
                Self::insert_free_capture_key(keys, second.as_str(), second.id);
            }
            WhenPattern::Var(binder) => {
                Self::insert_free_capture_key(keys, binder.as_str(), binder.id);
            }
            WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
        }
    }

    fn collect_free_var_keys(
        expr: &PseudoExpr,
        bound: &std::collections::HashSet<FreeCaptureKey>,
        free: &mut std::collections::HashSet<FreeCaptureKey>,
    ) {
        enum Step<'e> {
            Visit(
                &'e PseudoExpr,
                Rc<std::collections::HashSet<FreeCaptureKey>>,
            ),
            AfterLetValue {
                name: &'e str,
                id: Option<VarId>,
                body: &'e PseudoExpr,
                bound: Rc<std::collections::HashSet<FreeCaptureKey>>,
            },
        }

        let root_bound = Rc::new(bound.clone());
        let mut steps: Vec<Step<'_>> = vec![Step::Visit(expr, root_bound)];
        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(expr, bound) => match expr {
                    PseudoExpr::Var { name, id, .. } => {
                        let key = if let Some(id) = id.get() {
                            FreeCaptureKey::Id(id)
                        } else {
                            FreeCaptureKey::CompatName(name.clone())
                        };
                        if !bound.contains(&key) {
                            free.insert(key);
                        }
                    }
                    PseudoExpr::Lambda { params, body } => {
                        let mut lambda_bound = (*bound).clone();
                        for param in params {
                            Self::insert_free_capture_key(
                                &mut lambda_bound,
                                param.as_str(),
                                param.id,
                            );
                        }
                        steps.push(Step::Visit(body, Rc::new(lambda_bound)));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let mut rec_bound = (*bound).clone();
                        Self::insert_free_capture_key(&mut rec_bound, name.as_str(), name.id);
                        for param in params {
                            Self::insert_free_capture_key(&mut rec_bound, param.as_str(), param.id);
                        }
                        steps.push(Step::Visit(body, Rc::new(rec_bound)));
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                        ..
                    } => {
                        steps.push(Step::AfterLetValue {
                            name,
                            id: *id,
                            body,
                            bound: Rc::clone(&bound),
                        });
                        steps.push(Step::Visit(value, bound));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        for clause in clauses.iter().rev() {
                            let mut clause_bound = (*bound).clone();
                            if let Some(subject_name) = subject_name {
                                Self::insert_free_capture_key(
                                    &mut clause_bound,
                                    subject_name.as_str(),
                                    subject_name.id,
                                );
                            }
                            Self::collect_pattern_free_capture_keys(
                                &clause.pattern,
                                &mut clause_bound,
                            );
                            let clause_bound = Rc::new(clause_bound);
                            steps.push(Step::Visit(&clause.body, Rc::clone(&clause_bound)));
                            if let Some(guard) = &clause.guard {
                                steps.push(Step::Visit(guard, Rc::clone(&clause_bound)));
                            }
                            if let WhenPattern::Literal(literal) = &clause.pattern {
                                steps.push(Step::Visit(literal, Rc::clone(&bound)));
                            }
                        }
                        steps.push(Step::Visit(subject, bound));
                    }
                    PseudoExpr::Apply { function, args } => {
                        for arg in args.iter().rev() {
                            steps.push(Step::Visit(arg, Rc::clone(&bound)));
                        }
                        steps.push(Step::Visit(function, bound));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        steps.push(Step::Visit(else_branch, Rc::clone(&bound)));
                        steps.push(Step::Visit(then_branch, Rc::clone(&bound)));
                        steps.push(Step::Visit(condition, bound));
                    }
                    PseudoExpr::List { elements, tail } => {
                        if let Some(tail) = tail {
                            steps.push(Step::Visit(tail, Rc::clone(&bound)));
                        }
                        for element in elements.iter().rev() {
                            steps.push(Step::Visit(element, Rc::clone(&bound)));
                        }
                    }
                    PseudoExpr::Tuple(elements) => {
                        for element in elements.iter().rev() {
                            steps.push(Step::Visit(element, Rc::clone(&bound)));
                        }
                    }
                    PseudoExpr::Pair(left, right) | PseudoExpr::BinOp { left, right, .. } => {
                        steps.push(Step::Visit(right, Rc::clone(&bound)));
                        steps.push(Step::Visit(left, bound));
                    }
                    PseudoExpr::UnOp { operand, .. }
                    | PseudoExpr::FieldAccess {
                        record: operand, ..
                    }
                    | PseudoExpr::IndexAccess {
                        collection: operand,
                        ..
                    }
                    | PseudoExpr::Delay(operand)
                    | PseudoExpr::Force(operand) => {
                        steps.push(Step::Visit(operand, bound));
                    }
                    PseudoExpr::Constr { fields, .. } => {
                        for field in fields.iter().rev() {
                            steps.push(Step::Visit(field, Rc::clone(&bound)));
                        }
                    }
                    PseudoExpr::BuiltinCall { args, .. } => {
                        for arg in args.iter().rev() {
                            steps.push(Step::Visit(arg, Rc::clone(&bound)));
                        }
                    }
                    PseudoExpr::Trace { message, value } => {
                        steps.push(Step::Visit(value, Rc::clone(&bound)));
                        steps.push(Step::Visit(message, bound));
                    }
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
                Step::AfterLetValue {
                    name,
                    id,
                    body,
                    bound,
                } => {
                    let mut body_bound = (*bound).clone();
                    Self::insert_free_capture_key(
                        &mut body_bound,
                        name,
                        id.unwrap_or_else(VarId::fresh_compat_placeholder),
                    );
                    steps.push(Step::Visit(body, Rc::new(body_bound)));
                }
            }
        }
    }

    pub(super) fn try_promote_lambda_rec_wrapper(
        &self,
        name: &str,
        id: VarId,
        params: &[Binder],
        lambda_body: &PseudoExpr,
    ) -> Option<PseudoExpr> {
        // Compat lets carry `id: None`, so accept either shape:
        // `promoted_rec_binding_ref_matches` falls back to name when the
        // inner recursive self-call's binder id is absent.
        let PseudoExpr::Let {
            name: inner_name,
            id: inner_id,
            value: inner_value,
            body: inner_body,
        } = lambda_body
        else {
            return None;
        };
        let inner_id_for_match = *inner_id;

        let PseudoExpr::RecFn {
            name: rec_name,
            params: inner_params,
            body: rec_body,
        } = inner_value.as_ref()
        else {
            return None;
        };

        if rec_name.as_str() != inner_name
            || params.is_empty()
            || inner_params.is_empty()
            || inner_params.len() > params.len()
        {
            return None;
        }

        let PseudoExpr::Apply { function, args } = inner_body.as_ref() else {
            return None;
        };
        if !matches!(
            function.as_ref(),
            PseudoExpr::Var { name: call_name, id: call_id, .. }
                if Self::promoted_rec_binding_ref_matches(
                    call_name,
                    *call_id,
                    inner_name,
                    inner_id_for_match,
                    rec_name.var_id(),
                )
        ) || args.len() != inner_params.len()
        {
            return None;
        }

        let mut seen_outer = std::collections::HashSet::new();
        for param in params {
            let param_name = param.to_string();
            if param == "_" || !seen_outer.insert(param_name) {
                return None;
            }
        }

        let mut mapped_outer_params = Vec::with_capacity(inner_params.len());
        let mut mapped_outer_set = std::collections::HashSet::new();
        for arg in args {
            let PseudoExpr::Var {
                name: arg_name,
                id: Some(arg_id),
                ..
            } = arg
            else {
                return None;
            };
            let outer_param = params.iter().find(|param| {
                crate::decompile::var_match::refs_match(
                    arg_name,
                    arg_id.get(),
                    param.as_str(),
                    param.id.get(),
                )
            })?;
            if !seen_outer.contains(outer_param.as_str())
                || !mapped_outer_set.insert(outer_param.as_str().to_string())
            {
                return None;
            }
            mapped_outer_params.push(outer_param.as_str().to_string());
        }

        let extra_outer_params: Vec<Binder> = params
            .iter()
            .filter(|param| !mapped_outer_set.contains(param.as_str()))
            .cloned()
            .collect();
        let mut extra_outer_param_keys = std::collections::HashSet::new();
        for param in &extra_outer_params {
            Self::insert_free_capture_key(&mut extra_outer_param_keys, param.as_str(), param.id);
        }

        let mut rec_bound = std::collections::HashSet::new();
        for param in inner_params {
            Self::insert_free_capture_key(&mut rec_bound, param.as_str(), param.id);
        }
        Self::insert_free_capture_key(&mut rec_bound, rec_name.as_str(), rec_name.id);
        let mut free_captures = std::collections::HashSet::new();
        Self::collect_free_var_keys(rec_body, &rec_bound, &mut free_captures);
        if free_captures.contains(&FreeCaptureKey::Id(id))
            || free_captures.contains(&FreeCaptureKey::CompatName(name.to_string()))
            || free_captures
                .iter()
                .any(|capture| !extra_outer_param_keys.contains(capture))
        {
            return None;
        }

        if Self::count_var_uses_by_id(rec_body, name, Some(id)) > 0 {
            return None;
        }

        let mut body_refs = std::collections::HashSet::new();
        Self::collect_var_names(rec_body, &mut body_refs);

        let mut used_names = body_refs;
        used_names.insert(name.to_string());
        for param in params {
            used_names.insert(param.to_string());
        }

        let mut promoted_body = rec_body.as_ref().clone();

        let self_temp =
            self.fresh_name_for_scope(&mut used_names, "__promote_rec_self".to_string());
        if rec_name != name {
            promoted_body = Self::rename_var_binding(
                &promoted_body,
                rec_name,
                Some(rec_name.var_id()),
                &self_temp,
            );
        }

        let mut temp_params = Vec::new();
        for (idx, (inner_param, outer_param)) in inner_params
            .iter()
            .zip(mapped_outer_params.iter())
            .enumerate()
        {
            if inner_param == outer_param {
                continue;
            }
            let temp_name =
                self.fresh_name_for_scope(&mut used_names, format!("__promote_rec_param_{idx}"));
            promoted_body = Self::rename_var_binding(
                &promoted_body,
                inner_param,
                Some(inner_param.var_id()),
                &temp_name,
            );
            temp_params.push((temp_name, outer_param.clone()));
        }

        // Map outer-param name → VarId so the final temp → outer
        // rename can use `substitute_var_for_var` and re-point body
        // refs at the outer binder's id. A plain rename leaves them
        // carrying inner_param's original id, orphaned from the outer
        // binder.
        let outer_param_ids: std::collections::HashMap<String, VarId> =
            params.iter().map(|p| (p.to_string(), p.var_id())).collect();
        for (temp_name, outer_param) in temp_params {
            if let Some(&outer_id) = outer_param_ids.get(&outer_param) {
                promoted_body = Self::substitute_var_for_var(
                    &promoted_body,
                    &temp_name,
                    None,
                    &outer_param,
                    outer_id,
                );
            } else {
                promoted_body = Self::rename_var(&promoted_body, &temp_name, &outer_param);
            }
        }

        if !extra_outer_params.is_empty() {
            let rewritten_self_name = if rec_name != name {
                self_temp.as_str()
            } else {
                name
            };
            promoted_body = Self::reorder_promoted_rec_call_args(
                &promoted_body,
                rewritten_self_name,
                rec_name.var_id(),
                inner_params.len(),
                params,
                &mapped_outer_params,
                &extra_outer_params,
            );
        }

        // Body self-refs still hold `rec_name`'s original id
        // after the rename chain (rename_var is textual and
        // id-preserving), so the new RecFn's self-binder MUST
        // reuse that id or the refs are orphaned.
        let recfn_self_id = rec_name.var_id();
        if rec_name != name {
            promoted_body =
                Self::rename_var_binding(&promoted_body, &self_temp, Some(recfn_self_id), name);
        }

        Some(PseudoExpr::RecFn {
            name: crate::pseudo::ast::Binder::new(name.to_string(), recfn_self_id),
            params: params.to_vec(),
            body: PBox::new(promoted_body),
        })
    }
}

#[cfg(test)]
mod tests;
