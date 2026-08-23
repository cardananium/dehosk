use super::Simplifier;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, WhenClause};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

impl Simplifier {
    pub(super) fn may_be_scott_constructor_value(expr: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Let { body, .. } => pending.push(body),
                PseudoExpr::Lambda { params, body } => {
                    if params.len() >= 2
                        && matches!(
                            body.as_ref(),
                            PseudoExpr::Var { .. } | PseudoExpr::Apply { .. }
                        )
                    {
                        return true;
                    }
                }
                _ => {}
            }
        }
        false
    }

    pub(super) fn may_have_scott_constructor_fields(expr: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Let { body, .. } => pending.push(body),
                PseudoExpr::Lambda { params, body } => {
                    if params.len() >= 2 && matches!(body.as_ref(), PseudoExpr::Apply { .. }) {
                        return true;
                    }
                }
                _ => {}
            }
        }
        false
    }

    pub(super) fn try_rewrite_scott_constructor_value(
        expr: &PseudoExpr,
    ) -> Option<(PseudoExpr, usize, bool)> {
        let mut lets: Vec<(String, Option<VarId>, PseudoExpr)> = Vec::new();
        let mut cur = expr;
        while let PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } = cur
        {
            lets.push((name.clone(), *id, (**value).clone()));
            cur = body;
        }

        let (mut result, arity, has_fields) = Self::try_rewrite_scott_constructor_lambda(cur)?;

        for (name, id, value) in lets.into_iter().rev() {
            result = PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(result),
            };
        }

        Some((result, arity, has_fields))
    }

    /// Base case of [`Self::try_rewrite_scott_constructor_value`]'s
    /// `Let`-peeling chain: the shape that ends it.
    fn try_rewrite_scott_constructor_lambda(
        expr: &PseudoExpr,
    ) -> Option<(PseudoExpr, usize, bool)> {
        match expr {
            PseudoExpr::Lambda { params, body } => {
                if params.len() < 2 {
                    return None;
                }

                let mut used_idx = None;
                for (idx, param) in params.iter().enumerate() {
                    if Self::is_var_used_by_id(body, param.as_str(), param.id.get()) {
                        if used_idx.is_some() {
                            return None;
                        }
                        used_idx = Some(idx);
                    }
                }

                let used_idx = used_idx?;
                let used_name = &params[used_idx];

                match body.as_ref() {
                    PseudoExpr::Var { name, id, .. }
                        if Self::binder_matches_var_id(used_name, name, id.get()) =>
                    {
                        Some((
                            PseudoExpr::constr(
                                ConstructorShape::scott_positional(used_idx, 0),
                                vec![],
                            ),
                            params.len(),
                            false,
                        ))
                    }
                    PseudoExpr::Apply { function, args } => {
                        if !matches!(
                            function.as_ref(),
                            PseudoExpr::Var { name, id, .. }
                                if Self::binder_matches_var_id(used_name, name, id.get())
                        ) {
                            return None;
                        }
                        if args
                            .iter()
                            .any(|arg| Self::is_var_used_by_id(arg, used_name, used_name.id.get()))
                        {
                            return None;
                        }
                        Some((
                            PseudoExpr::constr(
                                ConstructorShape::scott_positional(used_idx, args.len()),
                                (args.clone()).into_vec(),
                            ),
                            params.len(),
                            !args.is_empty(),
                        ))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    pub(super) fn rewrite_scott_constructor_if_branches(
        then_branch: &PseudoExpr,
        else_branch: &PseudoExpr,
    ) -> Option<(PseudoExpr, PseudoExpr)> {
        if !Self::may_be_scott_constructor_value(then_branch)
            || !Self::may_be_scott_constructor_value(else_branch)
            || (!Self::may_have_scott_constructor_fields(then_branch)
                && !Self::may_have_scott_constructor_fields(else_branch))
        {
            return None;
        }
        let (then_rewritten, then_arity, then_has_fields) =
            Self::try_rewrite_scott_constructor_value(then_branch)?;
        let (else_rewritten, else_arity, else_has_fields) =
            Self::try_rewrite_scott_constructor_value(else_branch)?;
        (then_arity == else_arity && (then_has_fields || else_has_fields))
            .then_some((then_rewritten, else_rewritten))
    }

    pub(super) fn rewrite_scott_constructor_when_clauses(
        clauses: &[WhenClause],
    ) -> Option<Vec<WhenClause>> {
        let mut arity = None;
        let mut rewritten_count = 0usize;
        let mut has_fields = false;
        let mut rewritten = Vec::with_capacity(clauses.len());

        for clause in clauses {
            if Self::is_fail(&clause.body) {
                rewritten.push(clause.clone());
                continue;
            }

            if let Some((new_body, new_arity, clause_has_fields)) =
                Self::try_rewrite_scott_constructor_value(&clause.body)
            {
                match arity {
                    Some(expected) if expected != new_arity => return None,
                    None => arity = Some(new_arity),
                    _ => {}
                }
                rewritten_count += 1;
                has_fields |= clause_has_fields;
                rewritten.push(WhenClause {
                    pattern: clause.pattern.clone(),
                    guard: clause.guard.clone(),
                    body: new_body,
                });
            } else {
                rewritten.push(clause.clone());
            }
        }

        (rewritten_count >= 2 && has_fields).then_some(rewritten)
    }

    pub(super) fn extract_eta_pair_selector_subject(subject: &PseudoExpr) -> Option<PseudoExpr> {
        let PseudoExpr::Lambda { params, body } = subject else {
            return None;
        };
        if params.len() != 2 {
            return None;
        }

        let selector_param = &params[0];
        let second_param = &params[1];

        let PseudoExpr::Apply { function, args } = body.as_ref() else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        if !matches!(
            function.as_ref(),
            PseudoExpr::Var { name, id, .. }
                if Self::binder_matches_var_id(selector_param, name, id.get())
        ) {
            return None;
        }
        if !matches!(
            &args[1],
            PseudoExpr::Var { name, id, .. }
                if Self::binder_matches_var_id(second_param, name, id.get())
        ) {
            return None;
        }
        if Self::is_var_used_by_id(&args[0], selector_param, selector_param.id.get())
            || Self::is_var_used_by_id(&args[0], second_param, second_param.id.get())
        {
            return None;
        }

        Some(args[0].clone())
    }
}

#[cfg(test)]
mod tests;
