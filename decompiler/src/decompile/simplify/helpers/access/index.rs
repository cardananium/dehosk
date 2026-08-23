use std::collections::HashMap;

use crate::decompile::simplify::Simplifier;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause};
use crate::pseudo::var_id::VarId;

use super::{
    AccessShadow, access_ref_matches, shadow_access_binder, shadow_access_binding,
    shadow_access_pattern,
};

impl Simplifier {
    /// Count direct index accesses `collection_var[index]` in an expression.
    /// Shadow-aware: ignores uses under rebinding of `collection_var`.
    pub(crate) fn collect_index_access_counts(
        expr: &PseudoExpr,
        collection_var: &str,
        collection_id: Option<VarId>,
    ) -> HashMap<usize, usize> {
        let mut counts = HashMap::new();
        let mut stack = vec![(expr, AccessShadow::default())];

        while let Some((current, shadow)) = stack.pop() {
            if (!shadow.exact_blocked || !shadow.fallback_blocked)
                && let PseudoExpr::IndexAccess { collection, index } = current
                && let PseudoExpr::Var { name, id, .. } = collection.as_ref()
                && access_ref_matches(name, *id, collection_var, collection_id, shadow)
            {
                *counts.entry(*index).or_insert(0) += 1;
            }

            match current {
                PseudoExpr::Lambda { params, body } => {
                    let mut next_shadow = shadow;
                    for param in params {
                        next_shadow =
                            shadow_access_binder(next_shadow, param, collection_var, collection_id);
                    }
                    stack.push((body, next_shadow));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    let mut next_shadow =
                        shadow_access_binder(shadow, name, collection_var, collection_id);
                    for param in params {
                        next_shadow =
                            shadow_access_binder(next_shadow, param, collection_var, collection_id);
                    }
                    stack.push((body, next_shadow));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                    ..
                } => {
                    stack.push((
                        body,
                        shadow_access_binding(shadow, name, *id, collection_var, collection_id),
                    ));
                    stack.push((value, shadow));
                }
                PseudoExpr::Apply { function, args } => {
                    for arg in args.iter().rev() {
                        stack.push((arg, shadow));
                    }
                    stack.push((function, shadow));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    stack.push((else_branch, shadow));
                    stack.push((then_branch, shadow));
                    stack.push((condition, shadow));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                    ..
                } => {
                    for clause in clauses.iter().rev() {
                        let mut clause_shadow = shadow;
                        if let Some(subject_name) = subject_name {
                            clause_shadow = shadow_access_binder(
                                clause_shadow,
                                subject_name,
                                collection_var,
                                collection_id,
                            );
                        }
                        clause_shadow = shadow_access_pattern(
                            clause_shadow,
                            &clause.pattern,
                            collection_var,
                            collection_id,
                        );
                        stack.push((&clause.body, clause_shadow));
                        if let Some(guard) = &clause.guard {
                            stack.push((guard, clause_shadow));
                        }
                    }
                    stack.push((subject, shadow));
                }
                PseudoExpr::BinOp { left, right, .. } | PseudoExpr::Pair(left, right) => {
                    stack.push((right, shadow));
                    stack.push((left, shadow));
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
                    stack.push((operand, shadow));
                }
                PseudoExpr::BuiltinCall { args, .. } | PseudoExpr::Constr { fields: args, .. } => {
                    for arg in args.iter().rev() {
                        stack.push((arg, shadow));
                    }
                }
                PseudoExpr::Trace { message, value } => {
                    stack.push((value, shadow));
                    stack.push((message, shadow));
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(tail) = tail {
                        stack.push((tail, shadow));
                    }
                    for element in elements.iter().rev() {
                        stack.push((element, shadow));
                    }
                }
                PseudoExpr::Tuple(items) => {
                    for item in items.iter().rev() {
                        stack.push((item, shadow));
                    }
                }
                PseudoExpr::Var { .. }
                | PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::Unit
                | PseudoExpr::Error { .. }
                | PseudoExpr::Raw { .. }
                | PseudoExpr::Data(_)
                | PseudoExpr::HelperSymbol(_) => {}
            }
        }

        counts
    }

    /// Replace direct `collection_var[target_index]` with `replacement_name`.
    /// Shadow-aware: does not rewrite under rebinding of `collection_var`.
    pub(crate) fn replace_index_access(
        expr: PseudoExpr,
        collection_var: &str,
        collection_id: Option<VarId>,
        target_index: usize,
        replacement_name: &str,
        replacement_id: VarId,
    ) -> PseudoExpr {
        use crate::pseudo::fold::{ExprFolder, FoldAction};

        struct IndexAccessReplacer<'a> {
            collection_var: &'a str,
            collection_id: Option<VarId>,
            target_index: usize,
            replacement_name: &'a str,
            replacement_id: VarId,
            shadow: AccessShadow,
            /// Shadow to restore in the matching `exit_*` step.
            saved: Vec<AccessShadow>,
        }

        impl ExprFolder for IndexAccessReplacer<'_> {
            fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
                let shadow = self.shadow;
                if (!shadow.exact_blocked || !shadow.fallback_blocked)
                    && let PseudoExpr::IndexAccess { collection, index } = expr
                    && *index == self.target_index
                    && let PseudoExpr::Var { name, id, .. } = collection.as_ref()
                    && access_ref_matches(
                        name,
                        *id,
                        self.collection_var,
                        self.collection_id,
                        shadow,
                    )
                {
                    return FoldAction::Replace(PseudoExpr::Var {
                        name: self.replacement_name.to_string(),
                        id: Some(self.replacement_id),
                    });
                }
                FoldAction::Walk
            }

            fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
                self.saved.push(self.shadow);
                for param in params {
                    self.shadow = shadow_access_binder(
                        self.shadow,
                        param,
                        self.collection_var,
                        self.collection_id,
                    );
                }
                params.to_vec()
            }

            fn exit_lambda(&mut self, _params: &[Binder]) {
                self.shadow = self.saved.pop().expect("lambda shadow");
            }

            fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
                self.saved.push(self.shadow);
                self.shadow = shadow_access_binder(
                    self.shadow,
                    name,
                    self.collection_var,
                    self.collection_id,
                );
                for param in params {
                    self.shadow = shadow_access_binder(
                        self.shadow,
                        param,
                        self.collection_var,
                        self.collection_id,
                    );
                }
                (name.clone(), params.to_vec())
            }

            fn exit_recfn(&mut self, _name: &Binder, _params: &[Binder]) {
                self.shadow = self.saved.pop().expect("recfn shadow");
            }

            fn enter_let(&mut self, name: &str, id: &Option<VarId>, _value: &PseudoExpr) -> String {
                self.saved.push(self.shadow);
                self.shadow = shadow_access_binding(
                    self.shadow,
                    name,
                    *id,
                    self.collection_var,
                    self.collection_id,
                );
                name.to_string()
            }

            fn exit_let(&mut self, _name: &str) {
                self.shadow = self.saved.pop().expect("let shadow");
            }

            // Not on the generic step machine (its clauses need subject-name
            // and pattern-binder shadowing), so overridden here rather than via
            // `fold_clause` — which would also fold `Literal` patterns.
            fn fold_when(
                &mut self,
                subject: PseudoExpr,
                subject_name: Option<Binder>,
                clauses: Vec<WhenClause>,
            ) -> PseudoExpr {
                let subject = self.fold(subject);
                let outer_shadow = self.shadow;
                let clauses = clauses
                    .into_iter()
                    .map(|c| {
                        self.shadow = outer_shadow;
                        if let Some(subject_name) = &subject_name {
                            self.shadow = shadow_access_binder(
                                self.shadow,
                                subject_name,
                                self.collection_var,
                                self.collection_id,
                            );
                        }
                        self.shadow = shadow_access_pattern(
                            self.shadow,
                            &c.pattern,
                            self.collection_var,
                            self.collection_id,
                        );
                        let guard = c.guard.map(|g| self.fold(g));
                        let body = self.fold(c.body);
                        WhenClause {
                            pattern: c.pattern,
                            guard,
                            body,
                        }
                    })
                    .collect();
                self.shadow = outer_shadow;
                self.post_when(subject, subject_name, clauses)
            }
        }

        IndexAccessReplacer {
            collection_var,
            collection_id,
            target_index,
            replacement_name,
            replacement_id,
            shadow: AccessShadow::default(),
            saved: Vec::new(),
        }
        .fold(expr)
    }
}
