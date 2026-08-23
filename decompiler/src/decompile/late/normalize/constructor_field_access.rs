use crate::decompile::mid::type_env::{TypeEnvironment, resolve_type_with_env};
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, PseudoType, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

pub(super) fn subject_supports_data_fields(
    subject: &PseudoExpr,
    env: Option<&TypeEnvironment>,
) -> bool {
    matches!(
        resolve_type_with_env(subject, env).as_deref(),
        None | Some(PseudoType::Data | PseudoType::Unknown)
    )
}

pub(super) fn rewrite_constructor_subject_field_accesses_to_pattern_binders(
    expr: PseudoExpr,
) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;

    struct ConstructorScope {
        subject: Binder,
        fields: Vec<Binder>,
    }

    struct FieldAccessToBinders {
        scopes: Vec<ConstructorScope>,
    }

    impl ExprFolder for FieldAccessToBinders {
        fn post_index_access(&mut self, collection: PseudoExpr, index: usize) -> PseudoExpr {
            if let PseudoExpr::FieldAccess {
                record, selector, ..
            } = &collection
                && selector.as_pretty_name() == "fields"
                && let PseudoExpr::Var { id, .. } = record.as_ref()
                && let Some(binder) = self.scopes.iter().rev().find_map(|scope| {
                    (Some(scope.subject.id) == *id)
                        .then(|| scope.fields.get(index))
                        .flatten()
                        .filter(|binder| binder.name != "_")
                })
            {
                return PseudoExpr::var_with_id(binder.name.clone(), binder.id);
            }
            PseudoExpr::IndexAccess {
                collection: PBox::new(collection),
                index,
            }
        }

        // `When` is not on the generic step machine (its clauses need a
        // hook), so this override is where the per-clause scope push/pop
        // lives — exactly the "value must be folded before the binding
        // takes effect" shape `fold_inner` documents for `Let`, but here
        // the "binding" is conditional per clause and undone right after.
        fn fold_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            let subject = self.fold(subject);
            let effective_subject = subject_name.clone().or_else(|| match &subject {
                PseudoExpr::Var { name, id, .. } => Some(Binder::new(
                    name.clone(),
                    id.unwrap_or_else(VarId::fresh_compat_placeholder),
                )),
                _ => None,
            });
            let subject_is_data = subject_supports_data_fields(&subject, None);
            let clauses = clauses
                .into_iter()
                .map(|clause| {
                    let mut pushed = false;
                    if subject_is_data
                        && let (Some(subject), WhenPattern::Constructor { fields, .. }) =
                            (&effective_subject, &clause.pattern)
                        && !fields.is_empty()
                    {
                        self.scopes.push(ConstructorScope {
                            subject: subject.clone(),
                            fields: fields.clone(),
                        });
                        pushed = true;
                    }
                    let guard = clause.guard.map(|guard| self.fold(guard));
                    let body = self.fold(clause.body);
                    if pushed {
                        self.scopes.pop();
                    }
                    WhenClause {
                        pattern: clause.pattern,
                        guard,
                        body,
                    }
                })
                .collect();
            self.post_when(subject, subject_name, clauses)
        }
    }

    FieldAccessToBinders { scopes: Vec::new() }.fold(expr)
}
