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
    use std::collections::HashMap;

    /// A `when` whose clauses are being folded.
    struct WhenScope {
        /// The binder its subject goes by, when it has one.
        subject: Option<Binder>,
        subject_is_data: bool,
    }

    #[derive(Default)]
    struct FieldAccessToBinders {
        /// One per `when` whose clauses are being folded, innermost last.
        whens: Vec<WhenScope>,
        /// `(subject id, field index)` → the pattern binders naming that
        /// field in the open clauses, innermost last. Keyed so a lookup is
        /// one probe, not a walk over every enclosing clause — whens nest as
        /// deep as the script makes them.
        binders: HashMap<(VarId, usize), Vec<Binder>>,
        /// Per open clause, the keys it added to `binders`.
        clause_keys: Vec<Vec<(VarId, usize)>>,
    }

    impl ExprFolder for FieldAccessToBinders {
        // Folded flat, so a `when` nested as deep as the script makes it does
        // not recurse once per level: the clause scopes go through the
        // machine's clause hooks, and patterns are kept as they are.
        fn machine_folds_when(&self) -> bool {
            true
        }

        fn machine_keeps_pattern_literals(&self) -> bool {
            true
        }

        fn machine_scopes_clauses(&self) -> bool {
            true
        }

        fn post_index_access(&mut self, collection: PseudoExpr, index: usize) -> PseudoExpr {
            if let PseudoExpr::FieldAccess {
                record, selector, ..
            } = &collection
                && selector.as_pretty_name() == "fields"
                && let PseudoExpr::Var { id: Some(id), .. } = record.as_ref()
                && let Some(binder) = self
                    .binders
                    .get(&(*id, index))
                    .and_then(|binders| binders.last())
            {
                return PseudoExpr::var_with_id(binder.name.clone(), binder.id);
            }
            PseudoExpr::IndexAccess {
                collection: PBox::new(collection),
                index,
            }
        }

        fn enter_clauses(&mut self, subject: &PseudoExpr, subject_name: Option<&Binder>) {
            let subject_binder = subject_name.cloned().or_else(|| match subject {
                PseudoExpr::Var { name, id, .. } => Some(Binder::new(
                    name.clone(),
                    id.unwrap_or_else(VarId::fresh_compat_placeholder),
                )),
                _ => None,
            });
            self.whens.push(WhenScope {
                subject: subject_binder,
                subject_is_data: subject_supports_data_fields(subject, None),
            });
        }

        // A clause matching a constructor on a `Data` subject brings its
        // field binders into scope for its guard and body.
        fn enter_clause(&mut self, _subject_name: Option<&Binder>, pattern: &WhenPattern) {
            let mut keys = Vec::new();
            let when = self.whens.last().expect("enter_clauses opened this when");
            if when.subject_is_data
                && let (Some(subject), WhenPattern::Constructor { fields, .. }) =
                    (&when.subject, pattern)
            {
                for (index, field) in fields.iter().enumerate() {
                    if field.name != "_" {
                        keys.push((subject.id, index));
                        self.binders
                            .entry((subject.id, index))
                            .or_default()
                            .push(field.clone());
                    }
                }
            }
            self.clause_keys.push(keys);
        }

        fn exit_clause(&mut self, _subject_name: Option<&Binder>, _pattern: &WhenPattern) {
            for key in self
                .clause_keys
                .pop()
                .expect("enter_clause opened this clause")
            {
                if let Some(binders) = self.binders.get_mut(&key) {
                    binders.pop();
                }
            }
        }

        fn post_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            self.whens.pop();
            PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses: clauses.into(),
            }
        }
    }

    FieldAccessToBinders::default().fold(expr)
}
