use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;
use std::collections::HashSet;

use super::blueprint_registry::BlueprintHintRegistry;
use super::{contains_predicate, contains_predicate_with_options, simplify};

mod field_destructure;

pub(crate) use self::field_destructure::destructure_when_fields;

pub(crate) fn contains_eta_pair_selector_when_subjects(expr: &PseudoExpr) -> bool {
    contains_predicate_with_options(
        expr,
        &|e| match e {
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                if clauses.len() != 1 {
                    return false;
                }

                if extract_eta_pair_selector_subject(subject.as_ref()).is_none() {
                    return false;
                }

                let clause = &clauses[0];
                let is_pair_pattern = match &clause.pattern {
                    WhenPattern::Pair(_, _) => true,
                    WhenPattern::Constructor { shape, fields, .. } => {
                        shape.as_known() == Some(KnownConstructor::Pair) && fields.len() == 2
                    }
                    _ => false,
                };

                clause.guard.is_none() && is_pair_pattern
            }
            _ => false,
        },
        false,
    )
}

fn extract_eta_pair_selector_subject(subject: &PseudoExpr) -> Option<PseudoExpr> {
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
    if !matches!(function.as_ref(), PseudoExpr::Var { id, .. } if *id == Some(selector_param.var_id()))
    {
        return None;
    }
    if !matches!(&args[1], PseudoExpr::Var { id, .. } if *id == Some(second_param.var_id())) {
        return None;
    }
    if simplify::Simplifier::is_var_used_by_id(
        &args[0],
        selector_param,
        Some(selector_param.var_id()),
    ) || simplify::Simplifier::is_var_used_by_id(
        &args[0],
        second_param,
        Some(second_param.var_id()),
    ) {
        return None;
    }

    Some(args[0].clone())
}

pub(crate) fn contains_destructurable_when_fields(expr: &PseudoExpr) -> bool {
    fn contains_unpack_of_subject(expr: &PseudoExpr, subject_id: VarId) -> bool {
        contains_predicate(expr, &|e| {
            matches!(
                e,
                PseudoExpr::BuiltinCall { name, args }
                    if (*name == crate::BuiltinId::ConstrUnpack || *name == crate::BuiltinId::DataUnConstr)
                        && args.len() == 1
                        && matches!(
                            &args[0],
                            PseudoExpr::Var { id, .. } if *id == Some(subject_id)
                        )
            )
        })
    }

    contains_predicate(expr, &|e| match e {
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            let PseudoExpr::Var {
                id: Some(subject_id),
                ..
            } = subject.as_ref()
            else {
                return false;
            };

            clauses.iter().any(|clause| {
                let destructurable_pattern = matches!(
                    &clause.pattern,
                    WhenPattern::Constructor { fields, .. } if fields.is_empty()
                ) || matches!(&clause.pattern, WhenPattern::Wildcard);

                destructurable_pattern
                    && (contains_unpack_of_subject(&clause.body, *subject_id)
                        || clause
                            .guard
                            .as_ref()
                            .is_some_and(|guard| contains_unpack_of_subject(guard, *subject_id)))
            })
        }
        _ => false,
    })
}

fn extract_unpack_tag_subject(expr: &PseudoExpr) -> Option<PseudoExpr> {
    match expr {
        PseudoExpr::FieldAccess {
            record, selector, ..
        } if selector.is_pair_fst() => {
            if let PseudoExpr::BuiltinCall { name, args } = record.as_ref()
                && (*name == crate::BuiltinId::ConstrUnpack
                    || *name == crate::BuiltinId::DataUnConstr)
                && args.len() == 1
            {
                return Some(args[0].clone());
            }
            None
        }
        PseudoExpr::IndexAccess {
            collection,
            index: 0,
        } => {
            if let PseudoExpr::BuiltinCall { name, args } = collection.as_ref()
                && (*name == crate::BuiltinId::ConstrUnpack
                    || *name == crate::BuiltinId::DataUnConstr)
                && args.len() == 1
            {
                return Some(args[0].clone());
            }
            None
        }
        _ => None,
    }
}

pub(crate) fn contains_unpack_tag_when_subjects(expr: &PseudoExpr) -> bool {
    contains_predicate(expr, &|e| {
        matches!(
            e,
            PseudoExpr::When { subject, clauses, .. }
                if extract_unpack_tag_subject(subject).is_some()
                    && clauses.iter().any(|clause| {
                        matches!(clause.pattern, WhenPattern::Literal(PseudoExpr::Int(_)))
                    })
        )
    })
}

fn peel_identity_when_subject_ref(mut expr: &PseudoExpr) -> &PseudoExpr {
    loop {
        let PseudoExpr::Apply { function, args } = expr else {
            return expr;
        };
        if args.len() != 1 {
            return expr;
        }

        let mut current_fn = function.as_ref();
        loop {
            match current_fn {
                PseudoExpr::Force(inner) => current_fn = inner.as_ref(),
                PseudoExpr::Apply {
                    function: inner_fn,
                    args: inner_args,
                } if inner_args.is_empty() => current_fn = inner_fn.as_ref(),
                PseudoExpr::Lambda { params, body } if params.len() == 1 => {
                    if matches!(body.as_ref(), PseudoExpr::Var { id, .. } if *id == Some(params[0].var_id()))
                    {
                        expr = &args[0];
                        break;
                    }
                    return expr;
                }
                _ => return expr,
            }
        }
    }
}

fn peel_identity_when_subject(mut expr: PseudoExpr) -> PseudoExpr {
    loop {
        let PseudoExpr::Apply { function, args } = expr else {
            return expr;
        };
        if args.len() != 1 {
            return PseudoExpr::Apply { function, args };
        }

        let mut current_fn = function.into_inner();
        loop {
            match current_fn {
                PseudoExpr::Force(inner) => current_fn = inner.into_inner(),
                PseudoExpr::Apply {
                    function: inner_fn,
                    args: inner_args,
                } if inner_args.is_empty() => current_fn = inner_fn.into_inner(),
                PseudoExpr::Lambda { params, body } if params.len() == 1 => {
                    if matches!(body.as_ref(), PseudoExpr::Var { id, .. } if *id == Some(params[0].var_id()))
                    {
                        expr = args.into_iter().next().unwrap();
                        break;
                    }
                    return PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::Lambda { params, body }),
                        args,
                    };
                }
                _ => {
                    return PseudoExpr::Apply {
                        function: PBox::new(current_fn),
                        args,
                    };
                }
            }
        }
    }
}

fn is_simple_when_subject(expr: &PseudoExpr) -> bool {
    matches!(
        expr,
        PseudoExpr::Var { .. }
            | PseudoExpr::FieldAccess { .. }
            | PseudoExpr::IndexAccess { .. }
            | PseudoExpr::Int(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::String(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::Unit
    )
}

pub(crate) fn contains_complex_when_subjects(expr: &PseudoExpr) -> bool {
    contains_predicate(expr, &|e| match e {
        PseudoExpr::When { subject, .. } => {
            let normalized_subject = peel_identity_when_subject_ref(subject);
            let is_simple_call = matches!(
                normalized_subject,
                PseudoExpr::Apply { function, .. }
                    if matches!(function.as_ref(), PseudoExpr::Var { .. })
            );

            !is_simple_when_subject(normalized_subject) && !is_simple_call
        }
        _ => false,
    })
}

pub(crate) fn lift_unpack_tag_when_subjects(
    expr: PseudoExpr,
    blueprint_hints: Option<&crate::cardano::BlueprintHints>,
    registry: Option<&BlueprintHintRegistry>,
) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;
    use num_traits::ToPrimitive;

    struct UnpackTagWhenLifter<'a> {
        blueprint_hints: Option<&'a crate::cardano::BlueprintHints>,
        registry: Option<&'a BlueprintHintRegistry>,
    }

    impl ExprFolder for UnpackTagWhenLifter<'_> {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            let Some(real_subject) = extract_unpack_tag_subject(&subject) else {
                return PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                };
            };

            let mut saw_tag_literal = false;
            let lifted_clauses: Vec<WhenClause> = clauses
                .into_iter()
                .map(|clause| {
                    let pattern = match clause.pattern {
                        WhenPattern::Literal(PseudoExpr::Int(n)) => {
                            if let Some(tag) = n.to_usize() {
                                saw_tag_literal = true;
                                WhenPattern::constructor(
                                    ConstructorShape::unknown_data(tag, 0),
                                    vec![],
                                )
                            } else {
                                WhenPattern::Literal(PseudoExpr::Int(n))
                            }
                        }
                        other => other,
                    };
                    WhenClause {
                        pattern,
                        guard: clause.guard,
                        body: clause.body,
                    }
                })
                .collect();

            if !saw_tag_literal {
                return PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses: lifted_clauses,
                };
            }

            destructure_when_fields(
                PseudoExpr::When {
                    subject: PBox::new(real_subject),
                    subject_name,
                    clauses: lifted_clauses,
                },
                self.blueprint_hints,
                self.registry,
            )
        }
    }

    UnpackTagWhenLifter {
        blueprint_hints,
        registry,
    }
    .fold(expr)
}

/// Extract complex when-subjects to let bindings.
pub(crate) fn extract_complex_when_subjects(expr: PseudoExpr) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;

    let mut used_names = HashSet::new();
    simplify::Simplifier::collect_var_names(&expr, &mut used_names);

    struct SubjectExtractor {
        counter: usize,
        used_names: HashSet<String>,
    }

    impl SubjectExtractor {
        fn fresh_subject_name(&mut self, prefix: &str) -> String {
            loop {
                let candidate = format!("{prefix}_{}", self.counter);
                self.counter += 1;
                if self.used_names.insert(candidate.clone()) {
                    return candidate;
                }
            }
        }
    }

    impl ExprFolder for SubjectExtractor {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            let subject = peel_identity_when_subject(subject);

            if is_simple_when_subject(&subject) {
                return PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                };
            }

            if let PseudoExpr::Apply { ref function, .. } = subject
                && matches!(function.as_ref(), PseudoExpr::Var { .. })
            {
                return PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                };
            }

            let binder = if let Some(existing_subject_name) = subject_name {
                existing_subject_name
            } else {
                let prefix = if matches!(subject, PseudoExpr::RecFn { .. }) {
                    "fold_result"
                } else {
                    "match_subject"
                };
                let var_name = self.fresh_subject_name(prefix);
                Binder::new(var_name, VarId::fresh_binding())
            };

            PseudoExpr::Let {
                name: binder.to_string(),
                id: Some(binder.id),
                value: PBox::new(subject),
                body: PBox::new(PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::Var {
                        name: binder.to_string(),
                        id: Some(binder.id),
                    }),
                    subject_name: None,
                    clauses,
                }),
            }
        }
    }

    SubjectExtractor {
        counter: 0,
        used_names,
    }
    .fold(expr)
}

/// Collapse one-clause eta-expanded pair-selector wrappers that survive the
/// simplify loop and reappear in the late structural tail.
pub(crate) fn collapse_eta_pair_selector_when_subjects(expr: PseudoExpr) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;

    struct EtaPairSelectorWhenCollapser;

    impl ExprFolder for EtaPairSelectorWhenCollapser {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            if clauses.len() == 1
                && let Some(first_field) = extract_eta_pair_selector_subject(&subject)
            {
                let clause = &clauses[0];
                if clause.guard.is_none() {
                    let pair_binders = match &clause.pattern {
                        WhenPattern::Pair(first_name, second_name) => {
                            Some((first_name.clone(), second_name.clone()))
                        }
                        WhenPattern::Constructor { shape, fields, .. }
                            if shape.as_known() == Some(KnownConstructor::Pair)
                                && fields.len() == 2 =>
                        {
                            Some((fields[0].clone(), fields[1].clone()))
                        }
                        _ => None,
                    };
                    if let Some((first_name, second_name)) = pair_binders {
                        let mut body = clause.body.clone();

                        if second_name != "_"
                            && simplify::Simplifier::is_var_used_by_id(
                                &body,
                                &second_name,
                                Some(second_name.var_id()),
                            )
                        {
                            body = PseudoExpr::Lambda {
                                params: vec![second_name],
                                body: PBox::new(body),
                            };
                        }

                        if first_name != "_"
                            && simplify::Simplifier::is_var_used_by_id(
                                &body,
                                &first_name,
                                Some(first_name.var_id()),
                            )
                        {
                            let bind_id = first_name.var_id();
                            body = PseudoExpr::Let {
                                name: first_name.to_string(),
                                id: Some(bind_id),
                                value: PBox::new(first_field),
                                body: PBox::new(body),
                            };
                        }

                        if let Some(name) = subject_name.as_ref()
                            && name != "_"
                            && simplify::Simplifier::is_var_used_by_id(
                                &body,
                                name,
                                Some(name.var_id()),
                            )
                        {
                            let bind_id = name.var_id();
                            body = PseudoExpr::Let {
                                name: name.to_string(),
                                id: Some(bind_id),
                                value: PBox::new(subject.clone()),
                                body: PBox::new(body),
                            };
                        }

                        return body;
                    }
                }
            }

            PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses,
            }
        }
    }

    EtaPairSelectorWhenCollapser.fold(expr)
}

#[cfg(test)]
mod tests;
