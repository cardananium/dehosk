use std::rc::Rc;

use super::super::postprocess::{SumTypeId, sum_type_constructor_names};
use super::Simplifier;
use crate::decompile::ScriptVersion;
use crate::decompile::blueprint_registry::TypeHintId;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};

#[derive(Default)]
struct KnownConstructorPatternSummary {
    all_unnamed: bool,
    wildcard_is_fail_only: bool,
    constructor_clause_count: usize,
    has_false_ctor: bool,
    has_true_ctor: bool,
    has_some_ctor: bool,
    has_none_ctor: bool,
}

pub(super) struct SubjectConstructorNamingResult {
    pub clauses: Vec<WhenClause>,
    pub has_unnamed_constructors: bool,
}

impl Simplifier {
    pub(super) fn subject_constructor_names(
        &self,
        subject: &PseudoExpr,
    ) -> Option<&'static [&'static str]> {
        const PURPOSE_V3_NAMES: &[&str] = &[
            "Minting",
            "Spending",
            "Withdrawing",
            "Publishing",
            "Voting",
            "Proposing",
        ];

        let version = self.script_version?;

        match subject {
            PseudoExpr::Var { name, id, .. } => {
                let context_field_name = id
                    .get()
                    .and_then(|vid| self.context.context_field_names_by_id.get(&vid))
                    .map(|s| s.as_str())
                    .or_else(|| {
                        self.context
                            .context_field_names
                            .get(name)
                            .map(|s| s.as_str())
                    });

                match context_field_name {
                    Some("purpose") => match version {
                        ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2 => {
                            return sum_type_constructor_names(SumTypeId::Purpose, version);
                        }
                        ScriptVersion::PlutusV3 => return Some(PURPOSE_V3_NAMES),
                    },
                    Some("script_info") => {
                        return sum_type_constructor_names(SumTypeId::ScriptInfo, version);
                    }
                    _ => {}
                }

                if name == "purpose" {
                    return match version {
                        ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2 => {
                            sum_type_constructor_names(SumTypeId::Purpose, version)
                        }
                        ScriptVersion::PlutusV3 => Some(PURPOSE_V3_NAMES),
                    };
                }

                if name == "script_info" {
                    return sum_type_constructor_names(SumTypeId::ScriptInfo, version);
                }

                let var_type = id
                    .get()
                    .and_then(|vid| self.context.context_var_types_by_id.get(&vid))
                    .map(|s| s.as_str())
                    .or_else(|| self.context.context_var_types.get(name).map(|s| s.as_str()));

                var_type
                    .and_then(SumTypeId::from_display_name)
                    .and_then(|type_id| sum_type_constructor_names(type_id, version))
            }
            PseudoExpr::FieldAccess { selector, .. } => match selector.as_pretty_name() {
                "purpose" => match version {
                    ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2 => {
                        sum_type_constructor_names(SumTypeId::Purpose, version)
                    }
                    ScriptVersion::PlutusV3 => Some(PURPOSE_V3_NAMES),
                },
                "script_info" => sum_type_constructor_names(SumTypeId::ScriptInfo, version),
                _ => None,
            },
            _ => None,
        }
    }

    /// Name well-known constructor patterns (Bool, Option) in when clauses.
    ///
    /// Recognizes:
    /// 2-clause when with Constr<0>()/Constr<1>() → False/True
    /// 2-clause when with Constr<0>(field)/Constr<1>() → Some/None
    pub(super) fn name_known_constructors(clauses: Vec<WhenClause>) -> Vec<WhenClause> {
        if clauses.is_empty() {
            return clauses;
        }

        let mut summary = KnownConstructorPatternSummary {
            all_unnamed: true,
            wildcard_is_fail_only: true,
            ..KnownConstructorPatternSummary::default()
        };

        for clause in &clauses {
            match &clause.pattern {
                WhenPattern::Constructor {
                    shape: ConstructorShape::Known(_),
                    ..
                } => {
                    summary.all_unnamed = false;
                    break;
                }
                WhenPattern::Constructor {
                    shape: ConstructorShape::Unknown { .. },
                    tag,
                    fields,
                    ..
                } => {
                    summary.constructor_clause_count += 1;
                    summary.has_false_ctor |= *tag == 0 && fields.is_empty();
                    summary.has_true_ctor |= *tag == 1 && fields.is_empty();
                    summary.has_some_ctor |= *tag == 0 && fields.len() == 1;
                    summary.has_none_ctor |= *tag == 1 && fields.is_empty();
                }
                WhenPattern::Wildcard | WhenPattern::Var(_) => {
                    summary.wildcard_is_fail_only &= Self::is_fail(&clause.body);
                }
                _ => {}
            }
        }

        if !summary.all_unnamed {
            return clauses;
        }

        if summary.constructor_clause_count == 2
            && (clauses.len() == 2 || summary.wildcard_is_fail_only)
        {
            if summary.has_false_ctor && summary.has_true_ctor {
                return clauses
                    .into_iter()
                    .map(|c| match c.pattern {
                        // Only UNWITNESSED arms (`church_true: None`) take the
                        // CIP `Known(False/True)` labels. An arm carrying
                        // `church_true: Some(_)` stays `Unknown`, so that
                        // `summary.rs` orients true/false by THIS bool's own
                        // convention.
                        WhenPattern::Constructor {
                            tag: 0,
                            fields,
                            shape:
                                ConstructorShape::Unknown {
                                    church_true: None, ..
                                },
                            type_hint: None,
                        } if fields.is_empty() => WhenClause {
                            pattern: WhenPattern::constructor_known(
                                KnownConstructor::False,
                                fields,
                            ),
                            ..c
                        },
                        WhenPattern::Constructor {
                            tag: 1,
                            fields,
                            shape:
                                ConstructorShape::Unknown {
                                    church_true: None, ..
                                },
                            type_hint: None,
                        } if fields.is_empty() => WhenClause {
                            pattern: WhenPattern::constructor_known(KnownConstructor::True, fields),
                            ..c
                        },
                        _ => c,
                    })
                    .collect();
            }

            if summary.has_some_ctor && summary.has_none_ctor {
                return clauses
                    .into_iter()
                    .map(|c| match c.pattern {
                        // Mirrors the Bool path: never flatten an arm carrying
                        // `church_true: Some(_)` to `Known(Some/None)`, which
                        // would discard the per-bool convention. Unreachable
                        // today — a witnessed church bool has two NULLARY {0,1}
                        // arms and takes the Bool path — but the guard keeps
                        // the asymmetry from becoming a latent trap.
                        WhenPattern::Constructor {
                            tag: 0,
                            ref fields,
                            shape:
                                ConstructorShape::Unknown {
                                    church_true: None, ..
                                },
                            type_hint: None,
                        } if fields.len() == 1 => WhenClause {
                            pattern: WhenPattern::constructor_known(
                                KnownConstructor::Some,
                                fields.clone(),
                            ),
                            ..c
                        },
                        WhenPattern::Constructor {
                            tag: 1,
                            ref fields,
                            shape:
                                ConstructorShape::Unknown {
                                    church_true: None, ..
                                },
                            type_hint: None,
                        } if fields.is_empty() => WhenClause {
                            pattern: WhenPattern::constructor_known(
                                KnownConstructor::None,
                                fields.clone(),
                            ),
                            ..c
                        },
                        _ => c,
                    })
                    .collect();
            }
        }

        clauses
    }

    /// Legacy stringly sum-type name for the subject, stamped as a [`TypeHintId`]
    /// on the patterns so downstream passes (e.g. `disambiguate_constructors`)
    /// see a resolved sum-type context and skip their "unnamed" recognisers.
    ///
    /// In lockstep with [`Self::subject_constructor_names`]: every arm returning
    /// constructor names there returns a matching legacy name here, under the keys
    /// `cardano_context_naming::propagate_types_and_name_constructors` registers,
    /// so render-time lookup resolves through the same `TypeHintId`.
    fn subject_sum_type_display_name(&self, subject: &PseudoExpr) -> Option<Rc<str>> {
        match subject {
            PseudoExpr::Var { name, id, .. } => {
                let context_field_name = id
                    .get()
                    .and_then(|vid| self.context.context_field_names_by_id.get(&vid))
                    .map(|s| s.as_str())
                    .or_else(|| {
                        self.context
                            .context_field_names
                            .get(name)
                            .map(|s| s.as_str())
                    });

                if let Some(field @ ("purpose" | "script_info")) = context_field_name {
                    return Some(Rc::from(field));
                }

                if name == "purpose" || name == "script_info" {
                    return Some(Rc::from(name.as_str()));
                }

                let var_type = id
                    .get()
                    .and_then(|vid| self.context.context_var_types_by_id.get(&vid))
                    .map(|s| s.as_str())
                    .or_else(|| self.context.context_var_types.get(name).map(|s| s.as_str()));

                var_type
                    .and_then(SumTypeId::from_display_name)
                    .map(|type_id| Rc::from(type_id.display_name()))
            }
            PseudoExpr::FieldAccess { selector, .. } => {
                let field = selector.as_pretty_name();
                if matches!(field, "purpose" | "script_info") {
                    Some(Rc::from(field))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Name constructors for subject-known sum types in when clauses, using
    /// [`Self::subject_constructor_names`] and the subject's [`TypeHintId`].
    pub(super) fn name_subject_constructors(
        &self,
        subject: &PseudoExpr,
        clauses: Vec<WhenClause>,
    ) -> SubjectConstructorNamingResult {
        let constructor_names = self
            .subject_constructor_names(subject)
            .expect("subject constructor names resolved before calling name_subject_constructors");

        let hint_name = self.subject_sum_type_display_name(subject);
        let type_hint = hint_name.map(TypeHintId::new);

        let mut has_unnamed_constructors = false;
        let clauses = clauses
            .into_iter()
            .map(|c| match c.pattern {
                WhenPattern::Constructor {
                    tag,
                    fields,
                    shape: ConstructorShape::Unknown { .. },
                    type_hint: None,
                } => {
                    let ctor_name = constructor_names.get(tag).map(|s| Rc::from(*s));
                    has_unnamed_constructors |= ctor_name.is_none();
                    let shape = ConstructorShape::from_name_and_tag(
                        ctor_name.as_deref(),
                        tag,
                        fields.len(),
                    );
                    WhenClause {
                        pattern: WhenPattern::Constructor {
                            type_hint: type_hint.clone(),
                            tag,
                            fields,
                            shape,
                        },
                        ..c
                    }
                }
                _ => c,
            })
            .collect();

        SubjectConstructorNamingResult {
            clauses,
            has_unnamed_constructors,
        }
    }
}
