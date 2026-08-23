#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::decompile) enum PipelineProperty {
    RenamedVariables,
    UniqueLetNames,
    ValidatorParamNamesRenamed,
    TypeConstraintsSolved,
    TypesPropagated,
    CardanoFieldNamesResolved,
    /// Every `Var.id` equals the `VarId` of its nearest in-scope
    /// same-name binder. Produced by `retarget_refs_by_scope`;
    /// required by passes that reason on ids alone
    /// (`normalize_display_rewrites`, `assign_names`); invalidated
    /// by passes that clone/move subtrees or rename binders without
    /// retargeting refs (simplify_*, inline_*, hoist_*). A naming
    /// pass that preserves it must require it explicitly rather than
    /// repair stale input implicitly.
    ConsistentRefIds,
}

impl PipelineProperty {
    fn bit(self) -> u16 {
        match self {
            Self::RenamedVariables => 1 << 0,
            Self::UniqueLetNames => 1 << 1,
            Self::ValidatorParamNamesRenamed => 1 << 2,
            Self::TypeConstraintsSolved => 1 << 3,
            Self::TypesPropagated => 1 << 4,
            Self::CardanoFieldNamesResolved => 1 << 5,
            Self::ConsistentRefIds => 1 << 6,
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::RenamedVariables => "renamed_variables",
            Self::UniqueLetNames => "unique_let_names",
            Self::ValidatorParamNamesRenamed => "validator_param_names_renamed",
            Self::TypeConstraintsSolved => "type_constraints_solved",
            Self::TypesPropagated => "types_propagated",
            Self::CardanoFieldNamesResolved => "cardano_field_names_resolved",
            Self::ConsistentRefIds => "consistent_ref_ids",
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub(in crate::decompile) struct PipelinePropertySet {
    bits: u16,
}

impl PipelinePropertySet {
    pub(in crate::decompile) fn insert(&mut self, prop: PipelineProperty) {
        self.bits |= prop.bit();
    }

    pub(in crate::decompile) fn insert_all(&mut self, props: &'static [PipelineProperty]) {
        for prop in props {
            self.bits |= prop.bit();
        }
    }

    pub(in crate::decompile) fn remove_all(&mut self, props: &'static [PipelineProperty]) {
        for prop in props {
            self.bits &= !prop.bit();
        }
    }

    pub(in crate::decompile) fn satisfies(&self, props: &'static [PipelineProperty]) -> bool {
        props.iter().all(|prop| self.bits & prop.bit() != 0)
    }

    pub(in crate::decompile) fn missing_labels(
        &self,
        props: &'static [PipelineProperty],
    ) -> Vec<&'static str> {
        props
            .iter()
            .filter(|prop| self.bits & prop.bit() == 0)
            .map(|prop| prop.label())
            .collect()
    }
}

#[derive(Debug, Clone, Copy)]
pub(in crate::decompile) struct PassContract {
    pub(in crate::decompile) requires: &'static [PipelineProperty],
    pub(in crate::decompile) produces: &'static [PipelineProperty],
    pub(in crate::decompile) invalidates: &'static [PipelineProperty],
}

impl PassContract {
    const fn new(
        requires: &'static [PipelineProperty],
        produces: &'static [PipelineProperty],
        invalidates: &'static [PipelineProperty],
    ) -> Self {
        Self {
            requires,
            produces,
            invalidates,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct PipelinePassMeta {
    label: &'static str,
    contract: PassContract,
}

const NO_PROPERTIES: &[PipelineProperty] = &[];
const PROPAGATED_TYPE_PROPERTIES: &[PipelineProperty] = &[
    PipelineProperty::TypesPropagated,
    PipelineProperty::CardanoFieldNamesResolved,
];
const PROPAGATED_TYPE_AND_CONSISTENT_REF_ID_PROPERTIES: &[PipelineProperty] = &[
    PipelineProperty::TypesPropagated,
    PipelineProperty::CardanoFieldNamesResolved,
    PipelineProperty::ConsistentRefIds,
];
const FIELD_NAME_PROPERTIES: &[PipelineProperty] = &[PipelineProperty::CardanoFieldNamesResolved];
const FIELD_NAME_AND_CONSISTENT_REF_ID_PROPERTIES: &[PipelineProperty] = &[
    PipelineProperty::CardanoFieldNamesResolved,
    PipelineProperty::ConsistentRefIds,
];
const TYPE_NO_REF_PROPERTIES: &[PipelineProperty] = &[
    PipelineProperty::TypeConstraintsSolved,
    PipelineProperty::TypesPropagated,
    PipelineProperty::CardanoFieldNamesResolved,
];
const TYPE_AND_CONSISTENT_REF_ID_PROPERTIES: &[PipelineProperty] = &[
    PipelineProperty::TypeConstraintsSolved,
    PipelineProperty::TypesPropagated,
    PipelineProperty::CardanoFieldNamesResolved,
    PipelineProperty::ConsistentRefIds,
];
const UNIQUE_LET_AND_CONSISTENT_REF_ID_PROPERTIES: &[PipelineProperty] = &[
    PipelineProperty::UniqueLetNames,
    PipelineProperty::ConsistentRefIds,
];
const RENAMED_VARIABLES_AND_UNIQUE_LET_PROPERTIES: &[PipelineProperty] = &[
    PipelineProperty::RenamedVariables,
    PipelineProperty::UniqueLetNames,
];
const UNIQUE_LET_PROPERTIES: &[PipelineProperty] = &[PipelineProperty::UniqueLetNames];
const VALIDATOR_PARAM_NAMES_RENAMED_PROPERTY: &[PipelineProperty] =
    &[PipelineProperty::ValidatorParamNamesRenamed];
const SOLVED_TYPE_PROPERTY: &[PipelineProperty] = &[PipelineProperty::TypeConstraintsSolved];
const SOLVED_TYPE_AND_VALIDATOR_PARAM_PROPERTIES: &[PipelineProperty] = &[
    PipelineProperty::TypeConstraintsSolved,
    PipelineProperty::ValidatorParamNamesRenamed,
];
const PROPAGATED_TYPE_PROPERTY: &[PipelineProperty] = &[PipelineProperty::TypesPropagated];
const PROPAGATED_TYPE_AND_VALIDATOR_PARAM_PROPERTIES: &[PipelineProperty] = &[
    PipelineProperty::TypesPropagated,
    PipelineProperty::ValidatorParamNamesRenamed,
];
const CONSISTENT_REF_IDS_PROPERTY: &[PipelineProperty] = &[PipelineProperty::ConsistentRefIds];

macro_rules! define_pipeline_passes {
    (
        $(
            $variant:ident => $label:literal {
                requires: $requires:expr,
                produces: $produces:expr,
                invalidates: $invalidates:expr
            }
        ),+ $(,)?
    ) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub(in crate::decompile) enum PipelinePassId {
            $($variant),+
        }

        impl PipelinePassId {
            #[cfg(test)]
            pub(in crate::decompile) const ALL: &'static [Self] = &[
                $(Self::$variant),+
            ];

            fn meta(self) -> PipelinePassMeta {
                match self {
                    $(
                        Self::$variant => PipelinePassMeta {
                            label: $label,
                            contract: PassContract::new($requires, $produces, $invalidates),
                        }
                    ),+
                }
            }

            pub(in crate::decompile) fn label(self) -> &'static str {
                self.meta().label
            }

            pub(in crate::decompile) fn contract(self) -> PassContract {
                self.meta().contract
            }
        }
    };
}

define_pipeline_passes! {
    LowerMir => "lower_mir" {
        requires: NO_PROPERTIES,
        produces: NO_PROPERTIES,
        invalidates: NO_PROPERTIES
    },
    RenameVariables => "rename_variables" {
        requires: NO_PROPERTIES,
        produces: RENAMED_VARIABLES_AND_UNIQUE_LET_PROPERTIES,
        invalidates: NO_PROPERTIES
    },
    DeduplicateVarIdsForTypeRefinement => "deduplicate_var_ids_for_type_refinement" {
        requires: NO_PROPERTIES,
        produces: NO_PROPERTIES,
        invalidates: TYPE_AND_CONSISTENT_REF_ID_PROPERTIES
    },
    SolveTypeConstraints => "solve_type_constraints" {
        requires: NO_PROPERTIES,
        produces: SOLVED_TYPE_PROPERTY,
        invalidates: PROPAGATED_TYPE_PROPERTIES
    },
    SolveTypeConstraintsLate => "solve_type_constraints_late" {
        requires: NO_PROPERTIES,
        produces: SOLVED_TYPE_PROPERTY,
        invalidates: PROPAGATED_TYPE_PROPERTIES
    },
    SolveTypeConstraintsPostLateStructural => "solve_type_constraints_post_late_structural" {
        requires: NO_PROPERTIES,
        produces: SOLVED_TYPE_PROPERTY,
        invalidates: PROPAGATED_TYPE_PROPERTIES
    },
    PropagateTypes => "propagate_types" {
        requires: SOLVED_TYPE_AND_VALIDATOR_PARAM_PROPERTIES,
        produces: PROPAGATED_TYPE_PROPERTY,
        invalidates: FIELD_NAME_PROPERTIES
    },
    PropagateTypesLate => "propagate_types_late" {
        requires: SOLVED_TYPE_AND_VALIDATOR_PARAM_PROPERTIES,
        produces: PROPAGATED_TYPE_PROPERTY,
        invalidates: FIELD_NAME_PROPERTIES
    },
    PropagateTypesPostLateStructural => "propagate_types_post_late_structural" {
        requires: SOLVED_TYPE_AND_VALIDATOR_PARAM_PROPERTIES,
        produces: PROPAGATED_TYPE_PROPERTY,
        invalidates: FIELD_NAME_PROPERTIES
    },
    ResolveCardanoFieldNames => "resolve_cardano_field_names" {
        requires: PROPAGATED_TYPE_AND_VALIDATOR_PARAM_PROPERTIES,
        produces: FIELD_NAME_PROPERTIES,
        invalidates: NO_PROPERTIES
    },
    ResolveCardanoFieldNamesLate => "resolve_cardano_field_names_late" {
        requires: PROPAGATED_TYPE_AND_VALIDATOR_PARAM_PROPERTIES,
        produces: FIELD_NAME_PROPERTIES,
        invalidates: NO_PROPERTIES
    },
    ResolveCardanoFieldNamesPostLateStructural => "resolve_cardano_field_names_post_late_structural" {
        requires: PROPAGATED_TYPE_AND_VALIDATOR_PARAM_PROPERTIES,
        produces: FIELD_NAME_PROPERTIES,
        invalidates: NO_PROPERTIES
    },
    StructuralFinalCleanup => "structural_final_cleanup" {
        requires: NO_PROPERTIES,
        produces: CONSISTENT_REF_IDS_PROPERTY,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    DeduplicateVarIdsFinal => "deduplicate_var_ids_final" {
        requires: NO_PROPERTIES,
        produces: NO_PROPERTIES,
        invalidates: TYPE_AND_CONSISTENT_REF_ID_PROPERTIES
    },
    SolveTypeConstraintsFinal => "solve_type_constraints_final" {
        requires: NO_PROPERTIES,
        produces: SOLVED_TYPE_PROPERTY,
        invalidates: PROPAGATED_TYPE_PROPERTIES
    },
    BoolConstrCollapseFinal => "bool_constr_collapse_final" {
        requires: SOLVED_TYPE_PROPERTY,
        produces: NO_PROPERTIES,
        // Rewrites only `When → If` shapes and reads the solved
        // table read-only, so the SOLVED type property stays
        // intact for `propagate_types_final` downstream.
        invalidates: NO_PROPERTIES
    },
    PropagateTypesFinal => "propagate_types_final" {
        requires: SOLVED_TYPE_AND_VALIDATOR_PARAM_PROPERTIES,
        produces: PROPAGATED_TYPE_PROPERTY,
        invalidates: FIELD_NAME_PROPERTIES
    },
    ResolveCardanoFieldNamesFinal => "resolve_cardano_field_names_final" {
        requires: PROPAGATED_TYPE_AND_VALIDATOR_PARAM_PROPERTIES,
        produces: FIELD_NAME_PROPERTIES,
        invalidates: NO_PROPERTIES
    },
    InlineDanglingFieldAliases => "inline_dangling_field_aliases" {
        requires: FIELD_NAME_AND_CONSISTENT_REF_ID_PROPERTIES,
        produces: NO_PROPERTIES,
        invalidates: TYPE_AND_CONSISTENT_REF_ID_PROPERTIES
    },
    DefaultNamelessPostPipeline => "default_nameless_post_pipeline" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: CONSISTENT_REF_IDS_PROPERTY,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    UniquifyFinal => "uniquify_final" {
        requires: NO_PROPERTIES,
        produces: UNIQUE_LET_PROPERTIES,
        invalidates: NO_PROPERTIES
    },
    Simplify1 => "simplify_1" {
        requires: NO_PROPERTIES,
        produces: UNIQUE_LET_AND_CONSISTENT_REF_ID_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    InlineSingleUse => "inline_single_use" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    Simplify2 => "simplify_2" {
        requires: NO_PROPERTIES,
        produces: UNIQUE_LET_AND_CONSISTENT_REF_ID_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    InlineFp => "inline_fp" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: UNIQUE_LET_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    SimplifyFp => "simplify_fp" {
        requires: NO_PROPERTIES,
        produces: UNIQUE_LET_AND_CONSISTENT_REF_ID_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    ConvertExpectTag => "convert_expect_tag" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    RecoverLetBoundTagIfDispatch => "recover_let_bound_tag_if_dispatch" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: NO_PROPERTIES
    },
    ResolveFieldAccesses => "resolve_field_accesses" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    RenameValidatorParams => "rename_validator_params" {
        requires: NO_PROPERTIES,
        produces: VALIDATOR_PARAM_NAMES_RENAMED_PROPERTY,
        invalidates: PROPAGATED_TYPE_AND_CONSISTENT_REF_ID_PROPERTIES
    },
    CollapseTailChains => "collapse_tail_chains" {
        requires: UNIQUE_LET_AND_CONSISTENT_REF_ID_PROPERTIES,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    StripCosmeticDelays => "strip_cosmetic_delays" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    CancelForceDelayVars => "cancel_force_delay_vars" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    NormalizeListConsLiterals => "normalize_list_cons_literals" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    EliminateCpsSelectors => "eliminate_cps_selectors" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    ResolveScottConstructorLambdas => "resolve_scott_constructor_lambdas" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    ResolveDataConstr => "resolve_data_constr" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    LiftUnpackTagWhenSubjects => "lift_unpack_tag_when_subjects" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    DestructureWhenFields => "destructure_when_fields" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    SimplifyDoubleRecFn => "simplify_double_rec_fn" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    RecoverPairFixpoint => "recover_pair_fixpoint" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    SimplifyZCombinator => "simplify_z_combinator" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    ExtractComplexWhenSubjects => "extract_complex_when_subjects" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: UNIQUE_LET_AND_CONSISTENT_REF_ID_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    CollapseEtaPairSelectorWhenSubjects => "collapse_eta_pair_selector_when_subjects" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    ResolveExpectConstrUnpack => "resolve_expect_constr_unpack" {
        requires: UNIQUE_LET_AND_CONSISTENT_REF_ID_PROPERTIES,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    DisambiguateConstructors => "disambiguate_constructors" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    SimplifyBooleanAndIdentity => "simplify_boolean_and_identity" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    ResolveImmediateApplications => "resolve_immediate_applications" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: UNIQUE_LET_AND_CONSISTENT_REF_ID_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    ResolveDataCase => "resolve_data_case" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    EliminateDeadLets => "eliminate_dead_lets" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    ImproveVariableNames => "improve_variable_names" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: NO_PROPERTIES
    },
    FlattenLetChains => "flatten_let_chains" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    InlinePostReadability => "inline_post_readability" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: UNIQUE_LET_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    SimplifyPostReadability => "simplify_post_readability" {
        requires: NO_PROPERTIES,
        produces: NO_PROPERTIES,
        invalidates: TYPE_AND_CONSISTENT_REF_ID_PROPERTIES
    },
    FlattenLetChainsPostInline => "flatten_let_chains_post_inline" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    EliminateCpsSelectorsPostReadability => "eliminate_cps_selectors_post_readability" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    SimplifyBooleanAndIdentityPostReadability => "simplify_boolean_and_identity_post_readability" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    CollapseEtaPairSelectorWhenSubjectsPostReadability => "collapse_eta_pair_selector_when_subjects_post_readability" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    FlattenLetChainsPostReadability => "flatten_let_chains_post_readability" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    HoistLocalHelpers => "hoist_local_helpers" {
        requires: UNIQUE_LET_AND_CONSISTENT_REF_ID_PROPERTIES,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    ExtractHeavyConstants => "extract_heavy_constants" {
        requires: UNIQUE_LET_AND_CONSISTENT_REF_ID_PROPERTIES,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    RetargetRefsByScope => "retarget_refs_by_scope" {
        requires: NO_PROPERTIES,
        produces: CONSISTENT_REF_IDS_PROPERTY,
        invalidates: NO_PROPERTIES
    },
    NormalizeDisplayRewrites => "normalize_display_rewrites" {
        requires: UNIQUE_LET_AND_CONSISTENT_REF_ID_PROPERTIES,
        produces: NO_PROPERTIES,
        invalidates: TYPE_AND_CONSISTENT_REF_ID_PROPERTIES
    },
    HoistLocalHelpersPostNormalize => "hoist_local_helpers_post_normalize" {
        requires: UNIQUE_LET_AND_CONSISTENT_REF_ID_PROPERTIES,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    ImproveVariableNamesPostLate => "improve_variable_names_post_late" {
        requires: UNIQUE_LET_AND_CONSISTENT_REF_ID_PROPERTIES,
        produces: NO_PROPERTIES,
        invalidates: NO_PROPERTIES
    },
    ResolveScottConstructorLambdasLate => "resolve_scott_constructor_lambdas_late" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    ResolveImmediateApplicationsLate => "resolve_immediate_applications_late" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: UNIQUE_LET_AND_CONSISTENT_REF_ID_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    ResolveDataCaseLate => "resolve_data_case_late" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    },
    SimplifyBooleanAndIdentityLate => "simplify_boolean_and_identity_late" {
        requires: CONSISTENT_REF_IDS_PROPERTY,
        produces: NO_PROPERTIES,
        invalidates: TYPE_NO_REF_PROPERTIES
    }
}

#[cfg(test)]
mod tests;
