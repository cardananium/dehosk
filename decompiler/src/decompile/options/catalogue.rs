//! The descriptor types the option catalogue is built out of.
//!
//! Every string and slice here is `&'static`: static data compiled
//! into the binary. Only [`super::ui_options`] allocates, and only a
//! `Vec` of references.
//!
//! There is ONE entry type — a group is an option field that carries
//! members ([`Exposure::Nested`]), so the five pass groups reach the
//! catalogue through the same list every other field does.

use super::macros::define_group_ids;

define_group_ids! {
    /// Which panel section an option belongs to.
    ///
    /// Five ids match the crate's five pass structs one-for-one; the
    /// other three name the top-level sections the web panel draws with
    /// `border-t` dividers.
    ///
    /// The variants, their wire tokens and [`GroupId::ALL`] come out of
    /// the one list below, so a new section is tokenised and enumerated
    /// by construction. Giving it an [`OptionGroup`] stays manual, and
    /// `groups_cover_every_group_id` fails until that happens.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    GroupId {
        /// Output layer + the surface-rendering toggles.
        PipelineSurface => "pipeline_surface",
        /// Which Plutus version produced the bytecode.
        ScriptIdentification => "script_identification",
        /// How the validator block around the body is shaped.
        ValidatorWrapShape => "validator_wrap_shape",
        /// [`crate::decompile::SimplifyPasses`].
        Simplify => "simplify",
        /// [`crate::decompile::StructuralRecoveryPasses`].
        StructuralRecovery => "structural_recovery",
        /// [`crate::decompile::ReadabilityPasses`].
        Readability => "readability",
        /// [`crate::decompile::DisplayPolishPasses`].
        DisplayPolish => "display_polish",
        /// [`crate::decompile::TypePasses`].
        TypeInference => "type_inference",
    }
}

/// Extra input a choice needs beyond picking it.
///
/// Only `applied_kind`'s explicit split uses one: the count of
/// trailing runtime args
/// ([`crate::decompile::validator_shape::AppliedKind::RuntimeCount`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChoicePayload {
    /// A non-negative count. `key` is the JSON key the count is sent
    /// under inside the option's object form, so a consumer can build
    /// the request body without knowing which option it is looking at.
    Count {
        /// JSON key for the count inside the choice's object form.
        key: &'static str,
        /// Smallest accepted value.
        min: u32,
        /// Value to use when the choice is picked with no count given.
        default: u32,
    },
}

/// One selectable value of a [`OptionKind::Choice`] option.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OptionChoice {
    /// The serde tag, e.g. `"PlutusV3"` — what goes on the wire.
    ///
    /// Never a display string, and never parsed back out of one:
    /// [`crate::decompile::DecompileOptions::set`] resolves an incoming
    /// string by matching it against these declared values.
    pub value: &'static str,
    /// What a UI shows for this choice.
    pub label: &'static str,
    /// One line explaining what picking it does.
    pub summary: &'static str,
    /// Extra input this choice needs, if any.
    pub payload: Option<ChoicePayload>,
}

/// What kind of control an option is.
///
/// A new variant here is a compile error at every exhaustive `match`
/// that maps a kind onto a wire form — which is the point: a kind with
/// no wire mapping must not reach a consumer.
#[derive(Debug, Clone, Copy)]
pub enum OptionKind {
    /// An on/off switch.
    Toggle,
    /// A pick-one-of-N.
    Choice {
        /// The values on offer, in display order.
        choices: &'static [OptionChoice],
        /// Label for "no value" when the field is an `Option<_>`;
        /// `None` when the field always holds one of `choices`.
        unset: Option<&'static str>,
    },
}

/// How a field of the options struct reaches a user — or why it doesn't.
#[derive(Debug, Clone, Copy)]
pub enum Exposure {
    /// A control a user can see and set.
    Ui {
        /// What a UI shows next to the control.
        label: &'static str,
        /// Which section it belongs in.
        group: GroupId,
        /// Toggle or choice.
        kind: OptionKind,
        /// The CLI flag that drives this option, if there is one.
        ///
        /// The flag's polarity may be inverted with respect to the
        /// field — `synthesize_stub_adts` is driven by `--no-stub-adts`
        /// — so this names the flag, it does not describe how to set it.
        cli_flag: Option<&'static str>,
    },
    /// A field that holds a nested struct of further options.
    Nested {
        /// The nested struct's own entries, with their full paths.
        members: &'static [OptionEntry],
    },
    /// A field with no UI control, and the reason there is none.
    ///
    /// The reason is mandatory: a field that nobody can set is a claim
    /// about the product, and the claim should be written down next to
    /// the field rather than inferred from the absence of a control.
    Internal {
        /// Why this field has no control.
        reason: &'static str,
    },
}

/// One field of the options struct, as data.
#[derive(Debug, Clone, Copy)]
pub struct OptionEntry {
    /// The Rust field name.
    pub field: &'static str,
    /// The JSON path from the request root, as data — e.g.
    /// `["simplify_passes", "inline_fp"]`. Never a joined display
    /// string that a consumer would have to split apart again.
    pub path: &'static [&'static str],
    /// One line: what this option does.
    pub summary: &'static str,
    /// The rest of the prose, one entry per line, blank lines kept.
    pub detail: &'static [&'static str],
    /// How this field reaches a user.
    pub exposure: Exposure,
}

impl OptionEntry {
    /// The [`Exposure::Ui`] parts of this entry, or `None` for a nested
    /// or internal field.
    pub fn ui(&self) -> Option<(&'static str, GroupId, OptionKind, Option<&'static str>)> {
        match self.exposure {
            Exposure::Ui {
                label,
                group,
                kind,
                cli_flag,
            } => Some((label, group, kind, cli_flag)),
            Exposure::Nested { .. } | Exposure::Internal { .. } => None,
        }
    }
}

/// A panel section: metadata only. Membership is not listed here — an
/// entry carries its own [`GroupId`] and consumers partition by it, so
/// there is no second list that could disagree with the first.
#[derive(Debug, Clone, Copy)]
pub struct OptionGroup {
    /// Which section this is.
    pub id: GroupId,
    /// Section heading.
    pub title: &'static str,
    /// One line under the heading.
    pub summary: &'static str,
    /// The rest of the prose, one entry per line, blank lines kept.
    pub detail: &'static [&'static str],
    /// Path of the struct field holding this group's members, for the
    /// five pass groups whose panel has an all-on/all-off master
    /// switch. `None` for sections that are only a visual grouping.
    pub master_path: Option<&'static [&'static str]>,
}
