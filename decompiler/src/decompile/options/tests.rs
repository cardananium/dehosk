//! Each test here pins something the macro CANNOT pin.
//!
//! The macro already makes "a field with no catalogue entry"
//! impossible — the struct and the entry are one piece of source text.
//! What it cannot notice is a correctly-declared field that was never
//! wired into the value reader, a choice list gone short against its
//! Rust enum, or a container's path literal that stopped matching the
//! field holding it.

use std::collections::BTreeSet;

use super::*;
use crate::decompile::validator_meta::ValidatorPurpose;
use crate::decompile::validator_shape::{AppliedKind, ScriptKind, SplitPurposes};
use crate::decompile::{DecompileOptions, OutputLayer, ScriptVersion};

/// Every state the catalogue says an option has must survive a write
/// and read back as itself.
///
/// This is the layer that catches `field: _`, the escape hatch rustc
/// suggests when the total destructure in `values` stops compiling.
/// It builds clean, but a field that took it while claiming a UI
/// control fails here: `get` returns `None` for a path the reader
/// never produced.
#[test]
fn every_ui_entry_is_readable_and_writable() {
    for entry in ui_options() {
        let (label, _, kind, _) = entry.ui().expect("ui_options yields only Ui entries");
        let path = entry.path;
        let mut opts = DecompileOptions::default();

        assert!(
            opts.get(path).is_some(),
            "`{}` ({label}) is in the catalogue but `DecompileOptions::values` never produces it \
             — the field is probably ignored as `{}: _` in the total destructure",
            path.join("."),
            entry.field,
        );

        match kind {
            OptionKind::Toggle => {
                for want in [true, false] {
                    opts.set(path, OptionValue::Bool(want))
                        .unwrap_or_else(|e| panic!("set {}: {e}", path.join(".")));
                    assert_eq!(
                        opts.get(path),
                        Some(OptionValue::Bool(want)),
                        "`{}` did not read back the boolean it was written",
                        path.join("."),
                    );
                }
            }
            OptionKind::Choice { choices, unset } => {
                if unset.is_some() {
                    opts.set(path, OptionValue::Choice(None))
                        .unwrap_or_else(|e| panic!("set {} unset: {e}", path.join(".")));
                    assert_eq!(
                        opts.get(path),
                        Some(OptionValue::Choice(None)),
                        "`{}` declares an `unset` state that does not read back",
                        path.join("."),
                    );
                }
                for choice in choices {
                    opts.set(path, OptionValue::Choice(Some(choice.value)))
                        .unwrap_or_else(|e| {
                            panic!("set {} = {}: {e}", path.join("."), choice.value)
                        });
                    let want = match choice.payload {
                        // Picking a count-carrying choice with no count
                        // stores the declared default.
                        Some(ChoicePayload::Count { default, .. }) => OptionValue::Count(default),
                        None => OptionValue::Choice(Some(choice.value)),
                    };
                    assert_eq!(
                        opts.get(path),
                        Some(want),
                        "`{}` did not read back the choice `{}` it was written",
                        path.join("."),
                        choice.value,
                    );
                    if let Some(ChoicePayload::Count { min, .. }) = choice.payload {
                        opts.set(path, OptionValue::Count(min))
                            .unwrap_or_else(|e| panic!("set {} count: {e}", path.join(".")));
                        assert_eq!(
                            opts.get(path),
                            Some(OptionValue::Count(min)),
                            "`{}` did not read back the count it was written",
                            path.join("."),
                        );
                    }
                }
            }
        }
    }
}

/// The crate's own default for every exposed option has to be a value
/// the catalogue describes — otherwise a UI cannot render the state the
/// server starts in.
///
/// The catalogue declares no default of its own, deliberately: one
/// runtime read of `DecompileOptions::default()` cannot disagree with
/// itself, a second declared copy can. So what this pins is that the
/// declared CHOICE SET covers the default the crate actually holds.
#[test]
fn catalogue_choices_cover_every_crate_default() {
    let defaults = DecompileOptions::default();
    for entry in ui_options() {
        let (label, _, kind, _) = entry.ui().expect("ui_options yields only Ui entries");
        let value = defaults
            .get(entry.path)
            .unwrap_or_else(|| panic!("`{}` ({label}) is unreadable", entry.path.join(".")));
        match (kind, value) {
            (OptionKind::Toggle, OptionValue::Bool(_)) => {}
            (OptionKind::Choice { unset, .. }, OptionValue::Choice(None)) => assert!(
                unset.is_some(),
                "`{}` defaults to unset but declares no `unset` label",
                entry.path.join("."),
            ),
            (OptionKind::Choice { choices, .. }, OptionValue::Choice(Some(token))) => assert!(
                choices.iter().any(|c| c.value == token),
                "`{}` defaults to `{token}`, which is not one of its declared choices {:?}",
                entry.path.join("."),
                choices.iter().map(|c| c.value).collect::<Vec<_>>(),
            ),
            (OptionKind::Choice { choices, .. }, OptionValue::Count(_)) => assert!(
                choices
                    .iter()
                    .any(|c| matches!(c.payload, Some(ChoicePayload::Count { .. }))),
                "`{}` defaults to a count but no declared choice carries one",
                entry.path.join("."),
            ),
            (kind, value) => panic!(
                "`{}` is declared {kind:?} but reads back as {value:?}",
                entry.path.join("."),
            ),
        }
    }
}

/// A nested struct writes its own path prefix as a literal, one level
/// away from the field that holds it. Renaming either one alone leaves
/// a path that addresses nothing.
#[test]
fn nested_member_paths_start_with_container() {
    fn check(entries: &'static [OptionEntry]) {
        for entry in entries {
            if let Exposure::Nested { members } = entry.exposure {
                for member in members {
                    assert!(
                        member.path.starts_with(entry.path),
                        "`{}` is a member of `{}` but its path does not start with the \
                         container's — the `path [...]` literal in its macro invocation has \
                         drifted from the field name",
                        member.path.join("."),
                        entry.path.join("."),
                    );
                    assert_eq!(
                        member.path.len(),
                        entry.path.len() + 1,
                        "`{}` should be exactly one segment below `{}`",
                        member.path.join("."),
                        entry.path.join("."),
                    );
                }
                check(members);
            }
        }
    }
    check(DecompileOptions::ENTRIES);
}

/// Two options addressed by the same path would make one of them
/// unreachable through `get`/`set` and silently unsettable from a UI.
#[test]
fn option_paths_are_unique() {
    let mut seen = BTreeSet::new();
    for entry in ui_options() {
        assert!(
            seen.insert(entry.path.join(".")),
            "duplicate option path `{}`",
            entry.path.join("."),
        );
    }
    assert_eq!(
        seen.len(),
        46,
        "the exposed option count changed; if that is intended, update this number and check \
         that the new option reached the request DTO too",
    );
}

/// Descriptions are the deliverable. A catalogue of names with no prose
/// is the hardcoded panel with an extra hop.
#[test]
fn every_entry_carries_prose() {
    for entry in ui_options() {
        let (label, _, kind, _) = entry.ui().expect("ui_options yields only Ui entries");
        let path = entry.path.join(".");
        assert!(!label.trim().is_empty(), "`{path}` has no label");
        assert!(!entry.summary.trim().is_empty(), "`{path}` has no summary");
        assert!(
            entry.summary.lines().count() == 1,
            "`{path}`'s summary is more than one line",
        );
        if let OptionKind::Choice { choices, .. } = kind {
            assert!(!choices.is_empty(), "`{path}` is a choice with no choices");
            for choice in choices {
                assert!(
                    !choice.label.trim().is_empty(),
                    "`{path}` choice `{}` has no label",
                    choice.value,
                );
                assert!(
                    !choice.summary.trim().is_empty(),
                    "`{path}` choice `{}` has no summary",
                    choice.value,
                );
            }
        }
    }
}

/// A field with no control is a claim about the product; the claim has
/// to be written down.
#[test]
fn internal_fields_state_a_reason() {
    fn check(entries: &'static [OptionEntry]) {
        for entry in entries {
            match entry.exposure {
                Exposure::Internal { reason } => assert!(
                    !reason.trim().is_empty(),
                    "`{}` is internal with an empty reason",
                    entry.path.join("."),
                ),
                Exposure::Nested { members } => check(members),
                Exposure::Ui { .. } => {}
            }
        }
    }
    check(DecompileOptions::ENTRIES);
}

/// `GROUPS` is a hand-written list of section METADATA; the list of
/// section IDS is not — `GroupId::ALL` comes out of the same macro
/// list as the variants, so a new variant is in it by construction and
/// this loop cannot skip it.
///
/// That is why `ALL` is generated: a hand-written `[GroupId; 8]` still
/// type-checks after a ninth variant is added, so this test would find
/// every id it iterates listed, see the two lengths agree, and pass
/// while the ninth group has no heading.
#[test]
fn groups_cover_every_group_id() {
    fn listed(id: GroupId) -> bool {
        GROUPS.iter().any(|g| g.id == id)
    }
    for id in GroupId::ALL {
        assert!(listed(*id), "{id:?} is missing from GROUPS");
    }
    assert_eq!(GROUPS.len(), GroupId::ALL.len(), "GROUPS has a duplicate");

    // The other direction: an option may not claim a section that has no
    // metadata, or it renders under a heading that does not exist.
    for entry in ui_options() {
        let (label, group, _, _) = entry.ui().expect("ui_options yields only Ui entries");
        assert!(
            listed(group),
            "`{}` ({label}) is in {group:?}, which has no OptionGroup",
            entry.path.join("."),
        );
    }
}

/// An empty section renders as a heading with nothing under it.
#[test]
fn every_group_has_at_least_one_option() {
    for group in GROUPS {
        assert!(
            !ui_options_in(group.id).is_empty(),
            "group `{}` has no options",
            group.title,
        );
        assert!(!group.title.trim().is_empty(), "a group has no title");
        assert!(
            !group.summary.trim().is_empty(),
            "group `{}` has no summary",
            group.title,
        );
    }
}

/// A group's master switch has to address the field that actually holds
/// the members, and only the five pass groups have one.
#[test]
fn master_paths_address_a_nested_field() {
    for group in GROUPS {
        let Some(master) = group.master_path else {
            continue;
        };
        let entry = DecompileOptions::ENTRIES
            .iter()
            .find(|e| e.path == master)
            .unwrap_or_else(|| {
                panic!(
                    "group `{}` has master path `{}`, which is not a field",
                    group.title,
                    master.join("."),
                )
            });
        let Exposure::Nested { members } = entry.exposure else {
            panic!(
                "group `{}`'s master path `{}` is not a nested field",
                group.title,
                master.join("."),
            )
        };
        for member in members {
            let (_, member_group, _, _) = member.ui().expect("pass-group leaves are Ui entries");
            assert_eq!(
                member_group,
                group.id,
                "`{}` sits under group `{}`'s master but belongs to {member_group:?}",
                member.path.join("."),
                group.title,
            );
        }
    }
}

// A choice list is a hand-written list beside a Rust enum — the exact
// shape of defect this module exists to remove. Each `wire_token` has
// no `_` arm (a new variant fails the BUILD), and each test below
// asserts the token set equals the offered-choice set (a variant that
// is tokenised but not offered fails the SUITE).

fn offered(choices: &'static [OptionChoice]) -> BTreeSet<&'static str> {
    choices.iter().map(|c| c.value).collect()
}

#[test]
fn script_version_choices_match_the_enum() {
    let tokens: BTreeSet<_> = ScriptVersion::ALL
        .into_iter()
        .map(ScriptVersion::wire_token)
        .collect();
    assert_eq!(tokens, offered(SCRIPT_VERSION_CHOICES));
}

#[test]
fn output_layer_choices_match_the_enum() {
    let tokens: BTreeSet<_> = OutputLayer::ALL
        .into_iter()
        .map(OutputLayer::wire_token)
        .collect();
    assert_eq!(tokens, offered(OUTPUT_LAYER_CHOICES));
}

#[test]
fn purpose_choices_match_the_enum_minus_the_named_exception() {
    let tokens: BTreeSet<_> = ValidatorPurpose::ALL
        .into_iter()
        .map(ValidatorPurpose::wire_token)
        .filter(|t| !PURPOSE_NOT_OFFERED.contains(t))
        .collect();
    assert_eq!(tokens, offered(PURPOSE_CHOICES));
    // The exception is a real variant, not a typo that silently
    // excludes nothing.
    for excluded in PURPOSE_NOT_OFFERED {
        assert!(
            ValidatorPurpose::ALL
                .into_iter()
                .any(|p| p.wire_token() == *excluded),
            "`{excluded}` is excluded from the offered purposes but is not a purpose",
        );
    }
}

/// The purpose token IS the serde tag, not a second spelling of it
/// that happens to agree. `ValidatorPurpose` is the only one of the
/// six choice enums that derives `Serialize`, so it is the only one
/// provable in-crate; the other five are covered by `dehosk-web`'s
/// request-DTO round-trip test.
#[test]
fn purposes_serialise_as_their_wire_token() {
    for purpose in ValidatorPurpose::ALL {
        let json = serde_json::to_value(purpose).expect("ValidatorPurpose is Serialize");
        assert_eq!(
            json,
            serde_json::Value::String(purpose.wire_token().to_string()),
            "{purpose:?}'s wire token is not its serde tag",
        );
    }
}

#[test]
fn split_purposes_choices_match_the_enum() {
    let tokens: BTreeSet<_> = SplitPurposes::ALL
        .into_iter()
        .map(SplitPurposes::wire_token)
        .collect();
    assert_eq!(tokens, offered(SPLIT_PURPOSES_CHOICES));
}

#[test]
fn script_kind_choices_match_the_enum() {
    let tokens: BTreeSet<_> = ScriptKind::ALL
        .into_iter()
        .map(ScriptKind::wire_token)
        .collect();
    assert_eq!(tokens, offered(SCRIPT_KIND_CHOICES));
}

#[test]
fn applied_kind_choices_match_the_enum() {
    let tokens: BTreeSet<_> = AppliedKind::ALL
        .into_iter()
        .map(AppliedKind::wire_token)
        .collect();
    assert_eq!(tokens, offered(APPLIED_KIND_CHOICES));
    // The one variant that carries data must be the one that carries a
    // payload descriptor, or a consumer cannot build its request body.
    let explicit = APPLIED_KIND_CHOICES
        .iter()
        .find(|c| c.value == AppliedKind::RuntimeCount(0).wire_token())
        .expect("the explicit split is offered");
    assert!(
        matches!(explicit.payload, Some(ChoicePayload::Count { .. })),
        "the explicit split carries a count but declares no payload",
    );
}

#[test]
fn set_reports_what_it_refused() {
    let mut opts = DecompileOptions::default();
    assert_eq!(
        opts.set(&["nope"], OptionValue::Bool(true)),
        Err(OptionSetError::UnknownPath("nope".into())),
    );
    assert_eq!(
        opts.set(&["simplify_passes", "nope"], OptionValue::Bool(true)),
        Err(OptionSetError::UnknownPath("simplify_passes.nope".into())),
    );
    assert_eq!(
        opts.set(&["script_version"], OptionValue::Choice(Some("PlutusV9"))),
        Err(OptionSetError::UnknownChoice {
            path: "script_version".into(),
            got: "PlutusV9".into(),
        }),
    );
    assert_eq!(
        opts.set(&["safe_mode"], OptionValue::Choice(Some("nope"))),
        Err(OptionSetError::TypeMismatch {
            path: "safe_mode".into(),
            expected: "a boolean",
        }),
    );
    // A purpose the enum has but the catalogue does not offer is
    // refused, so the offered set is the whole contract.
    assert_eq!(
        opts.set(
            &["validator_shape", "purpose"],
            OptionValue::Choice(Some("Else")),
        ),
        Err(OptionSetError::UnknownChoice {
            path: "validator_shape.purpose".into(),
            got: "Else".into(),
        }),
    );
}

/// `any_enabled` is generated so that it covers every leaf: a leaf left
/// out of the OR makes its group look empty, skipping the whole
/// cluster.
#[test]
fn any_enabled_sees_every_leaf() {
    macro_rules! check_group {
        ($ty:ty, $off:expr) => {
            for entry in <$ty>::ENTRIES {
                let mut group = $off;
                assert!(group.set(entry.field, true));
                assert!(
                    group.any_enabled(),
                    "`{}` alone does not make its group look enabled",
                    entry.path.join("."),
                );
            }
        };
    }
    check_group!(crate::decompile::SimplifyPasses, SimplifyPasses::all_off());
    check_group!(
        crate::decompile::StructuralRecoveryPasses,
        StructuralRecoveryPasses::all_off()
    );
    check_group!(
        crate::decompile::ReadabilityPasses,
        ReadabilityPasses::all_off()
    );
    check_group!(
        crate::decompile::DisplayPolishPasses,
        DisplayPolishPasses::all_off()
    );
    check_group!(crate::decompile::TypePasses, TypePasses::all_off());
}

/// Force a visit to this file whenever a choice enum gains a variant.
///
/// A hand-written `ALL` is a second list the compiler does not tie to the
/// enum: add a variant and the old array literal still type-checks at its
/// old length, so `*_choices_match_the_enum` compares the catalogue against
/// a stale `ALL` and PASSES while the variant is missing from the catalogue
/// and from `set()`.
///
/// The matches below have no `_` arm, so a new variant is `error[E0004]:
/// non-exhaustive patterns` here. That is the guarantee — nobody can add a
/// variant without being sent to this file.
///
/// It is NOT a proof that `ALL` grew: every assertion here iterates `ALL`,
/// and iterating a list can never discover what is missing from it, so
/// adding the arm and leaving `ALL` alone still passes. Closing that gap
/// needs a macro that OWNS the enum declaration, the way `define_group_ids!`
/// owns `GroupId`; these five enums are public API declared elsewhere.
///
/// So when you arrive here from E0004, the edit is TWO lines, not one — the
/// arm below, and the variant in `ALL`.
#[test]
fn every_choice_enum_lists_all_of_its_variants() {
    fn seen<T: Copy>(all: &[T], f: impl Fn(T) -> u8) -> std::collections::BTreeSet<u8> {
        all.iter().copied().map(f).collect()
    }

    let script_version = |v: ScriptVersion| match v {
        ScriptVersion::PlutusV1 => 0u8,
        ScriptVersion::PlutusV2 => 1,
        ScriptVersion::PlutusV3 => 2,
    };
    assert_eq!(seen(&ScriptVersion::ALL, script_version).len(), 3);

    let output_layer = |v: OutputLayer| match v {
        OutputLayer::Decompiled => 0u8,
        OutputLayer::Uplc => 1,
        OutputLayer::UplcCanonical => 2,
        OutputLayer::RawPseudo => 3,
        OutputLayer::PostPipeline => 4,
        OutputLayer::PolarityReport => 5,
        OutputLayer::PrepProfile => 6,
    };
    assert_eq!(seen(&OutputLayer::ALL, output_layer).len(), 7);

    let split = |v: SplitPurposes| match v {
        SplitPurposes::Auto => 0u8,
        SplitPurposes::Always => 1,
        SplitPurposes::Never => 2,
    };
    assert_eq!(seen(&SplitPurposes::ALL, split).len(), 3);

    let kind = |v: ScriptKind| match v {
        ScriptKind::Validator => 0u8,
        ScriptKind::Plain => 1,
    };
    assert_eq!(seen(&ScriptKind::ALL, kind).len(), 2);

    let applied = |v: AppliedKind| match v {
        AppliedKind::Auto => 0u8,
        AppliedKind::Compile => 1,
        AppliedKind::Runtime => 2,
        AppliedKind::RuntimeCount(_) => 3,
    };
    assert_eq!(seen(&AppliedKind::ALL, applied).len(), 4);
}
