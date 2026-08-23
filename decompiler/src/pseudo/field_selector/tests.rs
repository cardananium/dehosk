use super::*;

#[test]
fn from_legacy_name_recognizes_structural_accessors() {
    assert_eq!(
        FieldSelector::from_display_name("fst"),
        FieldSelector::PairFst
    );
    assert_eq!(
        FieldSelector::from_display_name("snd"),
        FieldSelector::PairSnd
    );
    assert_eq!(
        FieldSelector::from_display_name("head"),
        FieldSelector::ListHead
    );
}

#[test]
fn surface_accessor_uses_ordinals_for_pairs() {
    // surface syntax: Pair access is `.1st`/`.2nd`, not `.fst`/`.snd`.
    assert_eq!(FieldSelector::PairFst.as_surface_accessor(), "1st");
    assert_eq!(FieldSelector::PairSnd.as_surface_accessor(), "2nd");
    // Everything else renders as its pretty name.
    assert_eq!(FieldSelector::ListHead.as_surface_accessor(), "head");
    assert_eq!(
        FieldSelector::NamedField("fields".to_string()).as_surface_accessor(),
        "fields"
    );
    // `as_pretty_name` and its round-trip keep `fst`/`snd`.
    assert_eq!(FieldSelector::PairFst.as_pretty_name(), "fst");
    assert_eq!(FieldSelector::PairSnd.as_pretty_name(), "snd");
    assert_eq!(
        FieldSelector::from_display_name(FieldSelector::PairFst.as_pretty_name()),
        FieldSelector::PairFst
    );
}

#[test]
fn from_legacy_name_falls_back_to_named_field() {
    assert_eq!(
        FieldSelector::from_display_name("tag"),
        FieldSelector::NamedField("tag".to_string())
    );
    assert_eq!(
        FieldSelector::from_display_name("fields"),
        FieldSelector::NamedField("fields".to_string())
    );
    assert_eq!(
        FieldSelector::from_display_name("policy_id"),
        FieldSelector::NamedField("policy_id".to_string())
    );
    // Structural names are case-sensitive; uppercase maps to NamedField.
    assert_eq!(
        FieldSelector::from_display_name("Fst"),
        FieldSelector::NamedField("Fst".to_string())
    );
}

#[test]
fn from_legacy_name_never_produces_context_field() {
    // The legacy-string path always falls through to NamedField,
    // even for recognizable Cardano identifiers.
    for name in [
        "transaction",
        "purpose",
        "datum",
        "datum_hash",
        "outputs",
        "policy_id",
        "tx_id",
        "script_info",
    ] {
        assert!(
            !matches!(
                FieldSelector::from_display_name(name),
                FieldSelector::ContextField(_)
            ),
            "legacy {name:?} must not parse to ContextField yet",
        );
    }
}

#[test]
fn as_pretty_name_round_trips_structural_accessors() {
    for s in [
        FieldSelector::PairFst,
        FieldSelector::PairSnd,
        FieldSelector::ListHead,
    ] {
        assert_eq!(FieldSelector::from_display_name(s.as_pretty_name()), s);
    }
}

#[test]
fn as_pretty_name_returns_carried_string_for_named_and_context() {
    assert_eq!(
        FieldSelector::NamedField("tag".to_string()).as_pretty_name(),
        "tag",
    );
    assert_eq!(
        FieldSelector::ContextField("purpose".to_string()).as_pretty_name(),
        "purpose",
    );
}

#[test]
fn is_structural_matches_only_built_in_accessors() {
    assert!(FieldSelector::PairFst.is_structural());
    assert!(FieldSelector::PairSnd.is_structural());
    assert!(FieldSelector::ListHead.is_structural());
    assert!(!FieldSelector::NamedField("tag".to_string()).is_structural());
    assert!(!FieldSelector::ContextField("purpose".to_string()).is_structural());
}

#[test]
fn per_variant_predicates_match_only_their_variant() {
    let fst = FieldSelector::PairFst;
    let snd = FieldSelector::PairSnd;
    let head = FieldSelector::ListHead;
    let named = FieldSelector::NamedField("tag".to_string());

    assert!(fst.is_pair_fst() && !fst.is_pair_snd() && !fst.is_list_head());
    assert!(!snd.is_pair_fst() && snd.is_pair_snd() && !snd.is_list_head());
    assert!(!head.is_pair_fst() && !head.is_pair_snd() && head.is_list_head());
    assert!(!named.is_pair_fst() && !named.is_pair_snd() && !named.is_list_head());
}
