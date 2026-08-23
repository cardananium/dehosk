use super::*;

#[test]
fn from_name_recognizes_each_known_constructor() {
    assert_eq!(
        KnownConstructor::from_name("False"),
        Some(KnownConstructor::False)
    );
    assert_eq!(
        KnownConstructor::from_name("True"),
        Some(KnownConstructor::True)
    );
    assert_eq!(
        KnownConstructor::from_name("None"),
        Some(KnownConstructor::None)
    );
    assert_eq!(
        KnownConstructor::from_name("Some"),
        Some(KnownConstructor::Some)
    );
    assert_eq!(
        KnownConstructor::from_name("Ok"),
        Some(KnownConstructor::Ok)
    );
    assert_eq!(
        KnownConstructor::from_name("Error"),
        Some(KnownConstructor::Error)
    );
    assert_eq!(
        KnownConstructor::from_name("Pair"),
        Some(KnownConstructor::Pair)
    );
    assert_eq!(
        KnownConstructor::from_name("Nil"),
        Some(KnownConstructor::Nil)
    );
    assert_eq!(
        KnownConstructor::from_name("Cons"),
        Some(KnownConstructor::Cons)
    );
    assert_eq!(
        KnownConstructor::from_name("Less"),
        Some(KnownConstructor::Less)
    );
    assert_eq!(
        KnownConstructor::from_name("Equal"),
        Some(KnownConstructor::Equal)
    );
    assert_eq!(
        KnownConstructor::from_name("Greater"),
        Some(KnownConstructor::Greater)
    );
    // Cardano-purpose constructor short names, the form
    assert_eq!(
        KnownConstructor::from_name("Mint"),
        Some(KnownConstructor::Mint)
    );
    assert_eq!(
        KnownConstructor::from_name("Spend"),
        Some(KnownConstructor::Spend)
    );
    assert_eq!(
        KnownConstructor::from_name("Withdraw"),
        Some(KnownConstructor::Withdraw)
    );
    assert_eq!(
        KnownConstructor::from_name("Publish"),
        Some(KnownConstructor::Publish)
    );
    assert_eq!(
        KnownConstructor::from_name("Vote"),
        Some(KnownConstructor::Vote)
    );
    assert_eq!(
        KnownConstructor::from_name("Propose"),
        Some(KnownConstructor::Propose)
    );
    // Void accepts both `Void` and the historical `Unit` alias.
    // `Unit` alias.
    assert_eq!(
        KnownConstructor::from_name("Void"),
        Some(KnownConstructor::Void)
    );
    assert_eq!(
        KnownConstructor::from_name("Unit"),
        Some(KnownConstructor::Void)
    );
}

#[test]
fn from_name_rejects_unknown() {
    assert_eq!(KnownConstructor::from_name(""), None);
    assert_eq!(KnownConstructor::from_name("MyCtor"), None);
    // Case-sensitive — "true" is not "True".
    assert_eq!(KnownConstructor::from_name("true"), None);
    // surface list sugar is not a bare constructor name.
    assert_eq!(KnownConstructor::from_name("[]"), None);
    assert_eq!(KnownConstructor::from_name("::"), None);
}

#[test]
fn pretty_name_round_trips_for_each_variant() {
    for kc in [
        KnownConstructor::False,
        KnownConstructor::True,
        KnownConstructor::None,
        KnownConstructor::Some,
        KnownConstructor::Ok,
        KnownConstructor::Error,
        KnownConstructor::Pair,
        KnownConstructor::Nil,
        KnownConstructor::Cons,
        KnownConstructor::Less,
        KnownConstructor::Equal,
        KnownConstructor::Greater,
        KnownConstructor::Mint,
        KnownConstructor::Spend,
        KnownConstructor::Withdraw,
        KnownConstructor::Publish,
        KnownConstructor::Vote,
        KnownConstructor::Propose,
        KnownConstructor::Void,
    ] {
        assert_eq!(KnownConstructor::from_name(kc.pretty_name()), Some(kc));
    }
}

#[test]
fn expected_tag_and_arity_match_plutus_abi() {
    assert_eq!(KnownConstructor::False.expected_tag(), 0);
    assert_eq!(KnownConstructor::False.expected_arity(), 0);
    assert_eq!(KnownConstructor::True.expected_tag(), 1);
    assert_eq!(KnownConstructor::True.expected_arity(), 0);
    // Standard Option ordering: Some=0 (carries 1 field), None=1 (nullary).
    assert_eq!(KnownConstructor::Some.expected_tag(), 0);
    assert_eq!(KnownConstructor::Some.expected_arity(), 1);
    assert_eq!(KnownConstructor::None.expected_tag(), 1);
    assert_eq!(KnownConstructor::None.expected_arity(), 0);
    assert_eq!(KnownConstructor::Ok.expected_tag(), 0);
    assert_eq!(KnownConstructor::Ok.expected_arity(), 1);
    assert_eq!(KnownConstructor::Error.expected_tag(), 1);
    assert_eq!(KnownConstructor::Error.expected_arity(), 1);
    assert_eq!(KnownConstructor::Pair.expected_tag(), 0);
    assert_eq!(KnownConstructor::Pair.expected_arity(), 2);
    // List tags: []=0, Cons=1. The reversed Plinth/PlutusTx encoding
    // is handled via `ConstructorShape::Unknown`.
    assert_eq!(KnownConstructor::Nil.expected_tag(), 0);
    assert_eq!(KnownConstructor::Nil.expected_arity(), 0);
    assert_eq!(KnownConstructor::Cons.expected_tag(), 1);
    assert_eq!(KnownConstructor::Cons.expected_arity(), 2);
    assert_eq!(KnownConstructor::Less.expected_tag(), 0);
    assert_eq!(KnownConstructor::Less.expected_arity(), 0);
    assert_eq!(KnownConstructor::Equal.expected_tag(), 1);
    assert_eq!(KnownConstructor::Equal.expected_arity(), 0);
    assert_eq!(KnownConstructor::Greater.expected_tag(), 2);
    assert_eq!(KnownConstructor::Greater.expected_arity(), 0);
    // Cardano-purpose variants follow the V1/V2 ScriptPurpose tag
    // layout, extended with V3 ScriptInfo's Voting/Proposing.
    assert_eq!(KnownConstructor::Mint.expected_tag(), 0);
    assert_eq!(KnownConstructor::Mint.expected_arity(), 1);
    assert_eq!(KnownConstructor::Spend.expected_tag(), 1);
    assert_eq!(KnownConstructor::Spend.expected_arity(), 1);
    assert_eq!(KnownConstructor::Withdraw.expected_tag(), 2);
    assert_eq!(KnownConstructor::Withdraw.expected_arity(), 1);
    assert_eq!(KnownConstructor::Publish.expected_tag(), 3);
    assert_eq!(KnownConstructor::Publish.expected_arity(), 1);
    assert_eq!(KnownConstructor::Vote.expected_tag(), 4);
    assert_eq!(KnownConstructor::Vote.expected_arity(), 1);
    assert_eq!(KnownConstructor::Propose.expected_tag(), 5);
    assert_eq!(KnownConstructor::Propose.expected_arity(), 2);
    // Void is `Constr 0 []`, overlapping structurally with `False`/`Nil`
    // /`Less` — disambiguation happens by name rather than by tag/arity.
    assert_eq!(KnownConstructor::Void.expected_tag(), 0);
    assert_eq!(KnownConstructor::Void.expected_arity(), 0);
}

#[test]
fn from_str_and_tag_validates_tag() {
    assert_eq!(
        KnownConstructor::from_str_and_tag("True", 1),
        Some(KnownConstructor::True)
    );
    // Wrong tag → not recognized, even though name is in the set.
    assert_eq!(KnownConstructor::from_str_and_tag("True", 0), None);
    assert_eq!(KnownConstructor::from_str_and_tag("Ok", 1), None);
    // Option tags: Some=0, None=1. The swapped tags are rejected.
    assert_eq!(
        KnownConstructor::from_str_and_tag("Some", 0),
        Some(KnownConstructor::Some)
    );
    assert_eq!(
        KnownConstructor::from_str_and_tag("None", 1),
        Some(KnownConstructor::None)
    );
    assert_eq!(KnownConstructor::from_str_and_tag("Some", 1), None);
    assert_eq!(KnownConstructor::from_str_and_tag("None", 0), None);
    // List tags: []=0, Cons=1. The swapped order is rejected
    // (the `Unknown` path handles reversed lists instead).
    assert_eq!(
        KnownConstructor::from_str_and_tag("Nil", 0),
        Some(KnownConstructor::Nil)
    );
    assert_eq!(
        KnownConstructor::from_str_and_tag("Cons", 1),
        Some(KnownConstructor::Cons)
    );
    assert_eq!(KnownConstructor::from_str_and_tag("Nil", 1), None);
    assert_eq!(KnownConstructor::from_str_and_tag("Cons", 0), None);
    // Ordering tags.
    assert_eq!(
        KnownConstructor::from_str_and_tag("Less", 0),
        Some(KnownConstructor::Less)
    );
    assert_eq!(
        KnownConstructor::from_str_and_tag("Equal", 1),
        Some(KnownConstructor::Equal)
    );
    assert_eq!(
        KnownConstructor::from_str_and_tag("Greater", 2),
        Some(KnownConstructor::Greater)
    );
    // Cardano-purpose tags (V1/V2 ScriptPurpose layout, V3 extras).
    assert_eq!(
        KnownConstructor::from_str_and_tag("Mint", 0),
        Some(KnownConstructor::Mint)
    );
    assert_eq!(
        KnownConstructor::from_str_and_tag("Spend", 1),
        Some(KnownConstructor::Spend)
    );
    assert_eq!(
        KnownConstructor::from_str_and_tag("Withdraw", 2),
        Some(KnownConstructor::Withdraw)
    );
    assert_eq!(
        KnownConstructor::from_str_and_tag("Publish", 3),
        Some(KnownConstructor::Publish)
    );
    assert_eq!(
        KnownConstructor::from_str_and_tag("Vote", 4),
        Some(KnownConstructor::Vote)
    );
    assert_eq!(
        KnownConstructor::from_str_and_tag("Propose", 5),
        Some(KnownConstructor::Propose)
    );
    // Mismatched tags reject — purpose names cannot pose as other tags.
    assert_eq!(KnownConstructor::from_str_and_tag("Spend", 0), None);
    assert_eq!(KnownConstructor::from_str_and_tag("Mint", 1), None);
    // Void accepts both `Void` and the `Unit` alias at
    // tag 0; wrong tag rejects.
    assert_eq!(
        KnownConstructor::from_str_and_tag("Void", 0),
        Some(KnownConstructor::Void)
    );
    assert_eq!(
        KnownConstructor::from_str_and_tag("Unit", 0),
        Some(KnownConstructor::Void)
    );
    assert_eq!(KnownConstructor::from_str_and_tag("Void", 1), None);
}

#[test]
fn from_str_and_tag_rejects_unknown_name() {
    assert_eq!(KnownConstructor::from_str_and_tag("MyCtor", 0), None);
}

#[test]
fn shape_from_name_and_tag_known_path() {
    // Option: Some carries 1 field at tag 0.
    let shape = ConstructorShape::from_name_and_tag(Some("Some"), 0, 1);
    assert_eq!(shape, ConstructorShape::Known(KnownConstructor::Some));
    assert!(shape.is_known());
    assert_eq!(shape.pretty_name(), Some("Some"));
    assert_eq!(shape.tag(), 0);
    assert_eq!(shape.arity(), 1);
}

#[test]
fn shape_from_name_and_tag_falls_back_when_name_missing() {
    let shape = ConstructorShape::from_name_and_tag(None, 7, 3);
    assert_eq!(shape, ConstructorShape::unknown_data(7, 3));
    assert!(!shape.is_known());
    assert_eq!(shape.pretty_name(), None);
    assert_eq!(shape.tag(), 7);
    assert_eq!(shape.arity(), 3);
}

#[test]
fn shape_from_name_and_tag_falls_back_on_unknown_name() {
    let shape = ConstructorShape::from_name_and_tag(Some("MyCtor"), 4, 2);
    assert_eq!(shape, ConstructorShape::unknown_data(4, 2));
}

#[test]
fn shape_from_name_and_tag_falls_back_on_tag_mismatch() {
    // Name says "True" (Constr 1) but data says tag 0 — preserve
    // structural info, drop the (wrong) name.
    let shape = ConstructorShape::from_name_and_tag(Some("True"), 0, 0);
    assert_eq!(shape, ConstructorShape::unknown_data(0, 0));
}

#[test]
fn shape_from_name_and_tag_falls_back_on_arity_mismatch() {
    // Name + tag agree (Some at tag 0), but arity is wrong
    // (Some carries one field, not two).
    let shape = ConstructorShape::from_name_and_tag(Some("Some"), 0, 2);
    assert_eq!(shape, ConstructorShape::unknown_data(0, 2));
}

#[test]
fn shape_known_constructor_helpers() {
    let shape = ConstructorShape::known(KnownConstructor::Pair);
    assert_eq!(shape.tag(), 0);
    assert_eq!(shape.arity(), 2);
    assert_eq!(shape.as_known(), Some(KnownConstructor::Pair));

    let unknown = ConstructorShape::unknown_data(9, 4);
    assert_eq!(unknown.as_known(), None);
}

#[test]
fn candidates_by_tag_arity_covers_each_known_shape() {
    // Overlapping (tag, arity) slots: tag 0 nullary is False / [] / Less;
    // tag 1 nullary is True / None / Equal (Some is tag 0 with 1 field).
    assert_eq!(
        KnownConstructor::candidates_by_tag_arity(0, 0),
        &[
            KnownConstructor::False,
            KnownConstructor::Nil,
            KnownConstructor::Less,
        ]
    );
    assert_eq!(
        KnownConstructor::candidates_by_tag_arity(1, 0),
        &[
            KnownConstructor::True,
            KnownConstructor::None,
            KnownConstructor::Equal,
        ]
    );
    assert_eq!(
        KnownConstructor::candidates_by_tag_arity(2, 0),
        &[KnownConstructor::Greater]
    );
    assert_eq!(
        KnownConstructor::candidates_by_tag_arity(0, 1),
        &[KnownConstructor::Some, KnownConstructor::Ok]
    );
    assert_eq!(
        KnownConstructor::candidates_by_tag_arity(1, 1),
        &[KnownConstructor::Error]
    );
    assert_eq!(
        KnownConstructor::candidates_by_tag_arity(0, 2),
        &[KnownConstructor::Pair]
    );
    assert_eq!(
        KnownConstructor::candidates_by_tag_arity(1, 2),
        &[KnownConstructor::Cons]
    );
}

#[test]
fn candidates_by_tag_arity_is_empty_for_unknown_shapes() {
    assert!(KnownConstructor::candidates_by_tag_arity(3, 0).is_empty());
    assert!(KnownConstructor::candidates_by_tag_arity(2, 2).is_empty());
    assert!(KnownConstructor::candidates_by_tag_arity(5, 3).is_empty());
}

#[test]
fn candidates_by_tag_arity_agrees_with_expected_tag_and_arity() {
    // Drift-invariant: every *structural* `KnownConstructor` is a
    // candidate for its own canonical `(tag, arity)`. Cardano-purpose
    // variants are omitted — see `candidates_by_tag_arity`.
    for kc in [
        KnownConstructor::False,
        KnownConstructor::True,
        KnownConstructor::None,
        KnownConstructor::Some,
        KnownConstructor::Ok,
        KnownConstructor::Error,
        KnownConstructor::Pair,
        KnownConstructor::Nil,
        KnownConstructor::Cons,
        KnownConstructor::Less,
        KnownConstructor::Equal,
        KnownConstructor::Greater,
    ] {
        let candidates =
            KnownConstructor::candidates_by_tag_arity(kc.expected_tag(), kc.expected_arity());
        assert!(
            candidates.contains(&kc),
            "{:?} missing from candidates for its own tag/arity",
            kc
        );
    }
}

#[test]
fn candidates_by_tag_arity_excludes_name_anchored_variants() {
    // Name-anchored variants (Cardano purposes + Void) are NOT
    // structurally disambiguatable, so the slot table must not
    // list them: adding `Mint` to `(0, 1)` or `Void` to `(0, 0)`
    // would silently break the exact-slice matches there.
    for kc in [
        KnownConstructor::Mint,
        KnownConstructor::Spend,
        KnownConstructor::Withdraw,
        KnownConstructor::Publish,
        KnownConstructor::Vote,
        KnownConstructor::Propose,
        KnownConstructor::Void,
    ] {
        let candidates =
            KnownConstructor::candidates_by_tag_arity(kc.expected_tag(), kc.expected_arity());
        assert!(
            !candidates.contains(&kc),
            "Name-anchored variant {:?} unexpectedly present in candidates table",
            kc
        );
    }
}

#[test]
fn recognize_two_branch_adt_bool() {
    assert_eq!(
        KnownConstructor::recognize_two_branch_adt((0, 0), (1, 0)),
        Some((KnownConstructor::False, KnownConstructor::True))
    );
    // Branch order is preserved — swapping inputs swaps outputs.
    assert_eq!(
        KnownConstructor::recognize_two_branch_adt((1, 0), (0, 0)),
        Some((KnownConstructor::True, KnownConstructor::False))
    );
}

#[test]
fn recognize_two_branch_adt_option_and_result() {
    // Option: Some at (tag 0, arity 1), None at (tag 1, arity 0).
    assert_eq!(
        KnownConstructor::recognize_two_branch_adt((0, 1), (1, 0)),
        Some((KnownConstructor::Some, KnownConstructor::None))
    );
    assert_eq!(
        KnownConstructor::recognize_two_branch_adt((1, 0), (0, 1)),
        Some((KnownConstructor::None, KnownConstructor::Some))
    );
    assert_eq!(
        KnownConstructor::recognize_two_branch_adt((0, 1), (1, 1)),
        Some((KnownConstructor::Ok, KnownConstructor::Error))
    );
    assert_eq!(
        KnownConstructor::recognize_two_branch_adt((1, 1), (0, 1)),
        Some((KnownConstructor::Error, KnownConstructor::Ok))
    );
}

#[test]
fn recognize_two_branch_adt_returns_none_for_non_standard_splits() {
    // Same tag on both branches is never a recognized ADT split.
    assert_eq!(
        KnownConstructor::recognize_two_branch_adt((0, 0), (0, 0)),
        None
    );
    // Non-standard (tag, arity) combos.
    assert_eq!(
        KnownConstructor::recognize_two_branch_adt((2, 0), (3, 0)),
        None
    );
    // Tag 0 arity 2 (Pair) paired with anything isn't a two-branch ADT.
    assert_eq!(
        KnownConstructor::recognize_two_branch_adt((0, 2), (1, 0)),
        None
    );
}

#[test]
fn recognize_three_branch_adt_ordering_in_canonical_order() {
    assert_eq!(
        KnownConstructor::recognize_three_branch_adt((0, 0), (1, 0), (2, 0)),
        Some((
            KnownConstructor::Less,
            KnownConstructor::Equal,
            KnownConstructor::Greater,
        ))
    );
}

#[test]
fn recognize_three_branch_adt_preserves_original_branch_order() {
    // Branches may appear in any order in the source — the mapping
    // keeps each returned `KnownConstructor` aligned with its input.
    assert_eq!(
        KnownConstructor::recognize_three_branch_adt((2, 0), (0, 0), (1, 0)),
        Some((
            KnownConstructor::Greater,
            KnownConstructor::Less,
            KnownConstructor::Equal,
        ))
    );
    assert_eq!(
        KnownConstructor::recognize_three_branch_adt((1, 0), (2, 0), (0, 0)),
        Some((
            KnownConstructor::Equal,
            KnownConstructor::Greater,
            KnownConstructor::Less,
        ))
    );
}

#[test]
fn recognize_three_branch_adt_returns_none_for_non_ordering_triples() {
    // Missing tag — not the full Ordering split.
    assert_eq!(
        KnownConstructor::recognize_three_branch_adt((0, 0), (1, 0), (3, 0)),
        None
    );
    // Duplicate tag — can't be three distinct branches of one ADT.
    assert_eq!(
        KnownConstructor::recognize_three_branch_adt((0, 0), (0, 0), (1, 0)),
        None
    );
    // Non-zero arity — Ordering constructors carry no fields.
    assert_eq!(
        KnownConstructor::recognize_three_branch_adt((0, 0), (1, 1), (2, 0)),
        None
    );
}

#[test]
fn display_name_or_prefers_shape_when_known() {
    let shape = ConstructorShape::known(KnownConstructor::Some);
    // Shape's canonical name wins even when a fallback is provided.
    assert_eq!(shape.display_name_or(Some("Other")), Some("Some"));
    assert_eq!(shape.display_name_or(None), Some("Some"));
}

#[test]
fn display_name_or_falls_back_when_unknown() {
    let shape = ConstructorShape::unknown_data(2, 0);
    // Unknown shape has no canonical name — fallback is returned verbatim.
    assert_eq!(shape.display_name_or(Some("Greater")), Some("Greater"));
    assert_eq!(shape.display_name_or(None), None);
}

#[test]
fn shape_is_copy_and_hashable() {
    // Both shapes must stay cheap value types usable in maps and sets.
    use std::collections::HashSet;

    let mut set: HashSet<ConstructorShape> = HashSet::new();
    set.insert(ConstructorShape::known(KnownConstructor::True));
    set.insert(ConstructorShape::unknown_data(5, 0));
    assert_eq!(set.len(), 2);
}
