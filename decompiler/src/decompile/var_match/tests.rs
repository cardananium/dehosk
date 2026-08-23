use super::*;
use crate::pseudo::var_id::VarId;

fn vid(raw: u32) -> VarId {
    VarId::from_raw(raw)
}

fn make_binder_with_id(name: &str, id: VarId) -> Binder {
    Binder::new(name, id)
}

#[test]
fn ref_matches_binder_uses_id_when_present() {
    // Pick an id in the interner range (low values) so id.get() returns Some.
    let b = make_binder_with_id("foo", vid(42));
    assert!(ref_matches_binder("foo", Some(vid(42)), &b));
    // Different name but same id → still matches (id wins).
    assert!(ref_matches_binder("bar", Some(vid(42)), &b));
}

#[test]
fn ref_matches_binder_rejects_different_id() {
    let b = make_binder_with_id("foo", vid(42));
    assert!(!ref_matches_binder("foo", Some(vid(43)), &b));
}

#[test]
fn ref_matches_binder_falls_back_to_name_when_id_none() {
    let b = make_binder_with_id("foo", vid(42));
    assert!(ref_matches_binder("foo", None, &b));
    assert!(!ref_matches_binder("bar", None, &b));
}

#[test]
fn refs_match_id_priority() {
    // Both ids Some and equal → match (names irrelevant).
    assert!(refs_match("a", Some(vid(1)), "b", Some(vid(1))));
    // Both ids Some, different → no match.
    assert!(!refs_match("a", Some(vid(1)), "a", Some(vid(2))));
}

#[test]
fn refs_match_name_fallback_when_one_id_none() {
    assert!(refs_match("foo", Some(vid(1)), "foo", None));
    assert!(refs_match("foo", None, "foo", Some(vid(1))));
    assert!(!refs_match("foo", Some(vid(1)), "bar", None));
}

#[test]
fn refs_match_name_only_when_both_ids_none() {
    assert!(refs_match("foo", None, "foo", None));
    assert!(!refs_match("foo", None, "bar", None));
}

#[test]
fn ids_match_strict_requires_both_some() {
    assert!(ids_match_strict(Some(vid(1)), Some(vid(1))));
    assert!(!ids_match_strict(Some(vid(1)), Some(vid(2))));
    assert!(!ids_match_strict(Some(vid(1)), None));
    assert!(!ids_match_strict(None, Some(vid(1))));
    assert!(!ids_match_strict(None, None));
}

#[test]
fn ref_matches_resolved_target_asymmetric() {
    // Target Some + ref id matches: yes.
    assert!(ref_matches_resolved_target(
        "foo",
        Some(vid(1)),
        "foo",
        Some(vid(1))
    ));
    // Target Some + ref id differs: no, even if names match.
    assert!(!ref_matches_resolved_target(
        "foo",
        Some(vid(2)),
        "foo",
        Some(vid(1))
    ));
    // Target Some + ref id None: no (no name fallback when target is resolved).
    assert!(!ref_matches_resolved_target(
        "foo",
        None,
        "foo",
        Some(vid(1))
    ));
    // Target None: name fallback fires.
    assert!(ref_matches_resolved_target(
        "foo",
        Some(vid(1)),
        "foo",
        None
    ));
    assert!(!ref_matches_resolved_target(
        "foo",
        Some(vid(1)),
        "bar",
        None
    ));
    assert!(ref_matches_resolved_target("foo", None, "foo", None));
}

#[test]
fn ids_compatible_returns_true_when_no_disagreement() {
    assert!(ids_compatible(Some(vid(1)), Some(vid(1))));
    assert!(!ids_compatible(Some(vid(1)), Some(vid(2))));
    // Either None → no disagreement.
    assert!(ids_compatible(Some(vid(1)), None));
    assert!(ids_compatible(None, Some(vid(1))));
    assert!(ids_compatible(None, None));
}

#[test]
fn ref_matches_binder_with_placeholder_binder_id_falls_back_to_name() {
    // A `Binder` may hold a compat-placeholder `VarId`, and
    // `ref_matches_binder` passes `binder.id.get()`, which is
    // `None` for such ids — so matching falls back to the name
    // whatever the ref's id state.
    let placeholder_id = VarId::fresh_compat_placeholder();
    let b = Binder::new("foo", placeholder_id);
    // Ref Some + binder placeholder → mixed Some/None → name fallback.
    assert!(ref_matches_binder("foo", Some(vid(99)), &b));
    assert!(!ref_matches_binder("bar", Some(vid(99)), &b));
    // Ref None + binder placeholder → both None → name fallback.
    assert!(ref_matches_binder("foo", None, &b));
    assert!(!ref_matches_binder("bar", None, &b));
}

#[test]
fn refs_match_paired_rejects_mixed_some_none() {
    // Both Some+equal: match.
    assert!(refs_match_paired("foo", Some(vid(1)), "bar", Some(vid(1))));
    // Both None + name match: match.
    assert!(refs_match_paired("foo", None, "foo", None));
    assert!(!refs_match_paired("foo", None, "bar", None));
    // Mixed: never matches even with same name.
    assert!(!refs_match_paired("foo", Some(vid(1)), "foo", None));
    assert!(!refs_match_paired("foo", None, "foo", Some(vid(1))));
}

// Algebraic invariants — catch silent semantics drift if a
// helper's body is edited later.

#[test]
fn helper_invariants_reflexive_on_identical_input() {
    let cases = [(Some(vid(1)), "a"), (Some(vid(99)), "b"), (None, "c")];
    for (id, name) in cases {
        assert!(refs_match(name, id, name, id), "refs_match reflexive");
        assert!(
            refs_match_paired(name, id, name, id),
            "refs_match_paired reflexive"
        );
        assert!(ids_compatible(id, id), "ids_compatible reflexive");
        if id.is_some() {
            assert!(
                ids_match_strict(id, id),
                "ids_match_strict reflexive when Some"
            );
        }
    }
}

#[test]
fn helper_invariants_symmetric_refs_match() {
    let cases = [
        ("a", Some(vid(1)), "b", Some(vid(2))),
        ("a", Some(vid(1)), "a", None),
        ("a", None, "a", None),
        ("a", None, "b", None),
        ("a", Some(vid(1)), "a", Some(vid(1))),
    ];
    for (an, ai, bn, bi) in cases {
        assert_eq!(refs_match(an, ai, bn, bi), refs_match(bn, bi, an, ai));
        assert_eq!(
            refs_match_paired(an, ai, bn, bi),
            refs_match_paired(bn, bi, an, ai)
        );
        assert_eq!(ids_compatible(ai, bi), ids_compatible(bi, ai));
        assert_eq!(ids_match_strict(ai, bi), ids_match_strict(bi, ai));
    }
}

#[test]
fn helper_invariants_strict_implies_compatible() {
    let cases = [
        (Some(vid(1)), Some(vid(1))),
        (Some(vid(1)), Some(vid(2))),
        (None, Some(vid(1))),
        (Some(vid(1)), None),
        (None, None),
    ];
    for (a, b) in cases {
        if ids_match_strict(a, b) {
            assert!(ids_compatible(a, b));
        }
    }
}

// Property-based tests across the full input space.
proptest::proptest! {
    #[test]
    fn prop_refs_match_reflexive(
        name in ".{0,30}",
        id_raw in proptest::option::of(1u32..1_000_000_u32),
    ) {
        let id_opt = id_raw.map(vid);
        proptest::prop_assert!(refs_match(&name, id_opt, &name, id_opt));
    }

    #[test]
    fn prop_refs_match_symmetric(
        an in ".{0,30}",
        ai in proptest::option::of(1u32..1_000_000_u32),
        bn in ".{0,30}",
        bi in proptest::option::of(1u32..1_000_000_u32),
    ) {
        let ai = ai.map(vid);
        let bi = bi.map(vid);
        proptest::prop_assert_eq!(
            refs_match(&an, ai, &bn, bi),
            refs_match(&bn, bi, &an, ai)
        );
    }

    #[test]
    fn prop_ids_match_strict_implies_compatible(
        ai in proptest::option::of(1u32..1_000_000_u32),
        bi in proptest::option::of(1u32..1_000_000_u32),
    ) {
        let ai = ai.map(vid);
        let bi = bi.map(vid);
        if ids_match_strict(ai, bi) {
            proptest::prop_assert!(ids_compatible(ai, bi));
        }
    }

    #[test]
    fn prop_ids_match_strict_requires_both_some(
        ai in proptest::option::of(1u32..1_000_000_u32),
        bi in proptest::option::of(1u32..1_000_000_u32),
    ) {
        let ai = ai.map(vid);
        let bi = bi.map(vid);
        if ai.is_none() || bi.is_none() {
            proptest::prop_assert!(!ids_match_strict(ai, bi));
        }
    }
}
