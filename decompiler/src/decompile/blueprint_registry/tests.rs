use super::*;
use crate::pseudo::constructor::KnownConstructor;

#[test]
fn new_registry_is_empty() {
    let reg = BlueprintHintRegistry::new();
    assert!(reg.is_empty());
    assert_eq!(reg.len(), 0);
}

#[test]
fn register_cardano_purpose_inserts_into_purpose_namespace() {
    let mut reg = BlueprintHintRegistry::new();
    reg.register_cardano_purpose(0, "Minting");
    reg.register_cardano_purpose(1, "Spending");
    assert_eq!(reg.len(), 2);
    assert_eq!(
        reg.resolve_cardano(SumTypeId::Purpose, 0).as_deref(),
        Some("Minting")
    );
    assert_eq!(
        reg.resolve_cardano(SumTypeId::Purpose, 1).as_deref(),
        Some("Spending")
    );
    // Other sum types are unaffected.
    assert!(reg.resolve_cardano(SumTypeId::ScriptInfo, 0).is_none());
}

#[test]
fn register_cardano_overwrites_previous_entry() {
    let mut reg = BlueprintHintRegistry::new();
    reg.register_cardano(SumTypeId::ScriptInfo, 0, "OldName");
    reg.register_cardano(SumTypeId::ScriptInfo, 0, "Minting");
    assert_eq!(reg.len(), 1);
    assert_eq!(
        reg.resolve_cardano(SumTypeId::ScriptInfo, 0).as_deref(),
        Some("Minting")
    );
}

#[test]
fn register_user_inserts_into_user_namespace() {
    let mut reg = BlueprintHintRegistry::new();
    let hint = TypeHintId::new("MyAdt");
    reg.register_user(hint.clone(), 0, "Foo");
    reg.register_user(hint.clone(), 1, "Bar");
    assert_eq!(reg.len(), 2);
    let shape = ConstructorShape::unknown_data(0, 0);
    assert_eq!(reg.resolve(shape, Some(&hint)).as_deref(), Some("Foo"));
    let shape1 = ConstructorShape::unknown_data(1, 0);
    assert_eq!(reg.resolve(shape1, Some(&hint)).as_deref(), Some("Bar"));
}

#[test]
fn register_user_accepts_string_and_rc_str() {
    let mut reg = BlueprintHintRegistry::new();
    let hint = TypeHintId::new("MyAdt");
    reg.register_user(hint.clone(), 0, "Foo");
    reg.register_user(hint.clone(), 1, String::from("Bar"));
    reg.register_user(hint.clone(), 2, Rc::<str>::from("Baz"));
    assert_eq!(reg.len(), 3);
    assert_eq!(
        reg.resolve(ConstructorShape::unknown_data(2, 0), Some(&hint),)
            .as_deref(),
        Some("Baz")
    );
}

#[test]
fn resolve_returns_known_canonical_name_when_no_user_hint() {
    let reg = BlueprintHintRegistry::new();
    let shape = ConstructorShape::known(KnownConstructor::Some);
    assert_eq!(reg.resolve(shape, None).as_deref(), Some("Some"));
}

#[test]
fn resolve_returns_none_for_unknown_shape_without_hint() {
    let reg = BlueprintHintRegistry::new();
    let shape = ConstructorShape::unknown_data(4, 0);
    assert_eq!(reg.resolve(shape, None), None);
}

#[test]
fn resolve_user_entry_wins_over_known_canonical_name() {
    // A user hint outranks the closed-set canonical name, so a
    // project can shadow a built-in — a user ADT named `Some`.
    let mut reg = BlueprintHintRegistry::new();
    let hint = TypeHintId::new("UserOption");
    reg.register_user(hint.clone(), 0, "MaybeSome");
    let shape = ConstructorShape::known(KnownConstructor::Some);
    assert_eq!(
        reg.resolve(shape, Some(&hint)).as_deref(),
        Some("MaybeSome")
    );
}

#[test]
fn resolve_falls_back_to_known_name_when_user_lookup_misses() {
    // Hint provided but `(hint, tag)` not registered — fall back to
    // the closed-set canonical name when the shape is `Known(_)`.
    let reg = BlueprintHintRegistry::new();
    let hint = TypeHintId::new("UserAdt");
    let shape = ConstructorShape::known(KnownConstructor::True);
    assert_eq!(reg.resolve(shape, Some(&hint)).as_deref(), Some("True"));
}

#[test]
fn resolve_falls_back_to_none_when_user_lookup_misses_on_unknown_shape() {
    let reg = BlueprintHintRegistry::new();
    let hint = TypeHintId::new("UserAdt");
    let shape = ConstructorShape::unknown_data(5, 0);
    assert_eq!(reg.resolve(shape, Some(&hint)), None);
}

#[test]
fn type_hint_id_distinguishes_distinct_names() {
    let a = TypeHintId::new("Foo");
    let b = TypeHintId::new("Bar");
    assert_ne!(a, b);
    assert_eq!(a.as_str(), "Foo");
    assert_eq!(b.as_str(), "Bar");
}

#[test]
fn type_hint_id_clones_share_equality() {
    let a = TypeHintId::new("Foo");
    let b = a.clone();
    assert_eq!(a, b);
    // Two independently-built ids with the same name are equal.
    let c = TypeHintId::new(String::from("Foo"));
    assert_eq!(a, c);
}

#[test]
fn type_hint_id_from_impls_compile() {
    let _: TypeHintId = "Foo".into();
    let _: TypeHintId = String::from("Foo").into();
    let _: TypeHintId = Rc::<str>::from("Foo").into();
}

#[test]
fn cardano_and_user_namespaces_are_independent() {
    // A Cardano entry at `(Purpose, 0)` and a user entry at
    // `(TypeHintId("Purpose"), 0)` coexist without aliasing.
    let mut reg = BlueprintHintRegistry::new();
    reg.register_cardano_purpose(0, "Minting");
    reg.register_user(TypeHintId::new("Purpose"), 0, "MyMint");
    assert_eq!(reg.len(), 2);
    assert_eq!(
        reg.resolve_cardano(SumTypeId::Purpose, 0).as_deref(),
        Some("Minting")
    );
    assert_eq!(
        reg.resolve(
            ConstructorShape::unknown_data(0, 0),
            Some(&TypeHintId::new("Purpose"))
        )
        .as_deref(),
        Some("MyMint")
    );
}

#[test]
fn cardano_context_writer_contract_roundtrips_via_user_namespace() {
    // Mirrors the contract of
    // `cardano_context_naming::propagate_types_and_name_constructors`:
    // it seeds names under
    // `TypeHintId::new(sum_type_id.display_name())` and stamps the
    // same hint on each `WhenPattern::Constructor`. The shape such a
    // pattern carries is always `Unknown` — long-form names are not in
    // the closed set.
    let mut reg = BlueprintHintRegistry::new();
    let purpose_hint = TypeHintId::new(SumTypeId::Purpose.display_name());
    for (tag, name) in PURPOSE_V1_V2_NAMES.iter().enumerate() {
        reg.register_user(purpose_hint.clone(), tag, *name);
    }
    for (tag, expected) in PURPOSE_V1_V2_NAMES.iter().enumerate() {
        let shape = ConstructorShape::unknown_data(tag, 1);
        assert_eq!(
            reg.resolve(shape, Some(&purpose_hint)).as_deref(),
            Some(*expected),
            "writer roundtrip for Purpose tag {} should render as {}",
            tag,
            expected,
        );
    }
}

#[test]
fn with_cardano_seed_populates_v1_v2_purpose_namespace() {
    let reg = BlueprintHintRegistry::with_cardano_seed(None);
    assert_eq!(
        reg.resolve_cardano(SumTypeId::Purpose, 0).as_deref(),
        Some("Minting")
    );
    assert_eq!(
        reg.resolve_cardano(SumTypeId::Purpose, 1).as_deref(),
        Some("Spending")
    );
    assert_eq!(
        reg.resolve_cardano(SumTypeId::Purpose, 2).as_deref(),
        Some("Rewarding")
    );
    assert_eq!(
        reg.resolve_cardano(SumTypeId::Purpose, 3).as_deref(),
        Some("Certifying")
    );
    // V1/V2 has no Voting/Proposing — those slots are unregistered.
    assert!(reg.resolve_cardano(SumTypeId::Purpose, 4).is_none());
}

#[test]
fn with_cardano_seed_populates_v3_script_info_namespace() {
    let reg = BlueprintHintRegistry::with_cardano_seed(None);
    assert_eq!(
        reg.resolve_cardano(SumTypeId::ScriptInfo, 0).as_deref(),
        Some("Minting")
    );
    assert_eq!(
        reg.resolve_cardano(SumTypeId::ScriptInfo, 4).as_deref(),
        Some("Voting")
    );
    assert_eq!(
        reg.resolve_cardano(SumTypeId::ScriptInfo, 5).as_deref(),
        Some("Proposing")
    );
}

#[test]
fn with_cardano_seed_total_entry_count() {
    // Cardano ns: 4 V1/V2 Purpose + 6 V3 ScriptInfo = 10.
    // User ns: 5 Data + 2 Option + 3 IntervalBoundType + 2 Credential
    //          + 2 StakeCredential = 14.
    // Version-gated types (Certificate, GovernanceAction, Voter,
    // OutputDatum) are absent at version=None. Total = 24.
    let reg = BlueprintHintRegistry::with_cardano_seed(None);
    assert_eq!(reg.len(), 24);
}

#[test]
fn with_cardano_seed_certificate_is_version_gated() {
    use crate::decompile::ScriptVersion;
    let cert = TypeHintId::new(SumTypeId::Certificate.display_name());
    let tag0 = ConstructorShape::unknown_data(0, 1);

    // V1/V2: DCert names seeded.
    let v2 = BlueprintHintRegistry::with_cardano_seed(Some(ScriptVersion::PlutusV2));
    assert_eq!(
        v2.resolve(tag0, Some(&cert)).as_deref(),
        Some("CredentialRegistration"),
    );

    // None: ambiguous (V1/V2 vs V3 differ under the same key) → NOT seeded.
    let none = BlueprintHintRegistry::with_cardano_seed(None);
    assert_eq!(none.resolve(tag0, Some(&cert)), None);

    // V3: `name_cardano_sum_arms` does not name V3 certs (Never-field arity),
    // so the seed intentionally skips Certificate under V3 too.
    let v3 = BlueprintHintRegistry::with_cardano_seed(Some(ScriptVersion::PlutusV3));
    assert_eq!(v3.resolve(tag0, Some(&cert)), None);
}

#[test]
fn with_cardano_seed_populates_data_variant_namespace() {
    let reg = BlueprintHintRegistry::with_cardano_seed(None);
    let hint = TypeHintId::new(DATA_TYPE_HINT_NAME);
    for (tag, expected) in ["Constr", "Map", "List", "Int", "ByteString"]
        .iter()
        .enumerate()
    {
        let shape = ConstructorShape::unknown_data(tag, 0);
        assert_eq!(
            reg.resolve(shape, Some(&hint)).as_deref(),
            Some(*expected),
            "Data variant tag {} should render as {}",
            tag,
            expected,
        );
    }
}

#[test]
fn with_cardano_seed_populates_option_namespace() {
    let reg = BlueprintHintRegistry::with_cardano_seed(None);
    let hint = TypeHintId::new(OPTION_TYPE_HINT_NAME);
    let some_shape = ConstructorShape::unknown_data(0, 0);
    assert_eq!(
        reg.resolve(some_shape, Some(&hint)).as_deref(),
        Some("Some")
    );
    let none_shape = ConstructorShape::unknown_data(1, 0);
    assert_eq!(
        reg.resolve(none_shape, Some(&hint)).as_deref(),
        Some("None")
    );
}

#[test]
fn empty_registry_resolve_for_known_shape_still_returns_canonical_name() {
    // The shape is the source of truth for built-in constructors,
    // so the canonical name resolves even from an empty registry.
    let reg = BlueprintHintRegistry::new();
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
        let shape = ConstructorShape::known(kc);
        assert_eq!(reg.resolve(shape, None).as_deref(), Some(kc.pretty_name()));
    }
}

#[test]
fn with_cardano_seed_v3_resolves_governance_action_hint() {
    use crate::decompile::ScriptVersion;
    // A `governance_action` hint stamped by `name_cardano_sum_arms` MUST
    // resolve to the ctor name, else the named arm renders as a raw
    // `Constr<tag>`.
    let reg = BlueprintHintRegistry::with_cardano_seed(Some(ScriptVersion::PlutusV3));
    let hint = TypeHintId::new(SumTypeId::GovernanceAction.display_name());
    assert_eq!(
        reg.resolve(ConstructorShape::unknown_data(0, 3), Some(&hint))
            .as_deref(),
        Some("ProtocolParameters"),
        "V3 GovernanceAction tag 0 must resolve to ProtocolParameters"
    );
    // GovernanceAction is V3-only: not seeded under V1/V2/None.
    let reg_v1 = BlueprintHintRegistry::with_cardano_seed(Some(ScriptVersion::PlutusV1));
    assert_eq!(
        reg_v1
            .resolve(ConstructorShape::unknown_data(0, 3), Some(&hint))
            .as_deref(),
        None,
        "GovernanceAction must NOT be seeded under V1"
    );
}
