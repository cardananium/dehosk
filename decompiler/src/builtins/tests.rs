use super::*;

#[test]
fn if_builtin_uses_pretty_keyword_safe_name() {
    assert_eq!(
        BuiltinId::IfThenElse.display_name(BuiltinDisplayStyle::Canonical),
        "if"
    );
    assert_eq!(
        BuiltinId::IfThenElse.display_name(BuiltinDisplayStyle::Pretty),
        "if_then_else"
    );
    // The raw list spine renders as the `builtin` surface.
    assert_eq!(
        BuiltinId::ListTail.display_name(BuiltinDisplayStyle::Pretty),
        "builtin.tail_list"
    );
}

#[test]
fn list_spine_and_constr_unpack_render_with_builtin_surface() {
    // `Constr.unpack` / `List.head` / `List.tail` / `List.is_empty` are
    // internal pseudonyms; the surface is the `builtin` form,
    // while the canonical name keeps the pseudonym for `from_name`.
    let mappings: &[(BuiltinId, &str, &str)] = &[
        (
            BuiltinId::ConstrUnpack,
            "Constr.unpack",
            "builtin.un_constr_data",
        ),
        (BuiltinId::ListHead, "List.head", "builtin.head_list"),
        (BuiltinId::ListTail, "List.tail", "builtin.tail_list"),
        (BuiltinId::ListIsEmpty, "List.is_empty", "builtin.null_list"),
    ];
    for (id, canonical, pretty) in mappings {
        assert_eq!(
            id.display_name(BuiltinDisplayStyle::Canonical),
            *canonical,
            "{id:?} canonical name regressed",
        );
        assert_eq!(
            id.display_name(BuiltinDisplayStyle::Pretty),
            *pretty,
            "{id:?} pretty name should render as the builtin.* surface",
        );
    }
}

#[test]
fn data_pseudonym_builtins_render_with_builtin_surface() {
    // `Data.un_bytearray` / `Data.Int(...)` / `Data.serialize` are
    // pseudonyms, not surface syntax — `Data` is a type, not a module.
    // The pretty form must be the real `builtin` surface.
    let mappings: &[(BuiltinId, &str, &str)] = &[
        (
            BuiltinId::DataUnByteArray,
            "Data.un_bytearray",
            "builtin.un_b_data",
        ),
        (BuiltinId::DataUnInt, "Data.un_int", "builtin.un_i_data"),
        (
            BuiltinId::DataUnList,
            "Data.un_list",
            "builtin.un_list_data",
        ),
        (BuiltinId::DataUnMap, "Data.un_map", "builtin.un_map_data"),
        (
            BuiltinId::DataUnConstr,
            "Data.un_constr",
            "builtin.un_constr_data",
        ),
        (BuiltinId::DataByteArray, "Data.ByteArray", "builtin.b_data"),
        (BuiltinId::DataInt, "Data.Int", "builtin.i_data"),
        (BuiltinId::DataList, "Data.List", "builtin.list_data"),
        (BuiltinId::DataMap, "Data.Map", "builtin.map_data"),
        (BuiltinId::DataConstr, "Data.Constr", "builtin.constr_data"),
        (
            BuiltinId::DataSerialize,
            "Data.serialize",
            "builtin.serialise_data",
        ),
        (BuiltinId::DataEq, "Data.eq", "builtin.equals_data"),
        (BuiltinId::DataCase, "Data.case", "builtin.choose_data"),
    ];
    for (id, canonical, pretty) in mappings {
        assert_eq!(
            id.display_name(BuiltinDisplayStyle::Canonical),
            *canonical,
            "{id:?} canonical name regressed"
        );
        assert_eq!(
            id.display_name(BuiltinDisplayStyle::Pretty),
            *pretty,
            "{id:?} pretty name should render as the builtin.* surface",
        );
    }
}

#[test]
fn returns_bool_and_monomorphic_return_type_agree() {
    // Invariant: every variant `returns_bool()` declares must produce
    // `Some(PseudoType::Bool)` from `monomorphic_return_type()`, or the
    // solver's `is_inherently_bool` and return-type inference disagree.
    let bool_variants: &[BuiltinId] = &[
        BuiltinId::ListIsEmpty,
        BuiltinId::IntEq,
        BuiltinId::IntLt,
        BuiltinId::IntLte,
        BuiltinId::ByteArrayEq,
        BuiltinId::ByteArrayLt,
        BuiltinId::ByteArrayLte,
        BuiltinId::StringEq,
        BuiltinId::DataEq,
        BuiltinId::Seq,
    ];
    for variant in bool_variants {
        assert!(
            variant.returns_bool(),
            "{variant:?} listed as bool-returning here but returns_bool() said false"
        );
        assert_eq!(
            variant.monomorphic_return_type(),
            Some(PseudoType::Bool),
            "{variant:?}.monomorphic_return_type() diverged from returns_bool()"
        );
    }
}

#[test]
fn polymorphic_builtins_have_no_monomorphic_return_type() {
    // These return types depend on argument types and must be resolved
    // by the caller, not the BuiltinId knowledge table.
    let polymorphic: &[BuiltinId] = &[
        BuiltinId::ListHead,
        BuiltinId::ListTail,
        BuiltinId::ListPrepend,
        BuiltinId::ListCons,
        BuiltinId::PairFirst,
        BuiltinId::PairSecond,
        BuiltinId::PairNew,
        BuiltinId::IfThenElse,
        BuiltinId::DataCase,
        BuiltinId::Trace,
        BuiltinId::Error,
    ];
    for variant in polymorphic {
        assert!(
            variant.monomorphic_return_type().is_none(),
            "{variant:?} should be polymorphic but returned a fixed type"
        );
    }
}

#[test]
fn empty_list_constructors_return_list_of_unknown() {
    // These always build an empty list; the element type is unresolved,
    // so `List(Unknown)` is the canonical monomorphic answer.
    let ctors: &[BuiltinId] = &[
        BuiltinId::ListEmpty,
        BuiltinId::ListEmptyPairs,
        BuiltinId::MkNilData,
        BuiltinId::MkNilPairData,
        BuiltinId::NewList,
        BuiltinId::NewPairs,
    ];
    for variant in ctors {
        match variant.monomorphic_return_type() {
            Some(PseudoType::List(inner)) => assert!(
                matches!(inner.as_ref(), PseudoType::Unknown),
                "{variant:?} must return List(Unknown), got List({inner:?})"
            ),
            other => panic!("{variant:?} must return List(Unknown), got {other:?}"),
        }
    }
}

#[test]
fn read_bit_returns_bool_not_int() {
    assert_eq!(
        BuiltinId::ByteArrayReadBit.monomorphic_return_type(),
        Some(PseudoType::Bool)
    );
}

#[test]
fn monomorphic_return_type_covers_canonical_monomorphic_builtins() {
    // Spot-checks for each return-type family so the big match in
    // monomorphic_return_type doesn't silently regress a variant.
    assert_eq!(
        BuiltinId::IntAdd.monomorphic_return_type(),
        Some(PseudoType::Int)
    );
    assert_eq!(
        BuiltinId::ByteArrayConcat.monomorphic_return_type(),
        Some(PseudoType::ByteArray)
    );
    assert_eq!(
        BuiltinId::StringConcat.monomorphic_return_type(),
        Some(PseudoType::String)
    );
    assert_eq!(
        BuiltinId::DataConstr.monomorphic_return_type(),
        Some(PseudoType::Data)
    );
    assert_eq!(
        BuiltinId::DataInt.monomorphic_return_type(),
        Some(PseudoType::Data)
    );
}
