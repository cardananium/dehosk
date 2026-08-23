use super::*;

#[test]
fn downgrades_true_false_to_unknown() {
    let t = PseudoExpr::Constr {
        type_hint: None,
        tag: 1,
        fields: vec![].into(),
        shape: ConstructorShape::Known(KnownConstructor::True),
    };
    let out = downgrade_prelude_constructors(t);
    match out {
        PseudoExpr::Constr { shape, .. } => assert_eq!(shape, ConstructorShape::unknown_data(1, 0)),
        other => panic!("expected Constr, got {other:?}"),
    }
}

#[test]
fn preserves_purpose_known_constructors() {
    // Spend/Mint/etc. stay Known — needed by purpose-dispatch
    // detection.
    let spend = PseudoExpr::Constr {
        type_hint: None,
        tag: 1,
        fields: vec![PseudoExpr::Unit].into(),
        shape: ConstructorShape::Known(KnownConstructor::Spend),
    };
    let out = downgrade_prelude_constructors(spend);
    match out {
        PseudoExpr::Constr { shape, .. } => assert!(matches!(
            shape,
            ConstructorShape::Known(KnownConstructor::Spend)
        )),
        other => panic!("expected Constr, got {other:?}"),
    }
}

#[test]
fn downgrades_some_none_void() {
    for known in [
        KnownConstructor::Some,
        KnownConstructor::None,
        KnownConstructor::Void,
    ] {
        let arity = known.expected_arity();
        let fields = (0..arity).map(|_| PseudoExpr::Unit).collect();
        let c = PseudoExpr::Constr {
            type_hint: None,
            tag: known.expected_tag(),
            fields,
            shape: ConstructorShape::Known(known),
        };
        let out = downgrade_prelude_constructors(c);
        match out {
            PseudoExpr::Constr { shape, .. } => assert!(
                matches!(shape, ConstructorShape::Unknown { .. }),
                "expected Unknown for {known:?}, got {shape:?}"
            ),
            other => panic!("expected Constr, got {other:?}"),
        }
    }
}
