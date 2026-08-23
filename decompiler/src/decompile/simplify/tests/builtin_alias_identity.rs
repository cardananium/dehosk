use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_idless_builtin_alias_resolves_via_synthetic_binding_id() {
    let expr = PseudoExpr::Let {
        name: "picker".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("List.tail"),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Var {
                name: "picker".to_string(),
                id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            }),
            args: vec![PseudoExpr::var("xs")].into(),
        }),
    };

    let simplified = simplify(expr);
    let pretty = simplified.to_pretty();

    assert!(
        !pretty.contains("picker("),
        "id-less builtin alias should resolve through a synthetic VarId instead of surviving as a bare local call: {pretty}"
    );
    assert!(
        // DEFAULT render (compilable-data-access OFF): `ListTail` applied to
        // one arg renders as `xs[1..]`, not `builtin.tail_list(xs)`.
        pretty == "xs[1..]" || pretty.contains("[1..]") || pretty.contains("tail_list"),
        "id-less builtin alias should still simplify as the builtin operation instead of remaining a local alias: {pretty}"
    );
}

#[test]
fn test_plain_bool_if_stays_if_without_constructor_evidence() {
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Var {
            name: "flag".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        }),
        then_branch: PBox::new(PseudoExpr::Int(1.into())),
        else_branch: PBox::new(PseudoExpr::Int(0.into())),
    };

    let simplified = simplify(expr);

    assert!(
        matches!(simplified, PseudoExpr::If { .. }),
        "plain Bool conditions should remain if-expressions when there is no constructor evidence: {simplified:?}"
    );
}

#[test]
fn test_idless_builtin_alias_does_not_leak_through_lambda_shadowing() {
    let expr = PseudoExpr::Let {
        name: "picker".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("List.tail"),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec!["picker".to_string().into()],
            body: PBox::new(PseudoExpr::var("picker")),
        }),
    };

    let simplified = simplify(expr);

    match simplified {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params, vec!["picker".to_string()]);
            assert!(
                matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "picker"),
                "inner lambda parameter should shadow the outer id-less builtin alias, got: {body:?}"
            );
        }
        other => panic!("expected outer alias let to simplify to a lambda, got: {other:?}"),
    }
}

#[test]
fn test_builtin_id_centralizes_force_and_projection_aliases() {
    assert_eq!(BuiltinId::from_name("tail_list"), Some(BuiltinId::ListTail));
    assert_eq!(BuiltinId::from_name("List.tail"), Some(BuiltinId::ListTail));
    assert!(BuiltinId::ListTail.is_projection_wrapper());
    assert!(BuiltinId::ListTail.starts_projection_chain());
    assert!(Simplifier::is_force1_builtin("List.tail"));
    assert!(Simplifier::is_force2_builtin("Data.case"));
}

#[test]
fn test_builtin_id_knows_internal_canonical_surface() {
    assert_eq!(
        BuiltinId::from_name("Constr.unpack"),
        Some(BuiltinId::ConstrUnpack)
    );
    assert_eq!(BuiltinId::from_name("List.cons"), Some(BuiltinId::ListCons));
    assert_eq!(
        BuiltinId::from_name("Data.to_bytes"),
        Some(BuiltinId::DataToBytes)
    );
    assert_eq!(
        BuiltinId::from_name("Data.constr_index"),
        Some(BuiltinId::DataConstrIndex)
    );
    assert!(BuiltinId::is_known_name("verify_ecdsa_secp256k1"));
}

#[test]
fn test_builtin_name_preserves_unmapped_force_only_builtins() {
    assert_eq!(Simplifier::nice_builtin_name("mk_nil_data"), "mk_nil_data");
    assert_eq!(Simplifier::nice_builtin_name("new_pairs"), "new_pairs");
}
