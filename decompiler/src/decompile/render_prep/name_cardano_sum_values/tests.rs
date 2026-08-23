use super::*;
use crate::decompile::render_prep::RenderCtx;
use crate::decompile::simplify::postprocess::CardanoTypeRef;
use crate::pseudo::ast::BinaryOp;
use crate::pseudo::var_id::VarId;

/// `Constr<tag>(#"00")` with no resolved shape.
fn stub_ctor(tag: usize) -> PseudoExpr {
    PseudoExpr::Constr {
        type_hint: None,
        tag,
        fields: vec![PseudoExpr::byte_array(vec![0x00])].into(),
        shape: ConstructorShape::unknown_data(tag, 1),
    }
}

fn env_with(vid: u32, ty: CardanoTypeRef) -> CardanoTypeEnv {
    let mut env = CardanoTypeEnv::default();
    env.debug_insert(VarId::new(vid), ty);
    env
}

fn eq(left: PseudoExpr, right: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(left),
        right: PBox::new(right),
    }
}

fn hint_of(expr: &PseudoExpr) -> Option<String> {
    match expr {
        PseudoExpr::BinOp { right, .. } => match right.as_ref() {
            PseudoExpr::Constr { type_hint, .. } => {
                type_hint.as_ref().map(|h| h.as_str().to_string())
            }
            _ => None,
        },
        _ => None,
    }
}

#[test]
fn types_the_constructor_from_the_other_side_of_the_comparison() {
    let env = env_with(7, CardanoTypeRef::Sum(SumTypeId::Credential));
    let expr = eq(
        PseudoExpr::var_with_id("value", VarId::new(7)),
        stub_ctor(0),
    );
    let out = name_cardano_sum_values(expr, &env, &RenderCtx::at(None));
    assert_eq!(hint_of(&out).as_deref(), Some("credential"));
}

#[test]
fn refuses_a_tag_the_sum_does_not_have() {
    // `Credential` has tags 0 and 1 only; nothing types tag 4.
    let env = env_with(7, CardanoTypeRef::Sum(SumTypeId::Credential));
    let expr = eq(
        PseudoExpr::var_with_id("value", VarId::new(7)),
        stub_ctor(4),
    );
    let out = name_cardano_sum_values(expr, &env, &RenderCtx::at(None));
    assert_eq!(hint_of(&out), None);
}

#[test]
fn refuses_when_neither_side_is_typed() {
    let env = CardanoTypeEnv::default();
    let expr = eq(
        PseudoExpr::var_with_id("value", VarId::new(7)),
        stub_ctor(0),
    );
    let out = name_cardano_sum_values(expr.clone(), &env, &RenderCtx::at(None));
    assert_eq!(out, expr);
}

#[test]
fn leaves_a_real_user_hint_alone() {
    let env = env_with(7, CardanoTypeRef::Sum(SumTypeId::Credential));
    let mut ctor = stub_ctor(0);
    if let PseudoExpr::Constr { type_hint, .. } = &mut ctor {
        *type_hint = Some(crate::decompile::TypeHintId::new("MyWallet"));
    }
    let out = name_cardano_sum_values(
        eq(PseudoExpr::var_with_id("v", VarId::new(7)), ctor),
        &env,
        &RenderCtx::at(None),
    );
    assert_eq!(hint_of(&out).as_deref(), Some("MyWallet"));
}

#[test]
fn only_equality_carries_the_type() {
    let env = env_with(7, CardanoTypeRef::Sum(SumTypeId::Credential));
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Lt,
        left: PBox::new(PseudoExpr::var_with_id("value", VarId::new(7))),
        right: PBox::new(stub_ctor(0)),
    };
    let out = name_cardano_sum_values(expr.clone(), &env, &RenderCtx::at(None));
    assert_eq!(out, expr);
}

#[test]
fn credential_needs_a_bytearray_witness() {
    // `Credential` shares its `{(0,1),(1,1)}` shape with every other
    // two-variant one-field stub, so tag and arity are not enough: an
    // Int payload is some other type wearing the same shape.
    let env = env_with(7, CardanoTypeRef::Sum(SumTypeId::Credential));
    let int_payload = PseudoExpr::Constr {
        type_hint: None,
        tag: 0,
        fields: vec![PseudoExpr::Int(42.into())].into(),
        shape: ConstructorShape::unknown_data(0, 1),
    };
    let out = name_cardano_sum_values(
        eq(PseudoExpr::var_with_id("value", VarId::new(7)), int_payload),
        &env,
        &RenderCtx::at(None),
    );
    assert_eq!(hint_of(&out), None);
}

#[test]
fn credential_accepts_a_b_data_wrapped_payload() {
    let env = env_with(7, CardanoTypeRef::Sum(SumTypeId::Credential));
    let wrapped = PseudoExpr::Constr {
        type_hint: None,
        tag: 1,
        fields: vec![PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::DataByteArray,
            args: vec![PseudoExpr::var("bytes")].into(),
        }]
        .into(),
        shape: ConstructorShape::unknown_data(1, 1),
    };
    let out = name_cardano_sum_values(
        eq(PseudoExpr::var_with_id("value", VarId::new(7)), wrapped),
        &env,
        &RenderCtx::at(None),
    );
    assert_eq!(hint_of(&out).as_deref(), Some("credential"));
}
