use super::extract_heavy_constants;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, PseudoExpr};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::OptionVarIdGet;

#[test]
fn test_extract_heavy_constants_wraps_large_static_eq_operand() {
    let heavy = PseudoExpr::constr(
        ConstructorShape::unknown_data(0, 2),
        vec![
            PseudoExpr::ByteArray(vec![0xaa; 32]),
            PseudoExpr::constr(
                ConstructorShape::unknown_data(0, 1),
                vec![PseudoExpr::ByteArray(vec![0xbb; 32])],
            ),
        ],
    );

    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(PseudoExpr::var("x")),
        right: PBox::new(heavy.clone()),
    };

    let result = extract_heavy_constants(expr);

    match result {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
            ..
        } => {
            let binding_id = id
                .get()
                .expect("expected heavy-constant extraction binding to carry a VarId");
            assert!(name.starts_with("data_const_"));
            assert!(value.as_ref().structural_eq(&heavy));
            match body.as_ref() {
                PseudoExpr::BinOp { right, .. } => {
                    assert!(matches!(
                        right.as_ref(),
                        PseudoExpr::Var { name: var_name, id: var_id, .. }
                            if var_name == &name && var_id.get() == Some(binding_id)
                    ));
                }
                _ => panic!("expected rebuilt binop after extraction"),
            }
        }
        _ => panic!("expected heavy constant extraction to introduce a let binding"),
    }
}

#[test]
fn test_extract_heavy_constants_uses_fresh_name_when_default_is_bound() {
    let existing_id = crate::pseudo::var_id::VarId::new(7011);
    let heavy = PseudoExpr::constr(
        ConstructorShape::unknown_data(0, 2),
        vec![
            PseudoExpr::ByteArray(vec![0xaa; 32]),
            PseudoExpr::ByteArray(vec![0xbb; 32]),
        ],
    );
    let expr = PseudoExpr::Let {
        name: "data_const_0".to_string(),
        id: Some(existing_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::var_with_id("data_const_0", existing_id)),
            right: PBox::new(heavy),
        }),
    };

    let result = extract_heavy_constants(expr);

    match result {
        PseudoExpr::Let { body, .. } => match body.as_ref() {
            PseudoExpr::Let { name, body, .. } => {
                assert_eq!(name, "data_const_1");
                assert!(
                    matches!(
                        body.as_ref(),
                        PseudoExpr::BinOp { right, .. }
                            if matches!(
                                right.as_ref(),
                                PseudoExpr::Var { name, .. } if name == "data_const_1"
                            )
                    ),
                    "expected extracted heavy constant to use the fresh binder name, got: {body:?}"
                );
            }
            other => {
                panic!("expected fresh heavy-constant let under existing let, got: {other:?}")
            }
        },
        other => panic!("expected existing let to remain outermost, got: {other:?}"),
    }
}
