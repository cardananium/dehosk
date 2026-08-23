use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn converts_expect_tag_eq_to_constr_when() {
    let x_id = crate::pseudo::var_id::VarId::fresh_binding();
    let body_id = crate::pseudo::var_id::VarId::fresh_binding();
    let input = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id("x", x_id),
                    "tag",
                )),
                right: PBox::new(PseudoExpr::int(0)),
            },
            PseudoExpr::var_with_id("body", body_id),
        ]
        .into(),
    };
    let out = convert_expect_tag_to_constr_when(input);
    assert!(
        matches!(out, PseudoExpr::When { .. }),
        "expect!(x.tag == 0, body) should become when, got: {out:?}"
    );
}

#[test]
fn identity_when_no_expect_marker() {
    let n = PseudoExpr::int(42);
    assert_eq!(convert_expect_tag_to_constr_when(n.clone()), n);

    let foo_id = crate::pseudo::var_id::VarId::fresh_binding();
    let call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("foo", foo_id)),
        args: vec![PseudoExpr::int(1)].into(),
    };
    assert_eq!(convert_expect_tag_to_constr_when(call.clone()), call);
}
