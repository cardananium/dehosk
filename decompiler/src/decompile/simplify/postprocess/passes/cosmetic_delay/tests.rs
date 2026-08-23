use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::ast::PBox;
use crate::pseudo::var_id::VarId;

#[test]
fn strips_cosmetic_delay_on_lambda_let_and_keeps_it_on_literals() {
    let lam_id = VarId::fresh_binding();
    let let_id = VarId::fresh_binding();

    let stripped_lambda = strip_cosmetic_delays(PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
        params: vec![Binder::new("x", lam_id)],
        body: PBox::new(PseudoExpr::int(1)),
    })));
    assert!(
        matches!(stripped_lambda, PseudoExpr::Lambda { .. }),
        "Delay(Lambda) should drop the wrapper, got: {stripped_lambda:?}"
    );

    let stripped_let = strip_cosmetic_delays(PseudoExpr::Delay(PBox::new(PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(let_id),
        value: PBox::new(PseudoExpr::int(2)),
        body: PBox::new(PseudoExpr::var_with_id("y", let_id)),
    })));
    assert!(
        matches!(stripped_let, PseudoExpr::Let { .. }),
        "Delay(Let) should drop the wrapper, got: {stripped_let:?}"
    );

    let kept_int = strip_cosmetic_delays(PseudoExpr::Delay(PBox::new(PseudoExpr::int(3))));
    assert!(
        matches!(kept_int, PseudoExpr::Delay(_)),
        "Delay(Int) should keep the wrapper, got: {kept_int:?}"
    );

    let kept_bool = strip_cosmetic_delays(PseudoExpr::Delay(PBox::new(PseudoExpr::Bool(true))));
    assert!(
        matches!(kept_bool, PseudoExpr::Delay(_)),
        "Delay(Bool) should keep the wrapper, got: {kept_bool:?}"
    );

    let bare = PseudoExpr::int(4);
    assert_eq!(strip_cosmetic_delays(bare.clone()), bare);
}
