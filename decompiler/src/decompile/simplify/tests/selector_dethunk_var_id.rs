use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_tracked_selector_call_requires_matching_var_id() {
    let outer_sel_id = VarId::new(720);
    let inner_sel_id = VarId::new(721);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier.selectors.selector_vars.insert(
        (2, 0),
        super::state::SelectorBinding::new("sel".to_string(), Some(outer_sel_id)),
    );

    let foreign_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("sel", inner_sel_id)),
        args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
    };
    let simplified = simplifier.simplify(foreign_call);

    assert!(
        matches!(
            &simplified,
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, id } if name == "sel" && *id == Some(inner_sel_id))
                    && matches!(args.as_slice(), [PseudoExpr::Int(_), PseudoExpr::Int(_)])
        ),
        "tracked outer selector must not inline a same-name foreign callee, got: {simplified:?}"
    );

    let matching_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("sel", outer_sel_id)),
        args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
    };
    let simplified = simplifier.simplify(matching_call);

    assert!(
        matches!(&simplified, PseudoExpr::Int(n) if n == &1.into()),
        "tracked selector should still inline the matching callee id, got: {simplified:?}"
    );
}

#[test]
fn test_tracked_selector_call_rejects_unresolved_compat_same_name() {
    let selector_id = VarId::new(722);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier.selectors.selector_vars.insert(
        (2, 0),
        super::state::SelectorBinding::new("sel".to_string(), Some(selector_id)),
    );

    let compat_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::compat_var("sel")),
        args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
    };
    let simplified = simplifier.simplify(compat_call);

    assert!(
        matches!(
            &simplified,
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, id } if name == "sel" && id.get().is_none())
                    && matches!(args.as_slice(), [PseudoExpr::Int(_), PseudoExpr::Int(_)])
        ),
        "tracked selector must not inline an unresolved compat same-name callee, got: {simplified:?}"
    );
}

#[test]
fn test_tracked_selector_call_moves_selected_arg_and_respects_arity() {
    let selector_id = VarId::new(724);
    let selected_id = VarId::new(725);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier.selectors.selector_vars.insert(
        (3, 2),
        super::state::SelectorBinding::new("sel".to_string(), Some(selector_id)),
    );

    let matching_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("sel", selector_id)),
        args: vec![
            PseudoExpr::int(1),
            PseudoExpr::int(2),
            PseudoExpr::var_with_id("picked", selected_id),
        ]
        .into(),
    };
    let simplified = simplifier.simplify(matching_call);
    assert!(
        matches!(
            &simplified,
            PseudoExpr::Var { name, id } if name == "picked" && *id == Some(selected_id)
        ),
        "tracked selector should pick the third arg, got: {simplified:?}"
    );

    let mismatched_arity = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("sel", selector_id)),
        args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
    };
    let simplified = simplifier.simplify(mismatched_arity);
    assert!(
        matches!(
            &simplified,
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, id } if name == "sel" && *id == Some(selector_id))
                    && args.len() == 2
        ),
        "tracked selector must not inline a mismatched arity call, got: {simplified:?}"
    );
}

#[test]
fn test_selector_lambda_cse_does_not_emit_idless_selector_var() {
    let err_id = VarId::new(723);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier.selectors.selector_vars.insert(
        (2, 1),
        super::state::SelectorBinding::new("_".to_string(), None),
    );

    let selector_lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("_", VarId::fresh_compat_placeholder()),
            Binder::new("err", err_id),
        ],
        body: PBox::new(PseudoExpr::var_with_id("err", err_id)),
    };
    let simplified = simplifier.simplify(selector_lambda);

    assert!(
        matches!(
            &simplified,
            PseudoExpr::Lambda { params, body }
                if params.len() == 2
                    && matches!(body.as_ref(), PseudoExpr::Var { name, id } if name == "err" && *id == Some(err_id))
        ),
        "idless selector CSE must leave the lambda in place instead of emitting compat `_`, got: {simplified:?}"
    );
}

#[test]
fn test_dethunk_application_requires_matching_var_id() {
    let outer_f_id = VarId::new(730);
    let inner_f_id = VarId::new(731);
    let mut simplifier = Simplifier::with_safe_mode(false);
    let mut dethunk_indices = std::collections::HashSet::new();
    dethunk_indices.insert(0);
    simplifier
        .dethunk
        .dethunk_params
        .insert(outer_f_id, dethunk_indices);

    let delayed_payload = || PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("g")),
        args: vec![PseudoExpr::int(1)].into(),
    };
    let foreign_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("f", inner_f_id)),
        args: vec![PseudoExpr::Delay(PBox::new(delayed_payload()))].into(),
    };
    let simplified = simplifier.simplify(foreign_call);

    assert!(
        matches!(
            &simplified,
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, id } if name == "f" && *id == Some(inner_f_id))
                    && matches!(args.as_slice(), [PseudoExpr::Delay(_)])
        ),
        "dethunk fact for outer f must not strip delay from same-name foreign callee, got: {simplified:?}"
    );

    let matching_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("f", outer_f_id)),
        args: vec![PseudoExpr::Delay(PBox::new(delayed_payload()))].into(),
    };
    let simplified = simplifier.simplify(matching_call);

    assert!(
        matches!(
            &simplified,
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, id } if name == "f" && *id == Some(outer_f_id))
                    && matches!(args.as_slice(), [PseudoExpr::Apply { .. }])
        ),
        "dethunk fact should still strip delay for matching callee id, got: {simplified:?}"
    );
}
