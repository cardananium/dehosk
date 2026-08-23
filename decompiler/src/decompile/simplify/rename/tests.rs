use super::Simplifier;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

#[test]
fn test_strip_thunked_self_calls_preserves_self_var_id() {
    let self_id = VarId::new(900);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("loop", self_id)),
        args: vec![].into(),
    };

    let result = Simplifier::strip_thunked_self_calls(&expr, "loop");

    assert!(
        matches!(
            result,
            PseudoExpr::Var { ref name, ref id, .. }
                if name == "loop" && id.get() == Some(self_id)
        ),
        "expected thunk-strip rewrite to preserve self VarId, got: {result:?}"
    );
}

#[test]
fn test_strip_rec_self_arg_removes_y_comb_seed_arg() {
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("acc")),
        args: vec![PseudoExpr::var("__y_comb_rec_fn"), PseudoExpr::var("xs")].into(),
    };

    let result = Simplifier::strip_rec_self_arg(&expr, "acc");

    assert!(
        matches!(
            &result,
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "acc")
                    && matches!(args.as_slice(), [PseudoExpr::Var { name, .. }] if name == "xs")
        ),
        "expected y-comb seed arg to be stripped from recursive entry call, got: {result:?}"
    );
}

#[test]
fn test_strip_rec_self_arg_respects_let_shadowing() {
    let shadow_id = VarId::new(321);
    let expr = PseudoExpr::Let {
        name: "acc".to_string(),
        id: Some(shadow_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("acc")),
            args: vec![PseudoExpr::var("__y_comb_rec_fn"), PseudoExpr::var("xs")].into(),
        }),
    };

    let result = Simplifier::strip_rec_self_arg(&expr, "acc");

    assert_eq!(result, expr);
}

#[test]
fn test_strip_thunked_self_calls_respects_lambda_shadowing() {
    let expr = PseudoExpr::Lambda {
        params: vec!["loop".to_string().into()],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("loop")),
            args: vec![].into(),
        }),
    };

    let result = Simplifier::strip_thunked_self_calls(&expr, "loop");

    assert_eq!(result, expr);
}

#[test]
fn test_rename_var_binding_uses_var_id_authoritatively() {
    let target_id = VarId::new(111);
    let other_id = VarId::new(222);
    let expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::var_with_id("x", target_id),
            PseudoExpr::var_with_id("x", other_id),
        ]
        .into(),
    );

    let result = Simplifier::rename_var_binding(&expr, "x", Some(target_id), "y");

    assert!(
        matches!(
            &result,
            PseudoExpr::Tuple(items)
                if matches!(&items[0], PseudoExpr::Var { name, id, .. } if name == "y" && id.get() == Some(target_id))
                    && matches!(&items[1], PseudoExpr::Var { name, id, .. } if name == "x" && id.get() == Some(other_id))
        ),
        "expected only the target VarId to be renamed, got: {result:?}"
    );
}

#[test]
fn test_substitute_var_for_var_updates_var_id() {
    let old_id = VarId::new(311);
    let other_id = VarId::new(312);
    let new_id = VarId::new(313);
    let expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::var_with_id("x", old_id),
            PseudoExpr::var_with_id("x", other_id),
        ]
        .into(),
    );

    let result = Simplifier::substitute_var_for_var(&expr, "x", Some(old_id), "y", new_id);

    assert!(
        matches!(
            &result,
            PseudoExpr::Tuple(items)
                if matches!(&items[0], PseudoExpr::Var { name, id, .. } if name == "y" && id.get() == Some(new_id))
                    && matches!(&items[1], PseudoExpr::Var { name, id, .. } if name == "x" && id.get() == Some(other_id))
        ),
        "expected substitution to update only the target VarId, got: {result:?}"
    );
}

#[test]
fn test_substitute_var_for_var_does_not_capture_under_let_new_name() {
    let old_id = VarId::new(321);
    let new_id = VarId::new(322);
    let inner_y_id = VarId::new(323);
    let expr = PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(inner_y_id),
        value: PBox::new(PseudoExpr::var_with_id("x", old_id)),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("x", old_id),
                PseudoExpr::var_with_id("y", inner_y_id),
            ]
            .into(),
        )),
    };

    let result = Simplifier::substitute_var_for_var(&expr, "x", Some(old_id), "y", new_id);

    assert!(
        matches!(
            &result,
            PseudoExpr::Let { value, body, .. }
                if matches!(value.as_ref(), PseudoExpr::Var { name, id, .. } if name == "y" && id.get() == Some(new_id))
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Tuple(items)
                            if matches!(&items[0], PseudoExpr::Var { name, id, .. } if name == "x" && id.get() == Some(old_id))
                                && matches!(&items[1], PseudoExpr::Var { name, id, .. } if name == "y" && id.get() == Some(inner_y_id))
                    )
        ),
        "expected substitution to rewrite let value but not body under inner y, got: {result:?}"
    );
}

#[test]
fn test_substitute_var_for_var_does_not_capture_under_lambda_new_name() {
    let old_id = VarId::new(331);
    let new_id = VarId::new(332);
    let inner_y_id = VarId::new(333);
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("y", inner_y_id)],
        body: PBox::new(PseudoExpr::var_with_id("x", old_id)),
    };

    let result = Simplifier::substitute_var_for_var(&expr, "x", Some(old_id), "y", new_id);

    assert!(
        matches!(
            &result,
            PseudoExpr::Lambda { body, .. }
                if matches!(body.as_ref(), PseudoExpr::Var { name, id, .. } if name == "x" && id.get() == Some(old_id))
        ),
        "expected substitution to stop under lambda y, got: {result:?}"
    );
}

#[test]
fn test_substitute_var_for_var_does_not_capture_under_when_subject_new_name() {
    let old_id = VarId::new(341);
    let new_id = VarId::new(342);
    let subject_y_id = VarId::new(343);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("x", old_id)),
        subject_name: Some(Binder::new("y", subject_y_id)),
        clauses: vec![WhenClause {
            pattern: WhenPattern::Literal(PseudoExpr::var_with_id("x", old_id)),
            guard: Some(PseudoExpr::var_with_id("x", old_id)),
            body: PseudoExpr::var_with_id("x", old_id),
        }],
    };

    let result = Simplifier::substitute_var_for_var(&expr, "x", Some(old_id), "y", new_id);

    assert!(
        matches!(
            &result,
            PseudoExpr::When { subject, clauses, .. }
                if matches!(subject.as_ref(), PseudoExpr::Var { name, id, .. } if name == "y" && id.get() == Some(new_id))
                    && matches!(&clauses[0].pattern, WhenPattern::Literal(PseudoExpr::Var { name, id, .. }) if name == "y" && id.get() == Some(new_id))
                    && matches!(clauses[0].guard.as_ref(), Some(PseudoExpr::Var { name, id, .. }) if name == "x" && id.get() == Some(old_id))
                    && matches!(&clauses[0].body, PseudoExpr::Var { name, id, .. } if name == "x" && id.get() == Some(old_id))
        ),
        "expected subject/pattern substitution but no guard/body capture under subject y, got: {result:?}"
    );
}

#[test]
fn test_rename_var_binding_respects_when_subject_shadowing_but_renames_pattern_literals() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("arg")),
        subject_name: Some("x".to_string().into()),
        clauses: vec![WhenClause {
            pattern: WhenPattern::Literal(PseudoExpr::var("x")),
            guard: Some(PseudoExpr::var("x")),
            body: PseudoExpr::var("x"),
        }],
    };

    let result = Simplifier::rename_var_binding(&expr, "x", None, "y");

    assert!(
        matches!(
            &result,
            PseudoExpr::When { clauses, .. }
                if clauses.len() == 1
                    && matches!(&clauses[0].pattern, WhenPattern::Literal(PseudoExpr::Var { name, .. }) if name == "y")
                    && matches!(clauses[0].guard.as_ref(), Some(PseudoExpr::Var { name, .. }) if name == "x")
                    && matches!(&clauses[0].body, PseudoExpr::Var { name, .. } if name == "x")
        ),
        "expected subject shadowing to block guard/body but not literal-pattern renaming, got: {result:?}"
    );
}
