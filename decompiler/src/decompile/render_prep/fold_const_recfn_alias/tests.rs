use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr};

/// `rec fn <name>(x) { <name> }` — trivial self-referencing body.
fn recfn(name: &str, self_id: VarId) -> PseudoExpr {
    PseudoExpr::RecFn {
        name: Binder::new(name, self_id),
        params: vec![Binder::new("x", VarId::new(9_000))],
        body: PBox::new(PseudoExpr::var_with_id(name, self_id)),
    }
}

/// Re-nest `(name, id, value)` entries into a Let chain over `terminal`.
fn chain(entries: Vec<(&str, VarId, PseudoExpr)>, terminal: PseudoExpr) -> PseudoExpr {
    let mut acc = terminal;
    for (name, id, value) in entries.into_iter().rev() {
        acc = PseudoExpr::Let {
            name: name.to_string(),
            id: Some(id),
            value: PBox::new(value),
            body: PBox::new(acc),
        };
    }
    acc
}

fn first_let_name(expr: &PseudoExpr) -> &str {
    match expr {
        PseudoExpr::Let { name, .. } => name,
        _ => panic!("expected a top-level Let, got {expr:?}"),
    }
}

#[test]
fn folds_synthetic_const_to_inner_recfn_name_and_rewires_calls() {
    // const field_0_64 = rec fn any(x) { any }
    // field_0_64(unit)        <- external call site
    let const_id = VarId::new(7001);
    let self_id = VarId::new(7002);
    let terminal = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("field_0_64", const_id)),
        args: vec![PseudoExpr::Unit].into(),
    };
    let expr = chain(
        vec![("field_0_64", const_id, recfn("any", self_id))],
        terminal,
    );

    let folded = fold_const_recfn_alias(expr);

    // Binder renamed to the inner fn name.
    assert_eq!(first_let_name(&folded), "any");
    // External call site rewired by VarId (name moved, id preserved).
    let PseudoExpr::Let { body, .. } = folded else {
        panic!()
    };
    let PseudoExpr::Apply { function, .. } = body.into_inner() else {
        panic!("expected the terminal Apply");
    };
    let PseudoExpr::Var { name, id } = function.into_inner() else {
        panic!("expected a Var callee");
    };
    assert_eq!(name, "any", "call site must use the new name");
    assert_eq!(id, Some(const_id), "VarId preserved on rewire");
}

#[test]
fn leaves_non_synthetic_const_binder_alone() {
    // const my_helper = rec fn any(x) { any } — user-named, do not fold.
    let const_id = VarId::new(7011);
    let self_id = VarId::new(7012);
    let expr = chain(
        vec![("my_helper", const_id, recfn("any", self_id))],
        PseudoExpr::Unit,
    );

    let folded = fold_const_recfn_alias(expr);
    assert_eq!(first_let_name(&folded), "my_helper");
}

#[test]
fn skips_fold_when_inner_name_collides_with_another_top_level_binding() {
    // const field_0 = rec fn shared(x) { shared }
    // const shared  = unit                          <- name collision
    let f_id = VarId::new(7021);
    let self_id = VarId::new(7022);
    let other_id = VarId::new(7023);
    let expr = chain(
        vec![
            ("field_0", f_id, recfn("shared", self_id)),
            ("shared", other_id, PseudoExpr::Unit),
        ],
        PseudoExpr::Unit,
    );

    let folded = fold_const_recfn_alias(expr);
    // Renaming field_0 -> shared would clash with the second binding; skip.
    assert_eq!(first_let_name(&folded), "field_0");
}

#[test]
fn skips_fold_when_inner_name_is_used_as_a_local_binder() {
    // const field_0 = rec fn any(x) { any }
    // fn(any) { field_0(any) }   <- local lambda param named `any`
    // Renaming field_0 -> any would make `field_0(any)` read `any(any)`,
    // capturing the local param instead of the helper. Must skip.
    let const_id = VarId::new(7041);
    let self_id = VarId::new(7042);
    let local_id = VarId::new(7043);
    let terminal = PseudoExpr::Lambda {
        params: vec![Binder::new("any", local_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("field_0", const_id)),
            args: vec![PseudoExpr::var_with_id("any", local_id)].into(),
        }),
    };
    let expr = chain(vec![("field_0", const_id, recfn("any", self_id))], terminal);

    let folded = fold_const_recfn_alias(expr);
    assert_eq!(
        first_let_name(&folded),
        "field_0",
        "local-binder capture must block the fold"
    );
}

#[test]
fn rewires_reference_inside_a_literal_pattern() {
    // The const is referenced inside a `when` literal pattern — the rewire
    // must reach it (else a stale `field_0_64` survives after the collapse).
    let const_id = VarId::new(7051);
    let self_id = VarId::new(7052);
    let terminal = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Unit),
        subject_name: None,
        clauses: vec![crate::pseudo::ast::WhenClause {
            pattern: crate::pseudo::ast::WhenPattern::Literal(PseudoExpr::var_with_id(
                "field_0_64",
                const_id,
            )),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };
    let expr = chain(
        vec![("field_0_64", const_id, recfn("any", self_id))],
        terminal,
    );

    let folded = fold_const_recfn_alias(expr);
    let PseudoExpr::Let { body, .. } = folded else {
        panic!()
    };
    let PseudoExpr::When { clauses, .. } = body.into_inner() else {
        panic!("expected When terminal")
    };
    let crate::pseudo::ast::WhenPattern::Literal(lit) = &clauses[0].pattern else {
        panic!("expected a literal pattern");
    };
    let PseudoExpr::Var { name, .. } = lit else {
        panic!("expected a Var inside the literal pattern");
    };
    assert_eq!(
        name, "any",
        "reference inside the literal pattern must be rewired"
    );
}

#[test]
fn skips_fold_when_inner_recfn_name_is_not_unique() {
    // Two distinct rec fns both named `dup` — renaming either const to `dup`
    // would be ambiguous, so neither folds.
    let f0 = VarId::new(7031);
    let f1 = VarId::new(7032);
    let s0 = VarId::new(7033);
    let s1 = VarId::new(7034);
    let expr = chain(
        vec![
            ("field_0", f0, recfn("dup", s0)),
            ("field_1", f1, recfn("dup", s1)),
        ],
        PseudoExpr::Unit,
    );

    let folded = fold_const_recfn_alias(expr);
    assert_eq!(first_let_name(&folded), "field_0");
    let PseudoExpr::Let { body, .. } = folded else {
        panic!()
    };
    assert_eq!(first_let_name(&body), "field_1");
}
