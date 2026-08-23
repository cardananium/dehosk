use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::var_id::VarId;

#[test]
fn renames_bare_compat_fix_var() {
    // Var("fix") with id=None — the sentinel from `compat_var("fix")`
    let expr = PseudoExpr::Var {
        name: "fix".to_string(),
        id: None,
    };
    let renamed = flag_orphan_fix(expr);
    assert!(matches!(renamed, PseudoExpr::Var { ref name, id: None } if name == RESIDUE_NAME));
}

#[test]
fn leaves_bound_fix_alone() {
    // let fix = 42 in fix — bound fix is a real local binder
    let fix_id = VarId::fresh_binding();
    let expr = PseudoExpr::let_bind_with_id(
        "fix",
        fix_id,
        PseudoExpr::int(42),
        PseudoExpr::var_with_id("fix", fix_id),
    );
    let renamed = flag_orphan_fix(expr);
    let PseudoExpr::Let { body, .. } = renamed else {
        panic!("expected Let")
    };
    assert!(matches!(*body, PseudoExpr::Var { ref name, .. } if name == "fix"));
}

#[test]
fn renames_orphan_fix_inside_when_subject() {
    // when fix is { _ -> 0 } — the orphan shape: the When subject is
    // the bare Var("fix") sentinel.
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "fix".to_string(),
            id: None,
        }),
        subject_name: None,
        clauses: vec![crate::pseudo::ast::WhenClause::new(
            crate::pseudo::ast::WhenPattern::wildcard(),
            PseudoExpr::int(0),
        )],
    };
    let renamed = flag_orphan_fix(expr);
    let PseudoExpr::When { subject, .. } = renamed else {
        panic!("expected When")
    };
    assert!(matches!(*subject, PseudoExpr::Var { ref name, .. } if name == RESIDUE_NAME));
}
