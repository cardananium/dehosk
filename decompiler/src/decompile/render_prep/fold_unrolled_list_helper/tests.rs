use super::*;
use crate::pseudo::ast::PBox;

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}
fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name, VarId::new(id))
}
fn nil() -> PseudoExpr {
    PseudoExpr::List {
        elements: vec![].into(),
        tail: None,
    }
}
fn cons(head: PseudoExpr, tail: PseudoExpr) -> PseudoExpr {
    PseudoExpr::List {
        elements: vec![head].into(),
        tail: Some(PBox::new(tail)),
    }
}
fn copy_when(subject: PseudoExpr, h: u32, t: u32, tail: impl FnOnce(u32) -> PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::List { elements: vec![], tail: None },
                guard: None,
                body: nil(),
            },
            WhenClause {
                pattern: WhenPattern::List {
                    elements: vec![binder("h", h)],
                    tail: Some(binder("t", t)),
                },
                guard: None,
                body: cons(var("h", h), tail(t)),
            },
        ],
    }
}

#[test]
fn plain_copy_collapses_to_subject() {
    let out = fold_unrolled_list_helper(copy_when(var("xs", 1), 5, 6, |t| var("t", t)));
    assert_eq!(out, var("xs", 1));
}

#[test]
fn helper_calls_collapse_and_wrap_levels() {
    let helper = PseudoExpr::RecFn {
        name: binder("copy", 10),
        params: vec![binder("v", 11)],
        body: PBox::new(copy_when(var("v", 11), 12, 13, |t| PseudoExpr::Apply {
            function: PBox::new(var("copy", 10)),
            args: vec![var("t", t)].into(),
        })),
    };
    let call = |arg| PseudoExpr::Apply {
        function: PBox::new(var("copy", 10)),
        args: vec![arg].into(),
    };
    let level = copy_when(var("xs", 1), 5, 6, |t| call(var("t", t)));
    let wrapped = PseudoExpr::Let {
        name: "copy".into(),
        id: VarId::new(10).into(),
        value: PBox::new(helper),
        body: PBox::new(level),
    };
    let out = fold_unrolled_list_helper(wrapped);
    let PseudoExpr::Let { body, .. } = out else { panic!("let kept") };
    assert_eq!(body.into_inner(), var("xs", 1));
}

#[test]
fn non_identity_tail_is_kept() {
    let e = copy_when(var("xs", 1), 5, 6, |_| var("other", 99));
    assert_eq!(fold_unrolled_list_helper(e.clone()), e);
}
