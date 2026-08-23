use super::*;
use crate::pseudo::mid::expr::{MidBranch, MidLiteral};

fn id(n: u64) -> MidExprId {
    MidExprId::new(n as u32)
}

fn var(n: u64, v: u32) -> MidExpr {
    MidExpr::Var {
        id: id(n),
        var: VarId::new(v),
    }
}

/// `\a b -> a` as curried closures (ids/vars offset by `base`).
fn fst_selector(base: u64) -> MidExpr {
    MidExpr::Closure {
        id: id(base),
        params: vec![VarId::new(base as u32 + 1)],
        body: Box::new(MidExpr::Closure {
            id: id(base + 1),
            params: vec![VarId::new(base as u32 + 2)],
            body: Box::new(var(base + 2, base as u32 + 1)),
            recursive: None,
        }),
        recursive: None,
    }
}

/// `\a b -> b`.
fn snd_selector(base: u64) -> MidExpr {
    MidExpr::Closure {
        id: id(base),
        params: vec![VarId::new(base as u32 + 1)],
        body: Box::new(MidExpr::Closure {
            id: id(base + 1),
            params: vec![VarId::new(base as u32 + 2)],
            body: Box::new(var(base + 2, base as u32 + 2)),
            recursive: None,
        }),
        recursive: None,
    }
}

fn thunk(n: u64, body: MidExpr) -> MidExpr {
    MidExpr::Thunk {
        id: id(n),
        body: Box::new(body),
        cosmetic: false,
    }
}

fn scott_bool_case(case_id: u64, scrutinee: MidExpr) -> MidExpr {
    MidExpr::Case {
        id: id(case_id),
        scrutinee: Box::new(scrutinee),
        branches: vec![
            MidBranch {
                tag: 0,
                binders: vec![],
                body: MidExpr::Lit {
                    id: id(case_id + 1),
                    value: MidLiteral::Unit,
                },
            },
            MidBranch {
                tag: 1,
                binders: vec![],
                body: MidExpr::Lit {
                    id: id(case_id + 2),
                    value: MidLiteral::Unit,
                },
            },
        ],
        encoding: CaseEncoding::Scott,
    }
}

fn if_producer(n: u64, then_branch: MidExpr, else_branch: MidExpr) -> MidExpr {
    MidExpr::If {
        id: id(n),
        condition: Box::new(MidExpr::Lit {
            id: id(n + 1),
            value: MidLiteral::Bool(true),
        }),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

/// `ifThenElse(c, <fst-sel>, <snd-sel>)` scrutinee => TrueFirst.
#[test]
fn if_of_selectors_is_true_first() {
    let tree = scott_bool_case(
        1000,
        if_producer(
            100,
            thunk(200, fst_selector(300)),
            thunk(210, snd_selector(400)),
        ),
    );
    let map = analyze_bool_orientations(&tree);
    assert_eq!(map.get(&id(1000)), Some(&Orientation::TrueFirst));
}

/// Swapped selectors => FalseFirst.
#[test]
fn if_of_swapped_selectors_is_false_first() {
    let tree = scott_bool_case(
        1000,
        if_producer(
            100,
            thunk(200, snd_selector(300)),
            thunk(210, fst_selector(400)),
        ),
    );
    let map = analyze_bool_orientations(&tree);
    assert_eq!(map.get(&id(1000)), Some(&Orientation::FalseFirst));
}

/// Selectors bound by `let`s, scrutinee = If over Vars.
#[test]
fn var_hops_resolve_through_let_env() {
    let case = scott_bool_case(1000, if_producer(100, var(101, 7), var(102, 8)));
    let tree = MidExpr::Let {
        id: id(1),
        var: VarId::new(7),
        value: Box::new(thunk(10, fst_selector(20))),
        use_count: 1,
        body: Box::new(MidExpr::Let {
            id: id(2),
            var: VarId::new(8),
            value: Box::new(thunk(11, snd_selector(40))),
            use_count: 1,
            body: Box::new(case),
        }),
    };
    let map = analyze_bool_orientations(&tree);
    assert_eq!(map.get(&id(1000)), Some(&Orientation::TrueFirst));
}

/// No witness (opaque scrutinee) => absent from the map (stays Unknown).
#[test]
fn opaque_scrutinee_is_unwitnessed() {
    let tree = scott_bool_case(1000, var(100, 9));
    let map = analyze_bool_orientations(&tree);
    assert!(map.is_empty());
}

/// Same selector on both If sides carries no orientation info.
#[test]
fn constant_selector_if_is_unwitnessed() {
    let tree = scott_bool_case(
        1000,
        if_producer(
            100,
            thunk(200, fst_selector(300)),
            thunk(210, fst_selector(400)),
        ),
    );
    let map = analyze_bool_orientations(&tree);
    assert!(map.is_empty());
}

/// Data-tag anchor: a Native two-arm dispatch whose tag-1 arm yields the
/// fst-selector is a decoded data Bool => TrueFirst.
#[test]
fn data_tag_decode_is_true_first() {
    let producer = MidExpr::Case {
        id: id(500),
        scrutinee: Box::new(var(501, 50)),
        branches: vec![
            MidBranch {
                tag: 0,
                binders: vec![],
                body: thunk(510, snd_selector(520)),
            },
            MidBranch {
                tag: 1,
                binders: vec![],
                body: thunk(530, fst_selector(540)),
            },
        ],
        encoding: CaseEncoding::IfChain,
    };
    let tree = scott_bool_case(1000, producer);
    let map = analyze_bool_orientations(&tree);
    assert_eq!(map.get(&id(1000)), Some(&Orientation::TrueFirst));
}
