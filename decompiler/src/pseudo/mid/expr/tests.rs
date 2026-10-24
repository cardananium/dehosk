use super::*;
use crate::pseudo::mid::expr_id::MidExprId;

fn id(n: u32) -> MidExprId {
    MidExprId::new(n)
}

fn var(n: u32) -> VarId {
    VarId::new(n)
}

#[test]
fn test_mid_expr_id() {
    let expr = MidExpr::Lit {
        id: id(0),
        value: MidLiteral::Integer(42.into()),
    };
    assert_eq!(expr.id(), id(0));
}

#[test]
fn test_children_lit() {
    let expr = MidExpr::Lit {
        id: id(0),
        value: MidLiteral::Bool(true),
    };
    assert_eq!(expr.children().len(), 0);
}

#[test]
fn test_children_apply() {
    let expr = MidExpr::Apply {
        id: id(0),
        function: MBox::new(MidExpr::Var {
            id: id(1),
            var: var(0),
        }),
        args: vec![
            MidExpr::Lit {
                id: id(2),
                value: MidLiteral::Integer(1.into()),
            },
            MidExpr::Lit {
                id: id(3),
                value: MidLiteral::Integer(2.into()),
            },
        ]
        .into(),
    };
    assert_eq!(expr.children().len(), 3);
    assert_eq!(expr.node_count(), 4);
}

#[test]
fn test_node_count_nested() {
    let inner = MidExpr::Lit {
        id: id(0),
        value: MidLiteral::Unit,
    };
    let thunk = MidExpr::Thunk {
        id: id(1),
        body: MBox::new(inner),
        cosmetic: true,
    };
    let force = MidExpr::Force {
        id: id(2),
        body: MBox::new(thunk),
        resolved: None,
    };
    assert_eq!(force.node_count(), 3);
}

/// What `#[derive(Debug)]` printed before `MidLiteral` got a hand-written
/// impl; the replacement must match it in both layouts.
#[derive(Debug)]
enum DerivedLiteral {
    Integer(BigInt),
    ByteString(Vec<u8>),
    String(String),
    Bool(bool),
    Unit,
    List(Vec<DerivedLiteral>),
    Pair(Box<DerivedLiteral>, Box<DerivedLiteral>),
    Bls12_381G1(Vec<u8>),
}

fn derived(lit: &MidLiteral) -> DerivedLiteral {
    match lit {
        MidLiteral::Integer(n) => DerivedLiteral::Integer(n.clone()),
        MidLiteral::ByteString(bytes) => DerivedLiteral::ByteString(bytes.clone()),
        MidLiteral::String(text) => DerivedLiteral::String(text.clone()),
        MidLiteral::Bool(b) => DerivedLiteral::Bool(*b),
        MidLiteral::Unit => DerivedLiteral::Unit,
        MidLiteral::List(items) => DerivedLiteral::List(items.iter().map(derived).collect()),
        MidLiteral::Pair(a, b) => DerivedLiteral::Pair(Box::new(derived(a)), Box::new(derived(b))),
        MidLiteral::Bls12_381G1(bytes) => DerivedLiteral::Bls12_381G1(bytes.clone()),
        other => panic!("not in the sample: {other:?}"),
    }
}

#[test]
fn mid_literal_debug_prints_what_the_derive_printed() {
    let lit = MidLiteral::List(vec![
        MidLiteral::Pair(
            Box::new(MidLiteral::String("a\"b".to_string())),
            Box::new(MidLiteral::List(Vec::new())),
        ),
        MidLiteral::Unit,
        MidLiteral::Bool(false),
        MidLiteral::Integer((-3).into()),
        MidLiteral::ByteString(vec![1, 2]),
        MidLiteral::Bls12_381G1(Vec::new()),
    ]);
    let reference = derived(&lit);
    assert_eq!(format!("{lit:?}"), format!("{reference:?}"));
    assert_eq!(format!("{lit:#?}"), format!("{reference:#?}"));
}

/// A list or pair constant nests as deep as the script makes it; clone,
/// equality, `Debug` and the destructor must not take a frame per level, nor
/// may cloning the `MidExpr` around it.
#[test]
fn deep_literals_and_trees_never_recurse() {
    const DEPTH: usize = 200_000;
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut lit = MidLiteral::Integer(1.into());
            for level in 0..DEPTH {
                lit = if level % 2 == 0 {
                    MidLiteral::List(vec![lit])
                } else {
                    MidLiteral::Pair(Box::new(lit), Box::new(MidLiteral::Unit))
                };
            }
            let copy = lit.clone();
            assert!(copy == lit);
            assert!(format!("{copy:?}").contains("Integer(1)"));

            let mut tree = MidExpr::Lit {
                id: id(0),
                value: lit,
            };
            for level in 1..=DEPTH as u32 {
                tree = MidExpr::Case {
                    id: id(level),
                    scrutinee: MBox::new(MidExpr::Var {
                        id: id(level),
                        var: var(0),
                    }),
                    branches: vec![MidBranch {
                        tag: 0,
                        binders: Vec::new(),
                        body: tree,
                    }],
                    encoding: CaseEncoding::Native,
                };
            }
            let tree_copy = tree.clone();
            assert_eq!(tree_copy.node_count(), tree.node_count());
            drop_iteratively(tree_copy);
            drop_iteratively(tree);
        })
        .expect("spawn");
    handle
        .join()
        .expect("deep literals must not overflow the stack");
}
