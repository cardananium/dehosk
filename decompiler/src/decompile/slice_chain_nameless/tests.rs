use super::*;
use crate::pseudo::nameless::{VarMetadata, VarOrigin};

fn id() -> VarId {
    VarId::fresh_binding()
}

fn record_slice(table: &mut VarTable, alias: VarId, parent: VarId, depth: usize) {
    table.insert(
        alias,
        VarMetadata {
            origin: VarOrigin::LetBinder,
            name_hint: None,
            display_name_hint: None,
            kind: VarKind::SliceTailAlias { parent, depth },
        },
    );
}

/// Wrap a test expression in a Lambda whose params put the given
/// ambient binders in scope: `inline_slice_chain_nameless` skips
/// substitutions whose parent is not in scope.
fn wrap_in_scope(body: NamelessExpr, ambient: Vec<VarId>) -> NamelessExpr {
    NamelessExpr::Lambda {
        params: ambient,
        body: Box::new(body),
    }
}

fn unwrap_in_scope(expr: NamelessExpr) -> NamelessExpr {
    match expr {
        NamelessExpr::Lambda { body, .. } => *body,
        other => other,
    }
}

#[test]
fn folds_slice_alias_index_access_to_parent_indexed() {
    // Given: r = fields[1..] (depth 1), body has r[0]
    // Expect: body becomes fields[1] (1 + 0 = 1)
    let mut table = VarTable::new();
    let fields = id();
    let r = id();
    record_slice(&mut table, r, fields, 1);

    let expr = wrap_in_scope(
        NamelessExpr::Let {
            binder: r,
            value: NamelessExpr::Var(fields).into(),
            body: NamelessExpr::IndexAccess {
                collection: Box::new(NamelessExpr::Var(r)),
                index: 0,
            }
            .into(),
        },
        vec![fields],
    );
    let folded = unwrap_in_scope(inline_slice_chain_nameless(expr, &table));
    // Let dropped; result is IndexAccess(fields, 1)
    match folded {
        NamelessExpr::IndexAccess { collection, index } => {
            assert_eq!(index, 1);
            match *collection {
                NamelessExpr::Var(actual) => assert_eq!(actual, fields),
                other => panic!("expected Var(fields), got {other:?}"),
            }
        }
        other => panic!("expected IndexAccess, got {other:?}"),
    }
}

#[test]
fn folds_nested_slice_aliases_through_indexed_access() {
    // r = fields[1..]; t = r[1..] (so t = fields[2..]); u = t[0]
    // body: u-style access via t[0] should resolve to fields[2]
    let mut table = VarTable::new();
    let fields = id();
    let r = id();
    let t = id();
    record_slice(&mut table, r, fields, 1);
    record_slice(&mut table, t, r, 1);

    let expr = wrap_in_scope(
        NamelessExpr::IndexAccess {
            collection: Box::new(NamelessExpr::Var(t)),
            index: 0,
        },
        vec![fields],
    );
    let folded = unwrap_in_scope(inline_slice_chain_nameless(expr, &table));
    match folded {
        NamelessExpr::IndexAccess { collection, index } => {
            assert_eq!(index, 2);
            match *collection {
                NamelessExpr::Var(actual) => assert_eq!(actual, fields),
                other => panic!("expected Var(fields), got {other:?}"),
            }
        }
        other => panic!("expected IndexAccess, got {other:?}"),
    }
}

#[test]
fn cyclic_slice_alias_var_is_left_unchanged() {
    let mut table = VarTable::new();
    let r = id();
    let t = id();
    record_slice(&mut table, r, t, 1);
    record_slice(&mut table, t, r, 1);

    let folded = inline_slice_chain_nameless(NamelessExpr::Var(r), &table);

    assert!(
        matches!(folded, NamelessExpr::Var(actual) if actual == r),
        "cyclic slice aliases should not recurse forever or rewrite to a bogus base"
    );
}

#[test]
fn cyclic_slice_alias_index_access_keeps_collection_var() {
    let mut table = VarTable::new();
    let r = id();
    let t = id();
    record_slice(&mut table, r, t, 1);
    record_slice(&mut table, t, r, 1);

    let folded = inline_slice_chain_nameless(
        NamelessExpr::IndexAccess {
            collection: Box::new(NamelessExpr::Var(r)),
            index: 0,
        },
        &table,
    );

    match folded {
        NamelessExpr::IndexAccess { collection, index } => {
            assert_eq!(index, 0);
            assert!(matches!(collection.as_ref(), NamelessExpr::Var(actual) if *actual == r));
        }
        other => panic!("expected cyclic alias index access to stay indexed, got {other:?}"),
    }
}

#[test]
fn standalone_slice_alias_var_unfolds_to_list_tail_chain() {
    // Var(r) where r = fields[2..]
    // Expect: Apply(List.tail, [Apply(List.tail, [Var(fields)])])
    let mut table = VarTable::new();
    let fields = id();
    let r = id();
    record_slice(&mut table, r, fields, 2);

    let expr = wrap_in_scope(NamelessExpr::Var(r), vec![fields]);
    let folded = unwrap_in_scope(inline_slice_chain_nameless(expr, &table));
    // Outer List.tail wraps inner List.tail wraps fields.
    let inner = match folded {
        NamelessExpr::Apply { args, .. } => args.into_iter().next().unwrap(),
        other => panic!("expected outer Apply, got {other:?}"),
    };
    let base = match inner {
        NamelessExpr::Apply { args, .. } => args.into_iter().next().unwrap(),
        other => panic!("expected inner Apply, got {other:?}"),
    };
    match base {
        NamelessExpr::Var(actual) => assert_eq!(actual, fields),
        other => panic!("expected Var(fields), got {other:?}"),
    }
}

#[test]
fn non_alias_var_is_unchanged() {
    // Var without VarKind::SliceTailAlias passes through.
    let table = VarTable::new();
    let v = id();
    let expr = NamelessExpr::Var(v);
    let folded = inline_slice_chain_nameless(expr, &table);
    assert!(matches!(folded, NamelessExpr::Var(actual) if actual == v));
}

#[test]
fn let_binder_for_slice_alias_is_dropped() {
    // The binding `let r = ...` is removed because r is a slice
    // alias; body uses are unfolded directly.
    let mut table = VarTable::new();
    let fields = id();
    let r = id();
    record_slice(&mut table, r, fields, 1);

    let expr = NamelessExpr::Let {
        binder: r,
        value: NamelessExpr::Var(fields).into(),
        body: NamelessExpr::Int(num_bigint::BigInt::from(0)).into(),
    };
    let folded = inline_slice_chain_nameless(expr, &table);
    assert!(matches!(folded, NamelessExpr::Int(_)));
}

// ============================================================
// Scope-aware substitution guard
// ============================================================

/// When the alias parent is NOT in any enclosing scope at the
/// substitution site the pass must leave the alias Var unchanged,
/// or the substitution leaks `Var(parent)` as a free reference.
#[test]
fn slice_alias_var_not_substituted_when_parent_out_of_scope() {
    let mut table = VarTable::new();
    let fields = id(); // ambient parent — but NOT in any in-scope binder
    let r = id();
    record_slice(&mut table, r, fields, 2);

    // `Var(r)` with no binder for `fields` anywhere: the fold sees an
    // out-of-scope parent and must skip the substitution.
    let expr = NamelessExpr::Var(r);
    let folded = inline_slice_chain_nameless(expr, &table);

    // Expectation: `Var(r)` stays intact (no List.tail chain emitted).
    assert!(
        matches!(folded, NamelessExpr::Var(actual) if actual == r),
        "slice_chain must NOT substitute when parent is out of scope; got {folded:?}"
    );
}

/// Index-access variant of the scope-aware guard: `Var(r)[n]` where
/// `r` is a slice alias of `fields` and `fields` is not in scope
/// must keep the IndexAccess unchanged (no fold to `fields[depth+n]`).
#[test]
fn slice_alias_index_access_not_folded_when_parent_out_of_scope() {
    let mut table = VarTable::new();
    let fields = id();
    let r = id();
    record_slice(&mut table, r, fields, 2);

    let expr = NamelessExpr::IndexAccess {
        collection: Box::new(NamelessExpr::Var(r)),
        index: 1,
    };
    let folded = inline_slice_chain_nameless(expr, &table);

    // The IndexAccess stays with `Var(r)`; the Var-arm inside its
    // collection also consults `in_scope`, so it too skips.
    match folded {
        NamelessExpr::IndexAccess { collection, index } => {
            assert_eq!(index, 1, "index must not be adjusted when fold is skipped");
            match *collection {
                NamelessExpr::Var(actual) => assert_eq!(
                    actual, r,
                    "collection must remain Var(r); out-of-scope parent must not be inlined"
                ),
                other => panic!("expected Var(r), got {other:?}"),
            }
        }
        other => panic!("expected IndexAccess, got {other:?}"),
    }
}

/// The substitution DOES fire when the parent is in scope via a
/// Lambda param — the scope check must not over-suppress.
#[test]
fn slice_alias_var_substituted_when_parent_in_scope_via_lambda() {
    let mut table = VarTable::new();
    let fields = id();
    let r = id();
    record_slice(&mut table, r, fields, 1);

    let expr = wrap_in_scope(NamelessExpr::Var(r), vec![fields]);
    let folded = unwrap_in_scope(inline_slice_chain_nameless(expr, &table));

    // Now expect List.tail wrap because parent IS in scope.
    let inner = match folded {
        NamelessExpr::Apply { args, .. } => args.into_iter().next().unwrap(),
        other => panic!("expected List.tail Apply, got {other:?}"),
    };
    match inner {
        NamelessExpr::Var(actual) => assert_eq!(actual, fields),
        other => panic!("expected Var(fields), got {other:?}"),
    }
}

/// Nested scope: the parent binds in the outer lambda and the alias
/// is used in the inner one, whose body still sees outer params.
#[test]
fn slice_alias_var_substituted_through_nested_lambdas() {
    let mut table = VarTable::new();
    let fields = id(); // outer
    let inner_param = id();
    let r = id();
    record_slice(&mut table, r, fields, 1);

    let expr = NamelessExpr::Lambda {
        params: vec![fields],
        body: Box::new(NamelessExpr::Lambda {
            params: vec![inner_param],
            body: Box::new(NamelessExpr::Var(r)),
        }),
    };
    let folded = inline_slice_chain_nameless(expr, &table);

    // Drill into the inner lambda's body.
    let inner_body = match folded {
        NamelessExpr::Lambda { body, .. } => match *body {
            NamelessExpr::Lambda { body, .. } => *body,
            other => panic!("expected inner Lambda, got {other:?}"),
        },
        other => panic!("expected outer Lambda, got {other:?}"),
    };
    let arg = match inner_body {
        NamelessExpr::Apply { args, .. } => args.into_iter().next().unwrap(),
        other => panic!("expected List.tail Apply, got {other:?}"),
    };
    match arg {
        NamelessExpr::Var(actual) => assert_eq!(actual, fields),
        other => panic!("expected Var(fields), got {other:?}"),
    }
}

#[test]
fn preserves_unused_effectful_slice_alias_let() {
    let mut table = VarTable::new();
    let fields = id();
    let r = id();
    record_slice(&mut table, r, fields, 1);

    let expr = NamelessExpr::Let {
        binder: r,
        value: NamelessExpr::Apply {
            function: Box::new(NamelessExpr::BuiltinCall {
                name: "List.tail".to_string().into(),
                args: vec![],
            }),
            args: vec![NamelessExpr::Var(fields)],
        }
        .into(),
        body: NamelessExpr::Unit.into(),
    };

    let folded = inline_slice_chain_nameless(expr, &table);

    match folded {
        NamelessExpr::Let {
            binder,
            value,
            body,
        } => {
            assert_eq!(binder, r);
            assert!(
                matches!(value.as_ref(), NamelessExpr::Apply { .. }),
                "expected effectful alias value to be preserved, got: {value:?}"
            );
            assert!(matches!(body.as_ref(), NamelessExpr::Unit));
        }
        other => panic!("expected effectful alias let to be preserved, got {other:?}"),
    }
}
