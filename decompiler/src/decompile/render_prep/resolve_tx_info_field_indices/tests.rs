use super::*;
use crate::pseudo::ast::PBox;

use crate::pseudo::var_id::VarId;

/// A fixed VarId for the validator entry `script_context` param, kept well
/// below `AUTHORITATIVE_BINDING_START` (1e9) so it never collides with
/// `fresh_binding()`. `tx_info_let` references it, and the runners auto-wrap
/// exprs in `entry(entry_sc_id(), ..)` so the VarId-gated tx_info-alias
/// collection fires.
fn entry_sc_id() -> VarId {
    VarId::new(990001)
}

/// Build `let tx_info(id) = <entry script_context>.tx_info in <body>`.
///
/// The `script_context` reference carries [`entry_sc_id`] so the VarId-gated
/// `collect_tx_info_binders` accepts it once the expr is wrapped in the matching
/// `entry(..)` (done by the collection runners).
fn tx_info_let(id: VarId, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "tx_info".to_string(),
        id: Some(id),
        value: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var_with_id("script_context", entry_sc_id()),
            "tx_info",
        )),
        body: PBox::new(body),
    }
}

/// `tx_info(id).fields[index]`.
fn tx_info_field(id: VarId, index: usize) -> PseudoExpr {
    PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::field_access(
            PseudoExpr::Var {
                name: "tx_info".to_string(),
                id: Some(id),
            },
            "fields",
        )),
        index,
    }
}

/// True when `expr` is already the validator entry (`let decompiled =
/// fn(script_context){..}`) — the entry-param tests build this directly.
fn is_entry_rooted(expr: &PseudoExpr) -> bool {
    matches!(expr, PseudoExpr::Let { name, .. } if name == "decompiled")
}

/// Extract the `decompiled` lambda body by value.
fn entry_body_owned(out: PseudoExpr) -> PseudoExpr {
    let PseudoExpr::Let { value, .. } = out else {
        panic!("expected decompiled Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.into_inner() else {
        panic!("expected Lambda")
    };
    body.into_inner()
}

/// Run `pass` on `expr`. If `expr` is not already entry-rooted, wrap it in
/// `entry(entry_sc_id(), ..)` first — so the VarId-gated tx_info-alias
/// collection fires — and return the unwrapped body, so the assertions can
/// destructure the `tx_info` let directly.
fn with_entry_collection<F: FnOnce(PseudoExpr) -> PseudoExpr>(
    expr: PseudoExpr,
    pass: F,
) -> PseudoExpr {
    if is_entry_rooted(&expr) {
        pass(expr)
    } else {
        entry_body_owned(pass(entry(entry_sc_id(), expr)))
    }
}

/// Run the pass with `version` on both channels.
fn run_with_version(expr: PseudoExpr, version: Option<ScriptVersion>) -> PseudoExpr {
    with_entry_collection(expr, |e| {
        resolve_tx_info_field_indices(e, &RenderCtx::at(version))
    })
}

/// Assert `expr` is `record.<field_name>` (a `NamedField` access).
fn assert_named_field(expr: &PseudoExpr, field_name: &str) {
    match expr {
        PseudoExpr::FieldAccess { selector, .. } => {
            assert_eq!(
                selector.as_pretty_name(),
                field_name,
                "expected field `{field_name}`, got `{}`",
                selector.as_pretty_name()
            );
        }
        other => panic!("expected FieldAccess `.{field_name}`, got {other:?}"),
    }
}

#[test]
fn resolves_let_bound_tx_info_fields_v3() {
    let id = VarId::fresh_binding();
    // let tx_info = script_context.tx_info in tx_info.fields[0]
    let expr = tx_info_let(id, tx_info_field(id, 0));
    let out = run_with_version(expr, Some(ScriptVersion::PlutusV3));
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected Let");
    };
    assert_named_field(&body, "inputs");
}

#[test]
fn resolves_reference_inputs_index_1_under_v3() {
    // Index 1 is `reference_inputs` in V2/V3 (it is `outputs` in V1) — proves
    // the version actually drives the mapping.
    let id = VarId::fresh_binding();
    let expr = tx_info_let(id, tx_info_field(id, 1));
    let out = run_with_version(expr, Some(ScriptVersion::PlutusV3));
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected Let");
    };
    assert_named_field(&body, "reference_inputs");
}

#[test]
fn same_index_maps_differently_for_v1() {
    // Index 1 → `outputs` under V1 (10-field TxInfo, no reference_inputs).
    let id = VarId::fresh_binding();
    let expr = tx_info_let(id, tx_info_field(id, 1));
    let out = run_with_version(expr, Some(ScriptVersion::PlutusV1));
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected Let");
    };
    assert_named_field(&body, "outputs");
}

#[test]
fn noop_without_version() {
    // No version set → positional `.fields[N]` preserved unchanged.
    let id = VarId::fresh_binding();
    let expr = tx_info_let(id, tx_info_field(id, 0));
    let out = run_with_version(expr.clone(), None);
    assert_eq!(out, expr, "pass must be a no-op when no version is active");
}

#[test]
fn bounds_check_leaves_out_of_range_index() {
    // Index 20 exceeds even the V3 arity (16) → left as positional `.fields[20]`.
    let id = VarId::fresh_binding();
    let expr = tx_info_let(id, tx_info_field(id, 20));
    let out = run_with_version(expr, Some(ScriptVersion::PlutusV3));
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected Let");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::IndexAccess { index: 20, .. }),
        "out-of-range index must stay positional, got {body:?}"
    );
}

#[test]
fn leaves_inline_script_context_tx_info_positional() {
    // `script_context.tx_info.fields[2]` with NO let alias is deliberately
    // left positional: the only sound anchor is the identity-tracked let
    // binder, not the name-only `script_context` match, which could false-hit
    // a non-entry-param binder.
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::field_access(
            PseudoExpr::field_access(PseudoExpr::var("script_context"), "tx_info"),
            "fields",
        )),
        index: 2,
    };
    let out = run_with_version(expr.clone(), Some(ScriptVersion::PlutusV3));
    assert_eq!(out, expr, "inline (un-aliased) form must stay positional");
}

#[test]
fn leaves_non_tx_info_record() {
    // `other.fields[0]` where `other` is not TxInfo → unchanged.
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::field_access(PseudoExpr::var("other"), "fields")),
        index: 0,
    };
    let out = run_with_version(expr.clone(), Some(ScriptVersion::PlutusV3));
    assert_eq!(out, expr, "non-TxInfo record must be left positional");
}

/// Build `let tx_info(tid) = script_context.tx_info in
///   let <binder_name>(fid) = tx_info.fields[index] in <binder_name>`.
fn aliased_field(tid: VarId, fid: VarId, binder_name: &str, index: usize) -> PseudoExpr {
    let inner = PseudoExpr::Let {
        name: binder_name.to_string(),
        id: Some(fid),
        value: PBox::new(tx_info_field(tid, index)),
        body: PBox::new(PseudoExpr::Var {
            name: binder_name.to_string(),
            id: Some(fid),
        }),
    };
    tx_info_let(tid, inner)
}

/// Drill to the inner `let` (the field alias) inside the `tx_info` let.
fn inner_let(out: PseudoExpr) -> (String, PseudoExpr, PseudoExpr) {
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected outer tx_info Let");
    };
    let PseudoExpr::Let {
        name, value, body, ..
    } = body.into_inner()
    else {
        panic!("expected inner field-alias Let");
    };
    (name, value.into_inner(), body.into_inner())
}

#[test]
fn renames_synthetic_field_alias_to_descriptive() {
    // let field_0_159 = tx_info.fields[0]  →  let tx_inputs_0 = tx_info.inputs
    let tid = VarId::fresh_binding();
    let fid = VarId::fresh_binding();
    let out = run_with_version(
        aliased_field(tid, fid, "field_0_159", 0),
        Some(ScriptVersion::PlutusV3),
    );
    let (name, value, body) = inner_let(out);
    assert_eq!(name, "tx_inputs_0", "binder renamed to tx_<field>_<idx>");
    assert_named_field(&value, "inputs");
    assert!(
        matches!(&body, PseudoExpr::Var { name, .. } if name == "tx_inputs_0"),
        "body reference renamed too, got {body:?}"
    );
}

#[test]
fn rename_uses_schema_index() {
    // index 1 in V3 is reference_inputs → tx_reference_inputs_1
    let tid = VarId::fresh_binding();
    let fid = VarId::fresh_binding();
    let out = run_with_version(
        aliased_field(tid, fid, "field_1_158", 1),
        Some(ScriptVersion::PlutusV3),
    );
    let (name, _, _) = inner_let(out);
    assert_eq!(name, "tx_reference_inputs_1");
}

#[test]
fn does_not_rename_non_synthetic_binder() {
    // A non-`field_N` binder name is never clobbered; only the field access
    // is relabeled.
    let tid = VarId::fresh_binding();
    let fid = VarId::fresh_binding();
    let out = run_with_version(
        aliased_field(tid, fid, "my_inputs", 0),
        Some(ScriptVersion::PlutusV3),
    );
    let (name, value, _) = inner_let(out);
    assert_eq!(name, "my_inputs", "non-synthetic binder name preserved");
    assert_named_field(&value, "inputs"); // field access still relabeled
}

#[test]
fn rename_noop_without_version() {
    let tid = VarId::fresh_binding();
    let fid = VarId::fresh_binding();
    let expr = aliased_field(tid, fid, "field_0_159", 0);
    let out = run_with_version(expr.clone(), None);
    assert_eq!(out, expr, "no rename (and no relabel) without a version");
}

// ---- derived decode-alias naming ----

use crate::builtins::BuiltinId;

/// `builtin.un_list_data(arg)` (direct BuiltinCall form).
fn un_list_data(arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnList,
        args: vec![arg].into(),
    }
}

fn un_map_data(arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnMap,
        args: vec![arg].into(),
    }
}

/// `let tx_info(tid) = script_context.tx_info in
///    let <fa_name>(fa) = tx_info.fields[index] in
///      let <decode_name>(dec) = un_*_data(<fa>) in <decode_name>`
fn decode_over_field(
    tid: VarId,
    fa: VarId,
    fa_name: &str,
    index: usize,
    dec: VarId,
    decode_name: &str,
    decode: fn(PseudoExpr) -> PseudoExpr,
) -> PseudoExpr {
    let inner = PseudoExpr::Let {
        name: decode_name.to_string(),
        id: Some(dec),
        value: PBox::new(decode(PseudoExpr::Var {
            name: fa_name.to_string(),
            id: Some(fa),
        })),
        body: PBox::new(PseudoExpr::Var {
            name: decode_name.to_string(),
            id: Some(dec),
        }),
    };
    let mid = PseudoExpr::Let {
        name: fa_name.to_string(),
        id: Some(fa),
        value: PBox::new(tx_info_field(tid, index)),
        body: PBox::new(inner),
    };
    tx_info_let(tid, mid)
}

/// Drill to the innermost (decode-alias) let and return its binder name.
fn innermost_let_name(out: PseudoExpr) -> String {
    let PseudoExpr::Let { body, .. } = out else {
        panic!("outer tx_info let");
    };
    let PseudoExpr::Let { body, .. } = body.into_inner() else {
        panic!("field-alias let");
    };
    let PseudoExpr::Let { name, .. } = body.into_inner() else {
        panic!("decode-alias let");
    };
    name
}

#[test]
fn renames_un_list_decode_alias_to_field_list() {
    // let fields_0_2_list = un_list_data(tx_inputs_0)  →  let inputs_list = ...
    let tid = VarId::fresh_binding();
    let fa = VarId::fresh_binding();
    let dec = VarId::fresh_binding();
    let out = run_with_version(
        decode_over_field(
            tid,
            fa,
            "field_0_159",
            0,
            dec,
            "fields_0_2_list",
            un_list_data,
        ),
        Some(ScriptVersion::PlutusV3),
    );
    assert_eq!(innermost_let_name(out), "inputs_list");
}

#[test]
fn renames_un_map_decode_alias_to_field_map() {
    // index 4 (mint) decoded as a map → mint_map
    let tid = VarId::fresh_binding();
    let fa = VarId::fresh_binding();
    let dec = VarId::fresh_binding();
    let out = run_with_version(
        decode_over_field(tid, fa, "field_4_46", 4, dec, "field_2_3_map", un_map_data),
        Some(ScriptVersion::PlutusV3),
    );
    assert_eq!(innermost_let_name(out), "mint_map");
}

#[test]
fn decode_alias_inline_tx_info_field_source() {
    // let field_0_3_list = un_list_data(tx_info.inputs)  (no field alias) → inputs_list
    let tid = VarId::fresh_binding();
    let dec = VarId::fresh_binding();
    let inner = PseudoExpr::Let {
        name: "field_0_3_list".to_string(),
        id: Some(dec),
        value: PBox::new(un_list_data(PseudoExpr::field_access(
            PseudoExpr::Var {
                name: "tx_info".to_string(),
                id: Some(tid),
            },
            "inputs",
        ))),
        body: PBox::new(PseudoExpr::Var {
            name: "field_0_3_list".to_string(),
            id: Some(dec),
        }),
    };
    let out = run_with_version(tx_info_let(tid, inner), Some(ScriptVersion::PlutusV3));
    let PseudoExpr::Let { body, .. } = out else {
        panic!("tx_info let");
    };
    let PseudoExpr::Let { name, .. } = body.into_inner() else {
        panic!("decode let");
    };
    assert_eq!(name, "inputs_list");
}

#[test]
fn does_not_rename_non_decode_binder_name() {
    // A binder that is NOT the synthetic `field(s)_N_list/_map` shape is left
    // alone even if it decodes a tx field.
    let tid = VarId::fresh_binding();
    let fa = VarId::fresh_binding();
    let dec = VarId::fresh_binding();
    let out = run_with_version(
        decode_over_field(tid, fa, "field_0_159", 0, dec, "my_list", un_list_data),
        Some(ScriptVersion::PlutusV3),
    );
    assert_eq!(innermost_let_name(out), "my_list");
}

#[test]
fn does_not_rename_decode_of_non_tx_field() {
    // un_list_data over a non-TxInfo var → no schema anchor → left synthetic.
    let dec = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "fields_0_2_list".to_string(),
        id: Some(dec),
        value: PBox::new(un_list_data(PseudoExpr::var("some_other_data"))),
        body: PBox::new(PseudoExpr::Var {
            name: "fields_0_2_list".to_string(),
            id: Some(dec),
        }),
    };
    let out = run_with_version(expr, Some(ScriptVersion::PlutusV3));
    let PseudoExpr::Let { name, .. } = out else {
        panic!("let");
    };
    assert_eq!(name, "fields_0_2_list", "no tx-field anchor → unchanged");
}

#[test]
fn is_synthetic_decode_alias_name_matches_expected() {
    assert!(is_synthetic_decode_alias_name("fields_0_2_list"));
    assert!(is_synthetic_decode_alias_name("field_2_3_list"));
    assert!(is_synthetic_decode_alias_name("field_0_3_list"));
    assert!(is_synthetic_decode_alias_name("field_4_map"));
    // Rejected: already-named (no field prefix), the field alias itself, junk.
    assert!(!is_synthetic_decode_alias_name("inputs_list"));
    assert!(!is_synthetic_decode_alias_name("tx_inputs_0"));
    assert!(!is_synthetic_decode_alias_name("field_7_48"));
    assert!(!is_synthetic_decode_alias_name("field_a_list"));
}

// ---- list-element naming (get_at Some-payload) ----

use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
use crate::pseudo::constructor::KnownConstructor;

/// `get_at(<list_var>, idx)` call (function head is a Var named "get_at").
fn get_at_call(list_id: VarId, list_name: &str) -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: "get_at".to_string(),
            id: Some(VarId::fresh_binding()),
        }),
        args: vec![
            PseudoExpr::Var {
                name: list_name.to_string(),
                id: Some(list_id),
            },
            PseudoExpr::int(0),
        ]
        .into(),
    }
}

/// `when <subject> is { Some(<elem_name>(elem)) -> <body>; None -> 0 }`.
fn when_some(subject: PseudoExpr, elem: VarId, elem_name: &str, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor_known(
                    KnownConstructor::Some,
                    vec![Binder::new(elem_name, elem)],
                ),
                body,
            ),
            WhenClause::new(
                WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                PseudoExpr::int(0),
            ),
        ],
    }
}

/// `let inputs_list(lid) = un_list_data(tx_info(tid).inputs) in <body>`.
fn with_inputs_list(tid: VarId, lid: VarId, body: PseudoExpr) -> PseudoExpr {
    let inner = PseudoExpr::Let {
        name: "inputs_list".to_string(),
        id: Some(lid),
        value: PBox::new(un_list_data(PseudoExpr::field_access(
            PseudoExpr::Var {
                name: "tx_info".to_string(),
                id: Some(tid),
            },
            "inputs",
        ))),
        body: PBox::new(body),
    };
    tx_info_let(tid, inner)
}

#[test]
fn names_get_at_some_payload_as_singular() {
    // expect Some(item) = get_at(inputs_list, 0) → Some(input); refs follow.
    let tid = VarId::fresh_binding();
    let lid = VarId::fresh_binding();
    let elem = VarId::fresh_binding();
    let body = PseudoExpr::field_access(
        PseudoExpr::Var {
            name: "item".to_string(),
            id: Some(elem),
        },
        "fields",
    );
    let when = when_some(get_at_call(lid, "inputs_list"), elem, "item", body);
    let out = run_with_version(
        with_inputs_list(tid, lid, when),
        Some(ScriptVersion::PlutusV3),
    );
    let found = find_some_binder_name(&out);
    assert_eq!(
        found.as_deref(),
        Some("input"),
        "Some payload renamed to singular"
    );
}

#[test]
fn does_not_name_element_of_non_list_source() {
    // get_at over an opaque var (not a tx list field) → element stays `item`.
    let elem = VarId::fresh_binding();
    let when = when_some(
        get_at_call(VarId::fresh_binding(), "some_other_list"),
        elem,
        "item",
        PseudoExpr::var("unused"),
    );
    // still need a version active + a tx_info binder so the pass runs
    let tid = VarId::fresh_binding();
    let out = run_with_version(tx_info_let(tid, when), Some(ScriptVersion::PlutusV3));
    assert_eq!(
        find_some_binder_name(&out).as_deref(),
        Some("item"),
        "opaque source unchanged"
    );
}

#[test]
fn does_not_name_when_subject_is_not_get_at() {
    // A plain `when find(inputs_list) is { Some(x) }` is NOT get_at → unchanged
    // (find's payload is not provably the element).
    let tid = VarId::fresh_binding();
    let lid = VarId::fresh_binding();
    let elem = VarId::fresh_binding();
    let find_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("find")),
        args: vec![PseudoExpr::Var {
            name: "inputs_list".to_string(),
            id: Some(lid),
        }]
        .into(),
    };
    let when = when_some(find_call, elem, "item", PseudoExpr::var("unused"));
    let out = run_with_version(
        with_inputs_list(tid, lid, when),
        Some(ScriptVersion::PlutusV3),
    );
    assert_eq!(
        find_some_binder_name(&out).as_deref(),
        Some("item"),
        "find payload not named"
    );
}

#[test]
fn list_field_singular_table() {
    assert_eq!(list_field_singular("inputs"), Some("input"));
    assert_eq!(
        list_field_singular("reference_inputs"),
        Some("reference_input")
    );
    assert_eq!(list_field_singular("signatories"), Some("signatory"));
    assert_eq!(list_field_singular("outputs"), Some("output"));
    // scalar / map fields have no element
    assert_eq!(list_field_singular("fee"), None);
    assert_eq!(list_field_singular("mint"), None);
    assert_eq!(list_field_singular("withdrawals"), None);
    assert_eq!(list_field_singular("id"), None);
}

/// Find the first `Some(_)` constructor-pattern binder name anywhere in `expr`.
fn find_some_binder_name(expr: &PseudoExpr) -> Option<String> {
    use crate::pseudo::constructor::ConstructorShape;
    if let PseudoExpr::When { clauses, .. } = expr {
        for c in clauses {
            if let WhenPattern::Constructor { shape, fields, .. } = &c.pattern
                && matches!(shape, ConstructorShape::Known(KnownConstructor::Some))
                && fields.len() == 1
            {
                return Some(fields[0].as_str().to_string());
            }
        }
    }
    for child in super::children(expr) {
        if let Some(n) = find_some_binder_name(child) {
            return Some(n);
        }
    }
    None
}

// ---- (late) interproc rec-fn list-param + cons-head naming ----

/// `let <fn_name>(lid) = rec fn <fn_name>(rid)(p0) {
///    when p0 is { [] -> 0; [head, ..tail] -> <fn_name>(rid)(tail) } }
///  in <fn_name>(lid)(<src_name>(src_id))`
/// wrapped in `let tx_info = script_context.tx_info; let <src_name> =
/// un_list_data(tx_info.inputs)`.
fn iter_rec_over_inputs(fn_name: &str) -> PseudoExpr {
    let tid = VarId::fresh_binding();
    let src = VarId::fresh_binding();
    let lid = VarId::fresh_binding();
    let rid = VarId::fresh_binding();
    let p0 = VarId::fresh_binding();
    let head = VarId::fresh_binding();
    let tail = VarId::fresh_binding();
    let rec_body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "list".to_string(),
            id: Some(p0),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::int(0),
            ),
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![Binder::new("head", head)],
                    tail: Some(Binder::new("tail", tail)),
                },
                // recursive call on the cons-tail
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::Var {
                        name: fn_name.to_string(),
                        id: Some(rid),
                    }),
                    args: vec![PseudoExpr::Var {
                        name: "tail".to_string(),
                        id: Some(tail),
                    }]
                    .into(),
                },
            ),
        ],
    };
    let rec_fn = PseudoExpr::RecFn {
        name: Binder::new(fn_name, rid),
        params: vec![Binder::new("list", p0)],
        body: PBox::new(rec_body),
    };
    let external_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: fn_name.to_string(),
            id: Some(lid),
        }),
        args: vec![PseudoExpr::Var {
            name: "inputs_list".to_string(),
            id: Some(src),
        }]
        .into(),
    };
    let fn_let = PseudoExpr::Let {
        name: fn_name.to_string(),
        id: Some(lid),
        value: PBox::new(rec_fn),
        body: PBox::new(external_call),
    };
    let src_let = PseudoExpr::Let {
        name: "inputs_list".to_string(),
        id: Some(src),
        value: PBox::new(un_list_data(PseudoExpr::field_access(
            PseudoExpr::Var {
                name: "tx_info".to_string(),
                id: Some(tid),
            },
            "inputs",
        ))),
        body: PBox::new(fn_let),
    };
    tx_info_let(tid, src_let)
}

/// Find the first RecFn and return (param0 display name, cons-head display name).
fn rec_fn_param_and_head(expr: &PseudoExpr) -> Option<(String, String)> {
    if let PseudoExpr::RecFn { params, body, .. } = expr {
        let p0 = params.first()?.as_str().to_string();
        let head = find_cons_head_name(body)?;
        return Some((p0, head));
    }
    for child in super::children(expr) {
        if let Some(r) = rec_fn_param_and_head(child) {
            return Some(r);
        }
    }
    None
}

fn find_cons_head_name(expr: &PseudoExpr) -> Option<String> {
    if let PseudoExpr::When { clauses, .. } = expr {
        for c in clauses {
            if let WhenPattern::List {
                elements,
                tail: Some(_),
            } = &c.pattern
                && elements.len() == 1
            {
                return Some(elements[0].as_str().to_string());
            }
        }
    }
    for child in super::children(expr) {
        if let Some(r) = find_cons_head_name(child) {
            return Some(r);
        }
    }
    None
}

/// Run the LATE pass (cons-head + interproc) with `version` active.
fn run_late_with_version(expr: PseudoExpr, version: Option<ScriptVersion>) -> PseudoExpr {
    with_entry_collection(expr, |e| {
        rename_list_element_binders_late(e, &RenderCtx::at(version))
    })
}

#[test]
fn interproc_names_opaque_rec_fn_param_and_head() {
    // rec_fn_5 fed only inputs_list (+ recursive tail) → param `list` → `inputs`,
    // cons-head `head` → `input`.
    let out = run_late_with_version(
        iter_rec_over_inputs("rec_fn_5"),
        Some(ScriptVersion::PlutusV3),
    );
    let (param, head) = rec_fn_param_and_head(&out).expect("rec fn");
    assert_eq!(
        param, "inputs",
        "opaque rec-fn list param renamed to plural"
    );
    assert_eq!(head, "input", "its cons-head renamed to singular");
}

#[test]
fn interproc_skips_generic_combinator() {
    // Same shape but the fn is a recognized generic combinator (`any`) → its
    // generic `list` param is preserved (not specialized to `inputs`).
    let out = run_late_with_version(iter_rec_over_inputs("any"), Some(ScriptVersion::PlutusV3));
    let (param, head) = rec_fn_param_and_head(&out).expect("rec fn");
    assert_eq!(param, "list", "generic combinator param left generic");
    assert_eq!(head, "head", "and its cons-head left generic");
}

#[test]
fn is_opaque_rec_name_matches() {
    assert!(is_opaque_rec_name("rec_fn_12"));
    assert!(is_opaque_rec_name("rec_fn_13"));
    assert!(is_opaque_rec_name("helper_7"));
    assert!(!is_opaque_rec_name("get_at"));
    assert!(!is_opaque_rec_name("any"));
    assert!(!is_opaque_rec_name("find"));
    assert!(!is_opaque_rec_name("lookup"));
}

#[test]
fn leaves_unrelated_let_binder_with_same_shape() {
    // A binder NOT bound to script_context.tx_info, even if it has `.fields[N]`,
    // is not rewritten (no false positive on arbitrary records).
    let id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "datum".to_string(),
        id: Some(id),
        value: PBox::new(PseudoExpr::var("some_data")),
        body: PBox::new(tx_info_field(id, 0)),
    };
    let out = run_with_version(expr.clone(), Some(ScriptVersion::PlutusV3));
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected Let");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::IndexAccess { index: 0, .. }),
        "binder not bound to script_context.tx_info must stay positional, got {body:?}"
    );
}

// ---- ScriptContext entry-param `script_context.fields[N]` resolution ----
// The arm is VarId-gated on the validator entry param (the `decompiled` lambda's
// `script_context` binder), so a helper param coincidentally named
// `script_context` is NOT mis-labeled.

/// `Var(script_context#sc_id).fields[index]`.
fn sc_field_of(sc_id: VarId, index: usize) -> PseudoExpr {
    PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var_with_id("script_context", sc_id),
            "fields",
        )),
        index,
    }
}

/// Wrap `body` as the validator entry `let decompiled = fn(script_context#sc_id) { body }`.
fn entry(sc_id: VarId, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "decompiled".to_string(),
        id: Some(VarId::new(99000)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("script_context".to_string(), sc_id)],
            body: PBox::new(body),
        }),
        body: PBox::new(PseudoExpr::Unit),
    }
}

/// Extract the `decompiled` lambda body after the pass ran.
fn entry_body(out: &PseudoExpr) -> &PseudoExpr {
    let PseudoExpr::Let { value, .. } = out else {
        panic!("expected decompiled Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.as_ref() else {
        panic!("expected Lambda")
    };
    body.as_ref()
}

#[test]
fn sc_fields_2_resolves_to_script_info_v3() {
    let sc = VarId::new(70001);
    let out = run_with_version(entry(sc, sc_field_of(sc, 2)), Some(ScriptVersion::PlutusV3));
    assert_named_field(entry_body(&out), "script_info");
}

#[test]
fn sc_fields_0_1_2_resolve_v3() {
    for (idx, name) in [(0, "tx_info"), (1, "redeemer"), (2, "script_info")] {
        let sc = VarId::new(70010 + idx as u32);
        let out = run_with_version(
            entry(sc, sc_field_of(sc, idx)),
            Some(ScriptVersion::PlutusV3),
        );
        assert_named_field(entry_body(&out), name);
    }
}

#[test]
fn sc_fields_v1_v2_resolve_purpose() {
    let sc = VarId::new(70020);
    assert_named_field(
        entry_body(&run_with_version(
            entry(sc, sc_field_of(sc, 1)),
            Some(ScriptVersion::PlutusV1),
        )),
        "purpose",
    );
    let sc2 = VarId::new(70021);
    assert_named_field(
        entry_body(&run_with_version(
            entry(sc2, sc_field_of(sc2, 1)),
            Some(ScriptVersion::PlutusV2),
        )),
        "purpose",
    );
}

#[test]
fn sc_fields_out_of_range_left_positional() {
    let sc = VarId::new(70030);
    let out = run_with_version(entry(sc, sc_field_of(sc, 3)), Some(ScriptVersion::PlutusV3));
    assert!(
        matches!(entry_body(&out), PseudoExpr::IndexAccess { index: 3, .. }),
        "out-of-range ScriptContext index must stay positional"
    );
}

#[test]
fn sc_fields_no_version_is_noop() {
    let sc = VarId::new(70040);
    let expr = entry(sc, sc_field_of(sc, 2));
    let out = run_with_version(expr.clone(), None);
    assert_eq!(
        out, expr,
        "no version → ScriptContext field access stays positional"
    );
}

#[test]
fn sc_fields_nested_helper_param_not_relabeled() {
    // A helper param named `script_context` (NOT the entry, a DIFFERENT VarId)
    // holds arbitrary data, so `.fields[2]` must stay positional — relabeling
    // it to `.script_info` would be valid-looking-wrong.
    let entry_sc = VarId::new(70050);
    let helper_sc = VarId::new(70051);
    let out = run_with_version(
        entry(entry_sc, sc_field_of(helper_sc, 2)),
        Some(ScriptVersion::PlutusV3),
    );
    assert!(
        matches!(entry_body(&out), PseudoExpr::IndexAccess { index: 2, .. }),
        "a non-entry `script_context` VarId must stay positional, not become .script_info"
    );
}

#[test]
fn tx_info_alias_off_nested_helper_param_not_relabeled() {
    // Sibling of `sc_fields_nested_helper_param_not_relabeled`, one hop through a
    // `tx_info` alias: a helper param named `script_context` (NOT the entry — a
    // DIFFERENT VarId) binds `let tx_info = script_context.tx_info`, so
    // `tx_info.fields[0]` must stay POSITIONAL — relabeling it to `.inputs` would
    // be valid-looking-wrong: the helper holds arbitrary `Data`, not real TxInfo.
    // `collect_tx_info_binders` is VarId-gated on the entry, so it isn't collected.
    let entry_sc = VarId::new(70070);
    let helper_sc = VarId::new(70071); // distinct, non-entry `script_context`
    let tid = VarId::fresh_binding();
    let inner = PseudoExpr::Let {
        name: "tx_info".to_string(),
        id: Some(tid),
        value: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var_with_id("script_context", helper_sc),
            "tx_info",
        )),
        body: PBox::new(tx_info_field(tid, 0)),
    };
    // entry-rooted ⇒ no auto-wrap; entry_sc_ids = {entry_sc}, excluding helper_sc.
    let out = run_with_version(entry(entry_sc, inner), Some(ScriptVersion::PlutusV3));
    let PseudoExpr::Let { body, .. } = entry_body(&out) else {
        panic!("expected tx_info let");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::IndexAccess { index: 0, .. }),
        "tx_info alias off a NON-entry `script_context` must stay positional, got {body:?}"
    );
}

/// Run with the strict channel `None` (V1/V2-ambiguous) but the SC channel
/// set to `sc` — the production ambiguous-mode configuration.
fn run_with_sc_version(expr: PseudoExpr, sc: Option<ScriptVersion>) -> PseudoExpr {
    with_entry_collection(expr, |e| {
        resolve_tx_info_field_indices(e, &RenderCtx::new(None, sc))
    })
}

/// `Var(script_context#sc_id).fields.head` — the church-pair inline form
/// of slot 0 (a FieldAccess+ListHead, never IndexAccess).
fn sc_fields_head_of(sc_id: VarId) -> PseudoExpr {
    PseudoExpr::field_access_typed(
        PseudoExpr::field_access(PseudoExpr::var_with_id("script_context", sc_id), "fields"),
        FieldSelector::ListHead,
    )
}

#[test]
fn sc_fields_head_resolves_to_tx_info_all_versions() {
    // Slot 0 = tx_info in V1, V2, V3 — version-agnostic by layout identity.
    for v in [
        ScriptVersion::PlutusV1,
        ScriptVersion::PlutusV2,
        ScriptVersion::PlutusV3,
    ] {
        let sc = VarId::new(71000 + v as u32);
        let out = run_with_version(entry(sc, sc_fields_head_of(sc)), Some(v));
        assert_named_field(entry_body(&out), "tx_info");
    }
}

#[test]
fn sc_fields_head_resolves_under_ambiguity() {
    // Strict channel None (ambiguous V1/V2) with the SC channel at plan V2.
    let sc = VarId::new(71010);
    let out = run_with_sc_version(
        entry(sc, sc_fields_head_of(sc)),
        Some(ScriptVersion::PlutusV2),
    );
    assert_named_field(entry_body(&out), "tx_info");
}

#[test]
fn sc_fields_1_purpose_under_ambiguity() {
    // `.fields[1]` → `.purpose` even when V1-vs-V2 is unresolved (V1==V2 slot 1).
    let sc = VarId::new(71020);
    let out = run_with_sc_version(entry(sc, sc_field_of(sc, 1)), Some(ScriptVersion::PlutusV2));
    assert_named_field(entry_body(&out), "purpose");
}

#[test]
fn tx_info_fields_stay_positional_under_ambiguity() {
    // TxInfo `.fields[1]` MUST NOT be named under V1/V2 ambiguity (V1 arity 10
    // = reference_inputs absent; V2 arity 12 — the layouts diverge at index 1).
    let id = VarId::fresh_binding();
    let expr = tx_info_let(id, tx_info_field(id, 1));
    let out = run_with_sc_version(expr, Some(ScriptVersion::PlutusV2));
    // The tx_info alias body must remain a positional IndexAccess.
    let PseudoExpr::Let { body, .. } = &out else {
        panic!("expected tx_info let, got {out:?}");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::IndexAccess { index: 1, .. }),
        "TxInfo .fields[1] must stay positional under ambiguity, got {body:?}"
    );
}

#[test]
fn sc_fields_head_nested_helper_not_relabeled() {
    // The ListHead arm is VarId-gated on the entry param too: a non-entry
    // `script_context` keeps `.fields.head` positional.
    let entry_sc = VarId::new(71030);
    let helper_sc = VarId::new(71031);
    let out = run_with_version(
        entry(entry_sc, sc_fields_head_of(helper_sc)),
        Some(ScriptVersion::PlutusV3),
    );
    let body = entry_body(&out);
    // Still a `.head` over `.fields` (not relabeled to `.tx_info`).
    let PseudoExpr::FieldAccess { selector, .. } = body else {
        panic!("expected FieldAccess, got {body:?}");
    };
    assert!(
        matches!(selector, FieldSelector::ListHead),
        "non-entry .fields.head must stay positional, got {body:?}"
    );
}

#[test]
fn nested_sc_fields_2_fields_1_resolves_inner_only() {
    // script_context.fields[2].fields[1] → script_context.script_info.fields[1]
    let sc = VarId::new(70060);
    let body = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::field_access(sc_field_of(sc, 2), "fields")),
        index: 1,
    };
    let out = run_with_version(entry(sc, body), Some(ScriptVersion::PlutusV3));
    let PseudoExpr::IndexAccess { collection, index } = entry_body(&out) else {
        panic!("expected outer IndexAccess");
    };
    assert_eq!(*index, 1);
    let PseudoExpr::FieldAccess { record, selector } = collection.as_ref() else {
        panic!("expected `.fields` FieldAccess");
    };
    assert_eq!(selector.as_pretty_name(), "fields");
    assert_named_field(record, "script_info");
}
