use super::*;
use crate::decompile::render_prep::RenderCtx;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;

fn id(n: u32) -> VarId {
    VarId::new(n)
}

/// `when purpose is { Constr<tag>(payload) -> body }` — a Purpose
/// dispatch.
fn when_purpose(tag: usize, payload: (&str, VarId), body: PseudoExpr) -> PseudoExpr {
    let payload_binder = Binder::new(payload.0, payload.1);
    PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("purpose", id(900))),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag,
                shape: ConstructorShape::from_name_and_tag(None, tag, 1),
                fields: vec![payload_binder],
            },
            guard: None,
            body,
        }],
    }
}

/// `when tx_info is { TxInfo(inputs, …, certificates, …) -> body }` — the
/// canonical arity-10 V1 TxInfo destructure, which satisfies the bridge's
/// defensive arity gate (10 or 12).
fn when_tx_info_certificates(cert_id: VarId, body: PseudoExpr) -> PseudoExpr {
    let names = [
        "inputs",
        "outputs",
        "fee",
        "mint",
        "certificates",
        "withdrawals",
        "valid_range",
        "signatories",
        "datums",
        "id",
    ];
    let fields: Vec<Binder> = names
        .iter()
        .enumerate()
        .map(|(i, n)| {
            if *n == "certificates" {
                Binder::new("certificates", cert_id)
            } else {
                Binder::new(*n, id(810 + i as u32))
            }
        })
        .collect();
    PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("tx_info", id(800))),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                shape: ConstructorShape::from_name_and_tag(None, 0, 10),
                fields,
            },
            guard: None,
            body,
        }],
    }
}

fn un_list_data(arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnList,
        args: vec![arg].into(),
    }
}

fn list_tail(arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::ListTail,
        args: vec![arg].into(),
    }
}

fn list_head(record: PseudoExpr) -> PseudoExpr {
    PseudoExpr::field_access_typed(record, FieldSelector::ListHead)
}

/// `let <fn_name> = fn(<param>) { <body> } in <rest>` — a non-rec helper.
fn let_helper(
    fn_name: &str,
    fn_id: VarId,
    param: (&str, VarId),
    body: PseudoExpr,
    rest: PseudoExpr,
) -> PseudoExpr {
    PseudoExpr::let_bind_with_id(
        fn_name,
        fn_id,
        PseudoExpr::lambda_with_binders(vec![Binder::new(param.0, param.1)], body),
        rest,
    )
}

fn call(fn_name: &str, fn_id: VarId, arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::apply(PseudoExpr::var_with_id(fn_name, fn_id), vec![arg])
}

/// Run the bridge under an explicit V1 render version.
fn run_v1(expr: PseudoExpr) -> PseudoExpr {
    schema_param_provenance(expr, &RenderCtx::at(Some(ScriptVersion::PlutusV1)))
}

/// The display name of the FIRST param of the let-bound helper named `fn_name`.
fn helper_param_name(expr: &PseudoExpr, fn_name: &str) -> Option<String> {
    fn walk(e: &PseudoExpr, fn_name: &str) -> Option<String> {
        if let PseudoExpr::Let { name, value, .. } = e
            && name == fn_name
            && let PseudoExpr::Lambda { params, .. } = value.as_ref()
        {
            return params.first().map(|p| p.as_str().to_string());
        }
        for c in children(e) {
            if let Some(found) = walk(c, fn_name) {
                return Some(found);
            }
        }
        None
    }
    walk(expr, fn_name)
}

#[test]
fn bridges_param_fed_only_certifying_payloads() {
    // let extract = fn(x_40) { x_40 } in
    //   when purpose is { Certifying(field_0) -> extract(field_0) }
    let body = when_purpose(
        PURPOSE_CERTIFYING_TAG,
        ("field_0", id(10)),
        call("extract", id(1), PseudoExpr::var_with_id("field_0", id(10))),
    );
    let expr = let_helper(
        "extract",
        id(1),
        ("x_40", id(2)),
        PseudoExpr::var_with_id("x_40", id(2)),
        body,
    );
    let out = run_v1(expr);
    assert_eq!(
        helper_param_name(&out, "extract").as_deref(),
        Some("certificate"),
        "param fed only Certifying payloads must be bridged to `certificate`"
    );
}

#[test]
fn bridges_param_fed_certificates_list_head() {
    // when tx_info is { TxInfo(certificates) ->
    //   let extract = fn(x_40) { x_40 } in
    //   let step = rec fn step(v) { extract(v.head) ... step(tail_list(v)) } in
    //   step(un_list_data(certificates))
    // }
    let extract_call = call(
        "extract",
        id(1),
        list_head(PseudoExpr::var_with_id("v", id(20))),
    );
    let recursive_call = call(
        "step",
        id(30),
        list_tail(PseudoExpr::var_with_id("v", id(20))),
    );
    // rec-fn body: a Pair so both the head extraction and the recursion appear.
    let rec_body = PseudoExpr::Pair(PBox::new(extract_call), PBox::new(recursive_call));
    let step_fn = PseudoExpr::RecFn {
        name: Binder::new("step", id(30)),
        params: vec![Binder::new("v", id(20))],
        body: PBox::new(rec_body),
    };
    let inner = PseudoExpr::let_bind_with_id(
        "step",
        id(31),
        step_fn,
        call(
            "step",
            id(31),
            un_list_data(PseudoExpr::var_with_id("certificates", id(50))),
        ),
    );
    let extract_def = let_helper(
        "extract",
        id(1),
        ("x_40", id(2)),
        PseudoExpr::var_with_id("x_40", id(2)),
        inner,
    );
    let expr = when_tx_info_certificates(id(50), extract_def);
    let out = run_v1(expr);
    assert_eq!(
        helper_param_name(&out, "extract").as_deref(),
        Some("certificate"),
        "param fed only certificates-list-head elements must be bridged"
    );
}

#[test]
fn fail_closed_when_used_as_value() {
    // let extract = fn(x_40) { x_40 } in
    //   let alias = extract in              <- value-use of `extract`
    //   when purpose is { Certifying(field_0) -> extract(field_0) }
    let cert_call = when_purpose(
        PURPOSE_CERTIFYING_TAG,
        ("field_0", id(10)),
        call("extract", id(1), PseudoExpr::var_with_id("field_0", id(10))),
    );
    let value_use = PseudoExpr::let_bind_with_id(
        "alias",
        id(99),
        PseudoExpr::var_with_id("extract", id(1)), // <- bare value-use
        cert_call,
    );
    let expr = let_helper(
        "extract",
        id(1),
        ("x_40", id(2)),
        PseudoExpr::var_with_id("x_40", id(2)),
        value_use,
    );
    let out = run_v1(expr);
    assert_eq!(
        helper_param_name(&out, "extract").as_deref(),
        Some("x_40"),
        "a function used as a value must NOT be bridged (fail-closed)"
    );
}

#[test]
fn fail_closed_when_one_site_feeds_non_cert() {
    // let extract = fn(x_40) { x_40 } in
    //   let x = when purpose is { Certifying(field_0) -> extract(field_0) } in  (cert site)
    //   extract(some_other)                                                      (NON-cert site)
    let cert_site = when_purpose(
        PURPOSE_CERTIFYING_TAG,
        ("field_0", id(10)),
        call("extract", id(1), PseudoExpr::var_with_id("field_0", id(10))),
    );
    let non_cert_site = call(
        "extract",
        id(1),
        PseudoExpr::var_with_id("some_other", id(77)),
    );
    let chained = PseudoExpr::let_bind_with_id("x", id(88), cert_site, non_cert_site);
    let expr = let_helper(
        "extract",
        id(1),
        ("x_40", id(2)),
        PseudoExpr::var_with_id("x_40", id(2)),
        chained,
    );
    let out = run_v1(expr);
    assert_eq!(
        helper_param_name(&out, "extract").as_deref(),
        Some("x_40"),
        "a function fed a non-cert arg at one site must NOT be bridged (fail-closed)"
    );
}

#[test]
fn no_op_without_explicit_v1_v2_version() {
    // Same enumerable all-cert shape as the positive test, but no render
    // version set ⇒ the version gate must keep the pass inert.
    let body = when_purpose(
        PURPOSE_CERTIFYING_TAG,
        ("field_0", id(10)),
        call("extract", id(1), PseudoExpr::var_with_id("field_0", id(10))),
    );
    let expr = let_helper(
        "extract",
        id(1),
        ("x_40", id(2)),
        PseudoExpr::var_with_id("x_40", id(2)),
        body,
    );
    let out = schema_param_provenance(expr, &RenderCtx::at(None));
    assert_eq!(
        helper_param_name(&out, "extract").as_deref(),
        Some("x_40"),
        "version-less render must leave the param untouched"
    );
}

#[test]
fn fail_closed_when_no_call_sites() {
    // A helper that is never called must not be bridged (no evidence).
    let expr = let_helper(
        "extract",
        id(1),
        ("x_40", id(2)),
        PseudoExpr::var_with_id("x_40", id(2)),
        PseudoExpr::var_with_id("unit", id(60)),
    );
    let out = run_v1(expr);
    assert_eq!(
        helper_param_name(&out, "extract").as_deref(),
        Some("x_40"),
        "a never-called helper must NOT be bridged"
    );
}
