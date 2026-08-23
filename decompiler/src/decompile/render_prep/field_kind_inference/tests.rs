use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::ast::PBox;
use num_bigint::BigInt;

fn th(s: &str) -> TypeHintId {
    TypeHintId::from(s)
}

fn ctor(th: &TypeHintId, tag: usize, arity: usize, fields: Vec<PseudoExpr>) -> PseudoExpr {
    debug_assert_eq!(fields.len(), arity);
    PseudoExpr::Constr {
        tag,
        shape: ConstructorShape::unknown_data(tag, arity),
        fields: fields.into(),
        type_hint: Some(th.clone()),
    }
}

fn lam() -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![
            Binder::new("x", VarId::new(1)),
            Binder::new("y", VarId::new(2)),
        ],
        body: PBox::new(PseudoExpr::var_with_id("x", VarId::new(1))),
    }
}

fn un_b_data() -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnByteArray,
        args: vec![PseudoExpr::var_with_id("d", VarId::new(9))].into(),
    }
}

/// A field whose construction value is a nested 2-variant stub ctor → Scott.
#[test]
fn nested_stub_ctor_field_is_scott() {
    let inner = th("Unknown_S_25"); // [1,1] catalog from two decls below
    let outer = th("Unknown_S_6");
    let decl0 = ctor(&inner, 0, 1, vec![PseudoExpr::Unit]);
    let decl1 = ctor(&inner, 1, 1, vec![PseudoExpr::Unit]);
    let outer_val = ctor(
        &outer,
        0,
        1,
        vec![ctor(&inner, 0, 1, vec![PseudoExpr::Unit])],
    );
    let expr = PseudoExpr::Tuple((vec![decl0, decl1, outer_val]).into());
    let table = infer_field_kinds(&expr);
    assert_eq!(
        table.get(&(outer.clone(), 0, 0)),
        Some(&FieldKind::Scott(vec![1, 1]))
    );
}

/// A field whose construction value is a Lambda → Fn.
#[test]
fn lambda_field_is_fn() {
    let outer = th("Unknown_S_30");
    let expr = ctor(&outer, 0, 1, vec![lam()]);
    let table = infer_field_kinds(&expr);
    assert_eq!(table.get(&(outer.clone(), 0, 0)), Some(&FieldKind::Fn));
}

/// A field whose construction value is `un_b_data(..)` → Native.
#[test]
fn data_builtin_field_is_native() {
    let outer = th("Unknown_S_1");
    let expr = ctor(&outer, 0, 1, vec![un_b_data()]);
    let table = infer_field_kinds(&expr);
    assert_eq!(table.get(&(outer.clone(), 0, 0)), Some(&FieldKind::Native));
}

/// Two disagreeing construction sites for the same key → Conflict.
#[test]
fn disagreeing_sites_conflict() {
    let outer = th("Unknown_S_9");
    let site_a = ctor(&outer, 0, 1, vec![lam()]); // Fn
    let site_b = ctor(&outer, 0, 1, vec![un_b_data()]); // Native
    let expr = PseudoExpr::Tuple((vec![site_a, site_b]).into());
    let table = infer_field_kinds(&expr);
    assert_eq!(
        table.get(&(outer.clone(), 0, 0)),
        Some(&FieldKind::Conflict)
    );
}

/// A bare-Var construction site is observed-but-unprovable → Opaque
/// (recorded, NOT absent — so it fails the key closed against Scott).
#[test]
fn bare_var_field_is_opaque() {
    let outer = th("Unknown_S_4");
    let expr = ctor(
        &outer,
        0,
        1,
        vec![PseudoExpr::var_with_id("v", VarId::new(7))],
    );
    let table = infer_field_kinds(&expr);
    assert_eq!(table.get(&(outer.clone(), 0, 0)), Some(&FieldKind::Opaque));
}

/// FAIL-CLOSED: one Scott site + one bare-Var site for the same key must
/// NOT yield Scott — the unprovable site forces Conflict.
#[test]
fn scott_plus_opaque_site_is_conflict() {
    let inner = th("Unknown_S_25");
    let outer = th("Unknown_S_7");
    let decl0 = ctor(&inner, 0, 1, vec![PseudoExpr::Unit]);
    let decl1 = ctor(&inner, 1, 1, vec![PseudoExpr::Unit]);
    let scott_site = ctor(
        &outer,
        0,
        1,
        vec![ctor(&inner, 0, 1, vec![PseudoExpr::Unit])],
    );
    let opaque_site = ctor(
        &outer,
        0,
        1,
        vec![PseudoExpr::var_with_id("v", VarId::new(3))],
    );
    let expr = PseudoExpr::Tuple((vec![decl0, decl1, scott_site, opaque_site]).into());
    let table = infer_field_kinds(&expr);
    assert_eq!(
        table.get(&(outer.clone(), 0, 0)),
        Some(&FieldKind::Conflict)
    );
}

/// FENCE: a non-stub (user/blueprint) outer hint defines NO keys, even with
/// a perfectly Scott-looking nested-stub field.
#[test]
fn non_stub_outer_hint_absent() {
    let inner = th("Unknown_S_25");
    let user = th("MyUserType");
    let decl0 = ctor(&inner, 0, 1, vec![PseudoExpr::Unit]);
    let decl1 = ctor(&inner, 1, 1, vec![PseudoExpr::Unit]);
    let user_val = ctor(
        &user,
        0,
        1,
        vec![ctor(&inner, 0, 1, vec![PseudoExpr::Unit])],
    );
    let expr = PseudoExpr::Tuple((vec![decl0, decl1, user_val]).into());
    let table = infer_field_kinds(&expr);
    assert_eq!(table.get(&(user.clone(), 0, 0)), None);
}

/// FENCE: a nested NON-stub ctor field is data, not Scott → Opaque.
#[test]
fn nested_non_stub_field_is_opaque() {
    let inner = th("MyUserType"); // 2 variants, but not a stub
    let outer = th("Unknown_S_11");
    let decl0 = ctor(&inner, 0, 1, vec![PseudoExpr::Unit]);
    let decl1 = ctor(&inner, 1, 1, vec![PseudoExpr::Unit]);
    let outer_val = ctor(
        &outer,
        0,
        1,
        vec![ctor(&inner, 0, 1, vec![PseudoExpr::Unit])],
    );
    let expr = PseudoExpr::Tuple((vec![decl0, decl1, outer_val]).into());
    let table = infer_field_kinds(&expr);
    assert_eq!(table.get(&(outer.clone(), 0, 0)), Some(&FieldKind::Opaque));
}

/// A 1-variant nested stub ctor is a record, not an eliminator → Opaque.
#[test]
fn single_variant_nested_is_opaque() {
    let inner = th("Unknown_S_Rec"); // only tag 0 declared
    let outer = th("Unknown_S_8");
    let expr = PseudoExpr::Tuple(
        vec![
            ctor(
                &inner,
                0,
                2,
                vec![PseudoExpr::Int(BigInt::from(1)), PseudoExpr::Unit],
            ),
            ctor(
                &outer,
                0,
                1,
                vec![ctor(&inner, 0, 2, vec![PseudoExpr::Unit, PseudoExpr::Unit])],
            ),
        ]
        .into(),
    );
    let table = infer_field_kinds(&expr);
    // inner has only 1 variant → arities.len() < 2 → not Scott → Opaque.
    assert_eq!(table.get(&(outer.clone(), 0, 0)), Some(&FieldKind::Opaque));
}

/// A prefix-sharing user type with a NON-numeric suffix is not a stub.
#[test]
fn non_numeric_suffix_is_not_stub() {
    assert!(is_stub_hint(&th("Unknown_S_6")));
    assert!(is_stub_hint(&th("Unknown_S_6_A2"))); // shard form
    assert!(is_stub_hint(&th("Unknown_E_3")));
    assert!(!is_stub_hint(&th("Unknown_S_Foo")));
    assert!(!is_stub_hint(&th("Unknown_Something")));
    assert!(!is_stub_hint(&th("MyUserType")));
}

/// Arity disagreement on the inner type's variant → uncertain → not Scott.
#[test]
fn conflicting_inner_arity_blocks_scott() {
    let inner = th("Unknown_S_25");
    let outer = th("Unknown_S_12");
    // tag 0 declared with arity 1 AND arity 2 → uncertain.
    let decl0a = ctor(&inner, 0, 1, vec![PseudoExpr::Unit]);
    let decl0b = ctor(&inner, 0, 2, vec![PseudoExpr::Unit, PseudoExpr::Unit]);
    let decl1 = ctor(&inner, 1, 1, vec![PseudoExpr::Unit]);
    let outer_val = ctor(
        &outer,
        0,
        1,
        vec![ctor(&inner, 0, 1, vec![PseudoExpr::Unit])],
    );
    let expr = PseudoExpr::Tuple((vec![decl0a, decl0b, decl1, outer_val]).into());
    let table = infer_field_kinds(&expr);
    // arities_for_hint returns None (tag 0 uncertain) → Opaque, not Scott.
    assert_eq!(table.get(&(outer.clone(), 0, 0)), Some(&FieldKind::Opaque));
}

// -- ScalarKind (elimination-site analysis) -----------------------------

use crate::pseudo::ast::{WhenClause, WhenPattern};

/// A stub-typed `when` arm binding a single field binder `vid`, whose body
/// is `body`. (`tag`/`field_idx` default to 0.)
fn stub_arm_when(hint: &TypeHintId, vid: VarId, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("subj", VarId::new(100))),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::constructor_with_hint(
                ConstructorShape::unknown_data(0, 1),
                vec![Binder::new("f0", vid)],
                Some(hint.clone()),
            ),
            body,
        )],
    }
}

fn un_b_of(vid: VarId) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnByteArray,
        args: vec![PseudoExpr::var_with_id("f0", vid)].into(),
    }
}

fn un_i_of(vid: VarId) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnInt,
        args: vec![PseudoExpr::var_with_id("f0", vid)].into(),
    }
}

/// `un_b_data(field)` in the arm body → ByteArray.
#[test]
fn scalar_un_b_data_site_is_bytearray() {
    let hint = th("Unknown_S_40");
    let vid = VarId::new(201);
    let expr = stub_arm_when(&hint, vid, un_b_of(vid));
    let table = infer_arm_field_scalars(&expr);
    assert_eq!(
        table.get(&(hint.clone(), 0, 0)),
        Some(&ScalarKind::ByteArray)
    );
}

/// `un_i_data(field)` in the arm body → Int.
#[test]
fn scalar_un_i_data_site_is_int() {
    let hint = th("Unknown_S_41");
    let vid = VarId::new(202);
    let expr = stub_arm_when(&hint, vid, un_i_of(vid));
    let table = infer_arm_field_scalars(&expr);
    assert_eq!(table.get(&(hint.clone(), 0, 0)), Some(&ScalarKind::Int));
}

/// `un_list_data(field)` → OtherData.
#[test]
fn scalar_un_list_data_site_is_other_data() {
    let hint = th("Unknown_S_42");
    let vid = VarId::new(203);
    let body = PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnList,
        args: vec![PseudoExpr::var_with_id("f0", vid)].into(),
    };
    let expr = stub_arm_when(&hint, vid, body);
    let table = infer_arm_field_scalars(&expr);
    assert_eq!(
        table.get(&(hint.clone(), 0, 0)),
        Some(&ScalarKind::OtherData)
    );
}

/// SAME key decoded BOTH as un_b_data AND un_i_data → Conflict.
#[test]
fn scalar_bytearray_and_int_same_key_conflict() {
    let hint = th("Unknown_S_43");
    let vid = VarId::new(204);
    let body = PseudoExpr::Tuple((vec![un_b_of(vid), un_i_of(vid)]).into());
    let expr = stub_arm_when(&hint, vid, body);
    let table = infer_arm_field_scalars(&expr);
    assert_eq!(
        table.get(&(hint.clone(), 0, 0)),
        Some(&ScalarKind::Conflict)
    );
}

/// A stub field passed into ANOTHER stub-typed constructor position →
/// Opaque (flowed into a stub, not decoded as a scalar).
#[test]
fn scalar_field_into_stub_ctor_is_opaque() {
    let hint = th("Unknown_S_44");
    let other = th("Unknown_S_99");
    let vid = VarId::new(205);
    let body = ctor(&other, 0, 1, vec![PseudoExpr::var_with_id("f0", vid)]);
    let expr = stub_arm_when(&hint, vid, body);
    let table = infer_arm_field_scalars(&expr);
    assert_eq!(table.get(&(hint.clone(), 0, 0)), Some(&ScalarKind::Opaque));
}

/// A stub field matched as a stub (subject of a stub `when`) + ALSO
/// decoded once as un_b_data → the Opaque use defeats ByteArray → Conflict.
#[test]
fn scalar_field_into_stub_match_plus_bytes_is_conflict() {
    let hint = th("Unknown_S_45");
    let inner_hint = th("Unknown_S_98");
    let vid = VarId::new(206);
    // Inner stub `when` on `field` (Opaque use) ...
    let inner_when = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("f0", vid)),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::constructor_with_hint(
                ConstructorShape::unknown_data(0, 0),
                vec![],
                Some(inner_hint.clone()),
            ),
            PseudoExpr::Unit,
        )],
    };
    // ... AND a un_b_data(field) site (ByteArray use).
    let body = PseudoExpr::Tuple((vec![inner_when, un_b_of(vid)]).into());
    let expr = stub_arm_when(&hint, vid, body);
    let table = infer_arm_field_scalars(&expr);
    assert_eq!(
        table.get(&(hint.clone(), 0, 0)),
        Some(&ScalarKind::Conflict)
    );
}

/// A tracked field with NO decode/use site fails CLOSED to Opaque
/// (present in the table, never silently assumed a scalar).
#[test]
fn scalar_unused_field_defaults_opaque() {
    let hint = th("Unknown_S_46");
    let vid = VarId::new(207);
    // Body never mentions the field.
    let expr = stub_arm_when(&hint, vid, PseudoExpr::Unit);
    let table = infer_arm_field_scalars(&expr);
    assert_eq!(table.get(&(hint.clone(), 0, 0)), Some(&ScalarKind::Opaque));
}

/// Merged-stub conflation at the classifier level: two SEPARATE `when`
/// sites of the SAME merged stub `TypeHintId`+tag, one decoding its field
/// with `un_b_data` (ByteArray), the other passing its field into a helper
/// `Apply` (unrecognized ⇒ never `observed` ⇒ `Opaque`). Both binders share
/// the key `(hint, 0, 0)`, so the join is `Conflict` — the Credential gate
/// must not read a conflated merged stub as a uniform `ByteArray`.
#[test]
fn scalar_merged_stub_bytes_plus_helper_call_is_conflict() {
    let hint = th("Unknown_S_1");
    let v_bytes = VarId::new(401); // un_b_data(field) — ByteArray
    let v_call = VarId::new(402); // extract_int(field) — Apply, unrecognized
    // Site A: `when subjA is { Unknown_S_1_0(f0) -> un_b_data(f0) }`.
    let site_a = stub_arm_when(&hint, v_bytes, un_b_of(v_bytes));
    // Site B: `when subjB is { Unknown_S_1_0(f0) -> extract_int(f0) }`.
    // The field flows into an unclassified `Apply`, so the binder is
    // never observed and contributes the per-binder Opaque default.
    let helper_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("extract_int", VarId::new(500))),
        args: vec![PseudoExpr::var_with_id("f0", v_call)].into(),
    };
    let site_b = stub_arm_when(&hint, v_call, helper_call);
    let expr = PseudoExpr::Tuple((vec![site_a, site_b]).into());
    let table = infer_arm_field_scalars(&expr);
    assert_eq!(
        table.get(&(hint.clone(), 0, 0)),
        Some(&ScalarKind::Conflict),
        "a merged-stub field decoded ByteArray at one site and passed into a \
         helper (unobserved → Opaque) at another must join to Conflict"
    );
}

/// Control for the conflation test: two SEPARATE `when` sites of the SAME
/// merged stub `TypeHintId`+tag, BOTH decoding `un_b_data` ⇒ a uniform
/// `ByteArray` — the per-binder Opaque default must not taint it.
#[test]
fn scalar_merged_stub_both_bytes_is_bytearray() {
    let hint = th("Unknown_S_1");
    let v1 = VarId::new(411);
    let v2 = VarId::new(412);
    let site_a = stub_arm_when(&hint, v1, un_b_of(v1));
    let site_b = stub_arm_when(&hint, v2, un_b_of(v2));
    let expr = PseudoExpr::Tuple((vec![site_a, site_b]).into());
    let table = infer_arm_field_scalars(&expr);
    assert_eq!(
        table.get(&(hint.clone(), 0, 0)),
        Some(&ScalarKind::ByteArray),
        "two un_b_data sites of the same merged-stub key stay uniformly ByteArray"
    );
}

/// SITE-COMPLETENESS: a SINGLE binder used BOTH as `un_b_data(f)`
/// (ByteArray) AND as a helper-call arg `extract_int(f)` (an `Apply` — an
/// unrecognized flow ⇒ Opaque) in the SAME arm body must join to
/// `Conflict`. An observed scalar decode must NOT let a later unrecognized
/// use of the same binder evade the conflation verdict.
#[test]
fn scalar_same_binder_bytes_and_helper_call_is_conflict() {
    let hint = th("Unknown_S_50");
    let vid = VarId::new(301);
    // body: (un_b_data(f0), extract_int(f0)) — f0 decoded as bytes AND
    // passed into an opaque helper `Apply`.
    let helper_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("extract_int", VarId::new(399))),
        args: vec![PseudoExpr::var_with_id("f0", vid)].into(),
    };
    let body = PseudoExpr::Tuple((vec![un_b_of(vid), helper_call]).into());
    let expr = stub_arm_when(&hint, vid, body);
    let table = infer_arm_field_scalars(&expr);
    assert_eq!(
        table.get(&(hint.clone(), 0, 0)),
        Some(&ScalarKind::Conflict),
        "un_b_data(f) ByteArray + extract_int(f) Opaque on the same binder ⇒ Conflict"
    );
}

/// A NON-stub (user) outer hint contributes NO tracked binders → its
/// pattern fields are absent from the scalar table.
#[test]
fn scalar_non_stub_arm_absent() {
    let user = th("MyUserType");
    let vid = VarId::new(208);
    let expr = stub_arm_when(&user, vid, un_b_of(vid));
    let table = infer_arm_field_scalars(&expr);
    assert_eq!(table.get(&(user.clone(), 0, 0)), None);
}

/// ScalarKind lattice: peers conflict, Unknown is identity, equal is idem.
#[test]
fn scalar_kind_join_lattice() {
    use ScalarKind::*;
    assert_eq!(Unknown.join(Int), Int);
    assert_eq!(Int.join(Unknown), Int);
    assert_eq!(Int.join(Int), Int);
    assert_eq!(ByteArray.join(Int), Conflict);
    assert_eq!(Int.join(ByteArray), Conflict);
    assert_eq!(Opaque.join(ByteArray), Conflict);
    assert_eq!(Conflict.join(Unknown), Conflict);
    assert_eq!(OtherData.join(OtherData), OtherData);
}
