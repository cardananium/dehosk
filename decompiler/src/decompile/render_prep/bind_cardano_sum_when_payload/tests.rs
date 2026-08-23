use super::*;
use crate::decompile::ScriptVersion;
use crate::pseudo::ast::PBox;
use crate::pseudo::constructor::ConstructorShape;

/// An explicit-V3 render context — the version the V3-only sums below
/// need; the ctx is a plain value, so no thread-local save/restore.
fn v3() -> RenderCtx {
    RenderCtx::at(Some(ScriptVersion::PlutusV3))
}

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}
fn field(record: PseudoExpr, name: &str) -> PseudoExpr {
    PseudoExpr::FieldAccess {
        record: PBox::new(record),
        selector: FieldSelector::NamedField(name.to_string()),
    }
}
fn index(coll: PseudoExpr, i: usize) -> PseudoExpr {
    PseudoExpr::IndexAccess {
        collection: PBox::new(coll),
        index: i,
    }
}
fn nullary_clause(tag: usize, body: PseudoExpr) -> WhenClause {
    WhenClause {
        pattern: WhenPattern::Constructor {
            type_hint: None,
            tag,
            fields: vec![],
            shape: ConstructorShape::unknown_data(tag, 0),
        },
        guard: None,
        body,
    }
}
fn fail_clause() -> WhenClause {
    WhenClause {
        pattern: WhenPattern::Wildcard,
        guard: None,
        body: PseudoExpr::Error { message: None },
    }
}
/// `when script_context.script_info is { Constr<5> -> <body>; _ -> fail }`.
fn script_info_when(body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(field(var("script_context", 1), "script_info")),
        subject_name: None,
        clauses: vec![nullary_clause(5, body), fail_clause()],
    }
}

/// V3 `Proposing` (arity 2): the nullary arm re-projecting `.fields[1]`
/// binds 2 fresh payload fields and rewrites the body to the 2nd binder.
#[test]
fn binds_proposing_payload_v3() {
    let subject = field(var("script_context", 1), "script_info");
    let body = index(field(subject, "fields"), 1);
    let out =
        bind_cardano_sum_when_payload(script_info_when(body), &CardanoTypeEnv::default(), &v3());
    let PseudoExpr::When { clauses, .. } = out else {
        panic!("When")
    };
    let WhenPattern::Constructor { fields, tag, .. } = &clauses[0].pattern else {
        panic!("ctor")
    };
    assert_eq!(*tag, 5);
    assert_eq!(fields.len(), 2, "Proposing payload (arity 2) bound");
    assert!(
        matches!(&clauses[0].body, PseudoExpr::Var { id: Some(id), .. } if *id == fields[1].id),
        "body `subject.fields[1]` rewritten to the 2nd bound field"
    );
}

/// Fail-closed: a body projecting `subject.fields[i]` with `i >= arity`
/// disproves the constructor — leave the `when` untouched.
#[test]
fn bails_on_out_of_range_projection() {
    let subject = field(var("script_context", 1), "script_info");
    let input = script_info_when(index(field(subject, "fields"), 5)); // 5 >= arity 2
    let out = bind_cardano_sum_when_payload(input.clone(), &CardanoTypeEnv::default(), &v3());
    assert_eq!(out, input, "out-of-range projection must bail");
}

/// A subject that does not resolve to a Cardano sum type is untouched.
#[test]
fn bails_on_non_cardano_subject() {
    let input = PseudoExpr::When {
        subject: PBox::new(var("foo", 1)),
        subject_name: None,
        clauses: vec![
            nullary_clause(5, index(field(var("foo", 1), "fields"), 1)),
            fail_clause(),
        ],
    };
    let out = bind_cardano_sum_when_payload(input.clone(), &CardanoTypeEnv::default(), &v3());
    assert_eq!(out, input, "non-Cardano subject must bail");
}
