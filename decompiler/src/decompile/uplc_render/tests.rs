use super::*;
use std::rc::Rc;
use uplc::ast::{Name, Program, Term};

fn name(text: &str) -> Name {
    Name {
        text: text.to_string(),
        unique: 0.into(),
    }
}
fn var(text: &str) -> Term<Name> {
    Term::Var {
        name: Rc::new(name(text)),
        uniq_id: 0,
    }
}
fn app(f: Term<Name>, x: Term<Name>) -> Term<Name> {
    Term::Apply {
        function: Rc::new(f),
        argument: Rc::new(x),
        uniq_id: 0,
    }
}

fn prog(term: Term<Name>) -> Program<Name> {
    Program {
        version: (1, 0, 0),
        term,
    }
}

#[test]
fn apply_spine_is_flattened() {
    // ((f a) b) c  → `[f a b c]`, NOT `[[[f a] b] c]`.
    let term = app(app(app(var("f"), var("a")), var("b")), var("c"));
    let out = render_program_flattened(&prog(term));
    assert!(
        out.contains("[f a b c]"),
        "expected flattened spine, got:\n{out}"
    );
    assert!(
        !out.contains("[["),
        "no binary nesting should remain, got:\n{out}"
    );
}

#[test]
fn lambda_compact_when_it_fits() {
    // (lam x x)
    let term = Term::Lambda {
        parameter_name: Rc::new(name("x")),
        body: Rc::new(var("x")),
        uniq_id: 0,
    };
    let out = render_program_flattened(&prog(term));
    assert!(
        out.contains("(lam x x)"),
        "expected compact lambda, got:\n{out}"
    );
}

#[test]
fn spine_breaks_across_lines_when_too_long() {
    // A spine wider than WIDTH must break — each arg on its own line, but
    // still semantically `[head a1 …]` (no binary nesting reintroduced).
    let long = "averyverylongvariablenamethatexceedstheprettywidthlimit";
    let term = app(app(var(long), var(long)), var(long));
    let out = render_program_flattened(&prog(term));
    assert!(
        out.contains('\n'),
        "expected a multi-line break, got:\n{out}"
    );
    assert!(
        !out.contains("[["),
        "must not reintroduce binary nesting, got:\n{out}"
    );
}
