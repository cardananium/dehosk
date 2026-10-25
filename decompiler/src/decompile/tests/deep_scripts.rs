//! Deep scripts decompile on a small call stack.
//!
//! A script nests as deep as its author likes — 32 KiB of flat holds ~65,000
//! levels of `delay` — and in the browser the decompiler runs on a call stack
//! that cannot grow. So every walk over a tree must cost stack independent of
//! its depth. These programs are each nested a few thousand levels deep in one
//! way a script can nest, and each is decompiled, in every output layer, on a
//! thread whose stack would overflow long before that if any walk recursed
//! once per level.

use std::rc::Rc;

use uplc::ast::{Constant, Data, DeBruijn, Program, Term, Type};
use uplc::builtins::DefaultFunction;

use crate::decompile::{DecompileOptions, OutputLayer, decompile};

type T = Term<DeBruijn>;

/// Deep enough that a frame per level overflows `STACK`.
const DEPTH: usize = 2_000;
/// The stack each decompile gets: 256 bytes a level, less than any
/// recursive walk's frame.
const STACK: usize = 512 * 1024;

fn var(i: usize) -> T {
    Term::Var {
        name: Rc::new(DeBruijn::new(i)),
        uniq_id: 0,
    }
}
fn lam(body: T) -> T {
    Term::Lambda {
        parameter_name: Rc::new(DeBruijn::new(0)),
        body: Rc::new(body),
        uniq_id: 0,
    }
}
fn app(f: T, a: T) -> T {
    Term::Apply {
        function: Rc::new(f),
        argument: Rc::new(a),
        uniq_id: 0,
    }
}
fn con(c: Constant) -> T {
    Term::Constant {
        value: Rc::new(c),
        uniq_id: 0,
    }
}
fn unit() -> T {
    con(Constant::Unit)
}
fn builtin(f: DefaultFunction) -> T {
    Term::Builtin { fun: f, uniq_id: 0 }
}
fn force(t: T) -> T {
    Term::Force {
        body: Rc::new(t),
        uniq_id: 0,
    }
}
fn delay(t: T) -> T {
    Term::Delay {
        body: Rc::new(t),
        uniq_id: 0,
    }
}
fn constr(fields: Vec<T>) -> T {
    Term::Constr {
        tag: 0,
        fields,
        uniq_id: 0,
    }
}
fn case(s: T, branches: Vec<T>) -> T {
    Term::Case {
        constr: Rc::new(s),
        branches,
        uniq_id: 0,
    }
}

/// One program per way of nesting, `DEPTH` levels deep.
fn deep_programs() -> Vec<(&'static str, T)> {
    let n = DEPTH;
    let chain = |seed: T, wrap: &dyn Fn(T) -> T| (0..n).fold(seed, |t, _| wrap(t));
    let if_then_else = |c: T, then: T, otherwise: T| {
        force(app(
            app(
                app(force(builtin(DefaultFunction::IfThenElse)), c),
                delay(then),
            ),
            delay(otherwise),
        ))
    };
    let data = (0..n).fold(Data::integer(0.into()), |d, _| Data::list(vec![d]));
    let mut list_type = Rc::new(Type::Integer);
    let mut list = Constant::Integer(1.into());
    for _ in 0..n {
        list = Constant::ProtoList((*list_type).clone(), vec![Rc::new(list)]);
        list_type = Rc::new(Type::List(list_type));
    }
    vec![
        ("delays", chain(unit(), &delay)),
        ("lambdas", lam(chain(var(1), &lam))),
        ("apply argument", chain(unit(), &|t| app(lam(var(1)), t))),
        ("apply function", chain(lam(unit()), &|t| app(t, unit()))),
        (
            "closure chain",
            chain(unit(), &|t| app(lam(lam(var(2))), t)),
        ),
        (
            "let chain, each binding used twice",
            lam(chain(var(1), &|t| {
                app(
                    lam(t),
                    app(app(builtin(DefaultFunction::AddInteger), var(1)), var(1)),
                )
            })),
        ),
        ("constructor field", chain(unit(), &|t| constr(vec![t]))),
        (
            "constructor field on a parameter",
            lam(chain(var(1), &|t| constr(vec![var(1), t]))),
        ),
        (
            "case in branch",
            lam(chain(unit(), &|t| case(var(1), vec![t]))),
        ),
        (
            "case in scrutinee",
            lam(chain(var(1), &|t| case(t, vec![var(1)]))),
        ),
        (
            "else-if ladder",
            lam(chain(unit(), &|t| if_then_else(var(1), unit(), t))),
        ),
        (
            "arithmetic",
            lam(chain(var(1), &|t| {
                app(app(builtin(DefaultFunction::AddInteger), t), var(1))
            })),
        ),
        (
            "traces",
            chain(unit(), &|t| {
                app(
                    app(
                        force(builtin(DefaultFunction::Trace)),
                        con(Constant::String("x".into())),
                    ),
                    t,
                )
            }),
        ),
        (
            "parameter applied to itself",
            lam(chain(var(1), &|t| app(var(1), t))),
        ),
        ("Data list", con(Constant::Data(data))),
        ("list of lists", con(list)),
    ]
}

#[test]
fn deep_scripts_decompile_on_a_small_stack() {
    // Lowering alone, the whole pipeline and render, and the UPLC echo.
    let layers = [
        OutputLayer::RawPseudo,
        OutputLayer::Decompiled,
        OutputLayer::Uplc,
    ];
    for (shape, term) in deep_programs() {
        let hex = hex::encode(
            Program {
                version: (1, 1, 0),
                term,
            }
            .to_cbor()
            .expect("encodes"),
        );
        for layer in layers {
            let hex = hex.clone();
            let result = std::thread::Builder::new()
                .stack_size(STACK)
                .spawn(move || {
                    let options = DecompileOptions {
                        output_layer: layer,
                        ..Default::default()
                    };
                    decompile(&hex, options)
                })
                .expect("spawns")
                .join()
                .unwrap_or_else(|_| panic!("{shape} panicked in {layer:?}"));
            let output = result.unwrap_or_else(|e| panic!("{shape} failed in {layer:?}: {e}"));
            assert!(!output.is_empty(), "{shape}: empty output in {layer:?}");
        }
    }
}

/// A `when` nested in its clause body, 100,000 deep, released on a small
/// stack: clause bodies sit inline in the clauses, not behind a box, so this
/// is the container's destructor at work.
#[test]
fn a_deep_when_chain_drops_on_a_small_stack() {
    use crate::pseudo::ast::{PBox, PseudoExpr, WhenClause, WhenPattern};
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut expr = PseudoExpr::Unit;
            for _ in 0..100_000 {
                expr = PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::Unit),
                    subject_name: None,
                    clauses: vec![WhenClause {
                        pattern: WhenPattern::Wildcard,
                        guard: None,
                        body: expr,
                    }]
                    .into(),
                };
            }
            drop(expr);
        })
        .expect("spawns")
        .join()
        .expect("dropped without overflowing");
}
