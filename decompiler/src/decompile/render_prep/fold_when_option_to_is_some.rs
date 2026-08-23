//! Fold `when X is { Some(_) -> True; None -> False }` to
//! `option.is_some(X)` (and the dual to `option.is_none(X)`).
//!
//! V1 scripts emit Bool checks on `Option`-typed values as explicit
//! `when` matches; the stdlib says the same in one call. Either polarity
//! is recognised; a trailing wildcard is dropped because Some/None is
//! already exhaustive.
//!
//! Both arms must be plain `Bool(true)` / `Bool(false)` literals —
//! trace-wrapped or computed booleans aren't covered. Guarded arms are
//! rejected. The Some-arm's payload binder is not inspected; `Some(_) ->
//! Bool(true)` is the form that arises.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::fold::ExprFolder;

pub(super) fn fold_when_option_to_is_some(expr: PseudoExpr) -> PseudoExpr {
    rewrite(expr)
}

struct OptionIsSomeFolder;

impl ExprFolder for OptionIsSomeFolder {
    fn post_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        if let Some(call) = try_fold(&subject, &clauses) {
            return call;
        }
        PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name,
            clauses,
        }
    }

    fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
        pattern
    }
}

fn rewrite(expr: PseudoExpr) -> PseudoExpr {
    OptionIsSomeFolder.fold(expr)
}

fn try_fold(subject: &PseudoExpr, clauses: &[WhenClause]) -> Option<PseudoExpr> {
    // A trailing wildcard arm is dropped — Some/None is exhaustive.
    let mut some_body: Option<&PseudoExpr> = None;
    let mut none_body: Option<&PseudoExpr> = None;
    let mut wild_count = 0;
    for c in clauses {
        if c.guard.is_some() {
            return None;
        }
        match &c.pattern {
            WhenPattern::Constructor {
                shape: ConstructorShape::Known(KnownConstructor::Some),
                ..
            } => {
                some_body = Some(&c.body);
            }
            WhenPattern::Constructor {
                shape: ConstructorShape::Known(KnownConstructor::None),
                ..
            } => {
                none_body = Some(&c.body);
            }
            WhenPattern::Wildcard => {
                wild_count += 1;
            }
            _ => return None,
        }
    }
    if wild_count > 1 {
        return None;
    }
    let some_body = some_body?;
    let none_body = none_body?;
    let (some_b, none_b) = match (some_body, none_body) {
        (PseudoExpr::Bool(s), PseudoExpr::Bool(n)) => (*s, *n),
        _ => return None,
    };
    // stdlib module qualifiers are lowercase (`use option` →
    // `option.is_some`); the capitalized `Option` is the TYPE, not the module.
    // This Var name is render-terminal — no downstream pass keys off it.
    let fn_name = match (some_b, none_b) {
        (true, false) => "option.is_some",
        (false, true) => "option.is_none",
        _ => return None,
    };
    Some(PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: fn_name.to_string(),
            id: None,
        }),
        args: vec![subject.clone()].into(),
    })
}
