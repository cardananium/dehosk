//! Downgrade prelude `KnownConstructor` variants to
//! `ConstructorShape::unknown_data(tag, arity)` so the renderer
//! emits raw `Constr<N>` instead of the prelude constructor
//! name: `True`/`False`, `Some`/`None`, `Ok`/`Error`, `Pair`,
//! `Nil`/`Cons`, `Less`/`Equal`/`Greater`, `Void`.
//!
//! Runs before render when
//! `DecompileOptions::recognize_prelude_constructors` is `false`,
//! to show the underlying UPLC structure or paste into
//! pre-prelude contexts.
//!
//! Cardano-domain variants (`Mint`, `Spend`, `Withdraw`,
//! `Publish`, `Vote`, `Propose`) stay recognized because
//! `validator_shape::detect_dispatch` relies on the Known anchor
//! to identify multi-purpose dispatches.

use crate::pseudo::ast::{PseudoExpr, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::fold::ExprFolder;

/// Downgrade non-purpose prelude constructors, plus `Bool`/`Unit`
/// leaves, to `Unknown { tag, arity }` throughout the AST.
pub(crate) fn downgrade_prelude_constructors(expr: PseudoExpr) -> PseudoExpr {
    walk(expr)
}

fn should_downgrade(known: KnownConstructor) -> bool {
    // Cardano purpose constructors stay Known — purpose-dispatch
    // detection needs them as anchors.
    !matches!(
        known,
        KnownConstructor::Mint
            | KnownConstructor::Spend
            | KnownConstructor::Withdraw
            | KnownConstructor::Publish
            | KnownConstructor::Vote
            | KnownConstructor::Propose
    )
}

fn maybe_downgrade(shape: ConstructorShape) -> ConstructorShape {
    if let ConstructorShape::Known(known) = shape
        && should_downgrade(known)
    {
        return ConstructorShape::unknown_data(known.expected_tag(), known.expected_arity());
    }
    shape
}

fn walk(expr: PseudoExpr) -> PseudoExpr {
    struct PreludeDowngrader;

    impl ExprFolder for PreludeDowngrader {
        // Also rewrite Bool/Unit leaves to raw `Constr<N>` so the
        // renderer doesn't emit `True`/`False`/`Void` keywords.
        fn post_bool(&mut self, b: bool) -> PseudoExpr {
            let tag = usize::from(b);
            PseudoExpr::Constr {
                type_hint: None,
                tag,
                fields: vec![].into(),
                shape: ConstructorShape::unknown_data(tag, 0),
            }
        }

        fn post_unit(&mut self) -> PseudoExpr {
            PseudoExpr::Constr {
                type_hint: None,
                tag: 0,
                fields: vec![].into(),
                shape: ConstructorShape::unknown_data(0, 0),
            }
        }

        fn post_constr(
            &mut self,
            type_hint: Option<crate::pseudo::type_hint::TypeHintId>,
            tag: usize,
            fields: Vec<PseudoExpr>,
            shape: ConstructorShape,
        ) -> PseudoExpr {
            PseudoExpr::Constr {
                type_hint,
                tag,
                fields: fields.into(),
                shape: maybe_downgrade(shape),
            }
        }

        fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
            match pattern {
                WhenPattern::Constructor {
                    type_hint,
                    tag,
                    fields,
                    shape,
                } => WhenPattern::Constructor {
                    type_hint,
                    tag,
                    fields,
                    shape: maybe_downgrade(shape),
                },
                // Matches the trait's default: a literal pattern's
                // expression still needs folding, everything else passes
                // through unchanged.
                WhenPattern::Literal(expr) => WhenPattern::Literal(self.fold(expr)),
                other => other,
            }
        }
    }

    PreludeDowngrader.fold(expr)
}

#[cfg(test)]
mod tests;
