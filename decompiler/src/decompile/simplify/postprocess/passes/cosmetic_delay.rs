use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::nameless::NamelessExpr;
use crate::pseudo::nameless::convert::{nameless_to_pseudo, pseudo_to_nameless};
use crate::pseudo::nameless::fold::NamelessFolder;

/// Strip cosmetic `Delay` wrappers: `Delay(Lambda)`, `Delay(RecFn)`,
/// `Delay(Let)`, `Delay(When)` and `Delay(If)` lose the wrapper;
/// every other shape keeps it.
pub(crate) fn strip_cosmetic_delays(expr: PseudoExpr) -> PseudoExpr {
    let (nameless, table) = pseudo_to_nameless(&expr);
    let cleaned = strip_cosmetic_delays_nameless(nameless);
    nameless_to_pseudo(&cleaned, &table)
}

/// Pure nameless implementation of [`strip_cosmetic_delays`].
pub(crate) fn strip_cosmetic_delays_nameless(expr: NamelessExpr) -> NamelessExpr {
    struct StripCosmeticDelays;

    impl NamelessFolder for StripCosmeticDelays {
        fn post_delay(&mut self, inner: NamelessExpr) -> NamelessExpr {
            match &inner {
                NamelessExpr::Lambda { .. } | NamelessExpr::RecFn { .. } => inner,
                NamelessExpr::Let { .. } => inner,
                NamelessExpr::When { .. } | NamelessExpr::If { .. } => inner,
                _ => NamelessExpr::Delay(Box::new(inner)),
            }
        }
    }

    StripCosmeticDelays.fold(expr)
}

#[cfg(test)]
mod tests;
