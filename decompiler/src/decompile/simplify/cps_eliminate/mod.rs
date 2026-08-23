//! CPS selector elimination.
//!
//! V2 Plutus scripts Scott-encode bools as `choose_fst = fn(x, _) { x }`
//! (True) and `choose_snd = fn(_, y) { y }` (False). Functions return
//! those selectors as callables, and call sites over-apply them:
//! `fn_3(x, y)(delay(a), delay(b))`. Classification finds the CPS
//! boolean functions; body rewriting turns selectors into `Bool`;
//! call-site rewriting turns the over-application into `if`/`else`.
//!
//! A classified function used as a value is dropped from the rewrite
//! set — it must stay a callable selector. Call-site rewriting still
//! runs even when nothing classified, so structural selectors
//! (`choose_fst(delay(a), delay(b))`) still become `if`.

use crate::decompile::mid::type_env::TypeEnvironment;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
#[cfg(test)]
use crate::pseudo::ast::{BinaryOp, Binder, PseudoType, UnaryOp};
#[cfg(test)]
use crate::pseudo::var_id::VarId;
use crate::pseudo::walker::Walker;

mod analysis;
mod body_rewrite;

use self::analysis::{
    ClassifiedBindings, KnownBindings, can_rewrite_selector_condition_as_if, classify_functions,
    collect_cps_used_selectors, collect_selector_names, find_value_uses, is_all_selector_returns,
};
#[cfg(test)]
use self::analysis::{CpsClassification, is_fst_selector, is_snd_selector};
use self::body_rewrite::{rewrite_cps_bodies, rewrite_selector_body};

// ===========================================================================
// Public entry point
// ===========================================================================

pub(crate) fn eliminate_cps_selectors(
    expr: PseudoExpr,
    _env: Option<&TypeEnvironment>,
) -> PseudoExpr {
    let (mut fst_names, mut snd_names) = collect_selector_names(&expr);

    // Filter: only keep selectors actually used at CPS-style call sites
    // (applied with >= 2 delay-wrapped args).
    let cps_used = collect_cps_used_selectors(&expr, &fst_names, &snd_names);
    fst_names.intersect_with(&cps_used);
    snd_names.intersect_with(&cps_used);

    let mut classifications = classify_functions(&expr, &fst_names, &snd_names);

    // Safety check: remove any classified function that is used as a value
    if !classifications.is_empty() {
        let value_uses = find_value_uses(&expr, &classifications);
        classifications.remove_all(&value_uses);
    }

    let expr = if !classifications.is_empty() {
        rewrite_cps_bodies(expr, &classifications, &fst_names, &snd_names)
    } else {
        expr
    };

    // ALWAYS run — handles both classified function calls AND structural selectors
    RewriteCallSites {
        classifications: &classifications,
        fst_names: &fst_names,
        snd_names: &snd_names,
    }
    .fold(expr)
}

// ===========================================================================
// Call site rewriting
// ===========================================================================

struct RewriteCallSites<'a> {
    classifications: &'a ClassifiedBindings,
    fst_names: &'a KnownBindings,
    snd_names: &'a KnownBindings,
}

impl Walker for RewriteCallSites<'_> {
    fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
        if let PseudoExpr::Var { name, id } = &function
            && let Some(cls) = self.classifications.get_var(name, *id)
        {
            let n = cls.param_count;
            if args.len() >= n + 2 {
                // The two continuation args should be Delay-wrapped
                if matches!(
                    (&args[n], &args[n + 1]),
                    (PseudoExpr::Delay(_), PseudoExpr::Delay(_))
                ) {
                    let classified_bool_condition =
                        self.classifications.get_var(name, *id).is_some();
                    let selector_condition_can_rewrite =
                        n == 0 && can_rewrite_selector_condition_as_if(&function);
                    if !classified_bool_condition && !selector_condition_can_rewrite {
                        let condition = if n == 0 {
                            function
                        } else {
                            PseudoExpr::Apply {
                                function: PBox::new(function),
                                args: args.iter().take(n).cloned().collect(),
                            }
                        };
                        return PseudoExpr::Apply {
                            function: PBox::new(condition),
                            args: args.into(),
                        };
                    }

                    let mut fn_args = args;
                    let continuation_args = fn_args.split_off(n);
                    let mut continuation_args = continuation_args.into_iter();
                    let then_inner = match continuation_args
                        .next()
                        .expect("classified CPS then continuation should exist")
                    {
                        PseudoExpr::Delay(inner) => inner,
                        _ => unreachable!("classified CPS then continuation was checked"),
                    };
                    let else_inner = match continuation_args
                        .next()
                        .expect("classified CPS else continuation should exist")
                    {
                        PseudoExpr::Delay(inner) => inner,
                        _ => unreachable!("classified CPS else continuation was checked"),
                    };
                    let remaining: Vec<PseudoExpr> = continuation_args.collect();
                    let condition = if fn_args.is_empty() {
                        function
                    } else {
                        PseudoExpr::Apply {
                            function: PBox::new(function),
                            args: fn_args.into(),
                        }
                    };
                    let if_expr = PseudoExpr::If {
                        condition: PBox::new(condition),
                        then_branch: then_inner,
                        else_branch: else_inner,
                    };
                    if !remaining.is_empty() {
                        return PseudoExpr::Apply {
                            function: PBox::new(if_expr),
                            args: remaining.into(),
                        };
                    }
                    return if_expr;
                }
            }
        }

        // Whole-program structural CPS elimination:
        // Apply(selector_expr, [Delay(a), Delay(b)]) -> If(selector_as_bool, a, b)
        // where selector_expr is any expression that evaluates to choose_fst/choose_snd
        if args.len() == 2
            && matches!(
                (&args[0], &args[1]),
                (PseudoExpr::Delay(_), PseudoExpr::Delay(_))
            )
            && is_all_selector_returns(&function, self.fst_names, self.snd_names)
        {
            let bool_expr = rewrite_selector_body(&function, self.fst_names, self.snd_names);
            if !can_rewrite_selector_condition_as_if(&bool_expr) {
                return PseudoExpr::Apply {
                    function: PBox::new(function),
                    args: args.into(),
                };
            }
            let mut args = args.into_iter();
            let then_inner = match args
                .next()
                .expect("structural CPS then continuation should exist")
            {
                PseudoExpr::Delay(inner) => inner,
                _ => unreachable!("structural CPS then continuation was checked"),
            };
            let else_inner = match args
                .next()
                .expect("structural CPS else continuation should exist")
            {
                PseudoExpr::Delay(inner) => inner,
                _ => unreachable!("structural CPS else continuation was checked"),
            };
            return PseudoExpr::If {
                condition: PBox::new(bool_expr),
                then_branch: then_inner,
                else_branch: else_inner,
            };
        }

        PseudoExpr::Apply {
            function: PBox::new(function),
            args: args.into(),
        }
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests;
