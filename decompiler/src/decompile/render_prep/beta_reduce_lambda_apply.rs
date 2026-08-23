//! Beta-reduce `Apply(Lambda(params, body), args)` to a Let-chain.
//!
//! Render-prep passes leave immediately-applied lambdas behind:
//! `decode_church_list_fold_partial` emits an `fn(n) { … }` that a
//! call site applies to the nil-value, and
//! `inline_pack_call_use_sites` leaves residue that downstream
//! simplifiers resolve only once the redex is gone.
//!
//! The rewrite is `Let p1 = a1 in … Let pN = aN in body` — not
//! in-place substitution. The `Let`s stay, and dropping the dead
//! ones is `drop_dead_pure_lets`'s job downstream. Capture-safe by
//! construction: each `Let` scopes its `p_i` exactly as the Lambda
//! did.
//!
//! Only when `args.len() == params.len()`. Partial application
//! would leave the remaining params unbound; over-application would
//! mean the body returns a function — a different rewrite. Skip
//! `RecFn` — beta-reducing the recursive entry breaks the
//! recursion. Skip lambdas whose params carry validator entry names
//! (`is_validator_entry_param_name`): Cardano validator wrapping in
//! `promote_validator_entry_first` needs the Lambda structure to
//! survive. Bottom-up via `rewrite_bottom_up` so inner redexes resolve
//! first. Idempotent — the result's outermost node is a `Let` (or
//! the body's first node), never an `Apply { function: Lambda, … }`.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;

use super::scope_recurse::rewrite_bottom_up;

pub(super) fn beta_reduce_lambda_apply(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_rewrite)
}

fn try_rewrite(expr: PseudoExpr) -> PseudoExpr {
    let PseudoExpr::Apply { function, args } = expr else {
        return expr;
    };
    let (params, body) = match function.into_inner() {
        PseudoExpr::Lambda { params, body } => (params, body),
        other => {
            return PseudoExpr::Apply {
                function: PBox::new(other),
                args,
            };
        }
    };
    if params.len() != args.len() {
        return PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Lambda { params, body }),
            args,
        };
    }
    // Skip validator entry lambdas — promote_validator_entry_first
    // relies on the Lambda structure surviving.
    if params
        .iter()
        .any(|p| is_validator_entry_param_name(&p.name))
    {
        return PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Lambda { params, body }),
            args,
        };
    }
    // Build the Let-chain: Let p1 = a1 in Let p2 = a2 in … body.
    let mut acc = body.into_inner();
    for (p, a) in params.into_iter().zip(args).rev() {
        acc = PseudoExpr::Let {
            name: p.name,
            id: Some(p.id),
            value: PBox::new(a),
            body: PBox::new(acc),
        };
    }
    acc
}

/// Cardano validator entry parameter names — a heuristic on
/// the naming convention `naming::improve_*` uses for the
/// V1/V2/V3 entry args, plus their `_<N>` disambiguation
/// suffixes.
fn is_validator_entry_param_name(name: &str) -> bool {
    // Strip trailing `_<N>` disambiguation suffix.
    let base = name
        .rsplit_once('_')
        .and_then(|(prefix, suffix)| {
            if suffix.chars().all(|c| c.is_ascii_digit()) {
                Some(prefix)
            } else {
                None
            }
        })
        .unwrap_or(name);
    matches!(
        base,
        "redeemer" | "datum" | "script_context" | "purpose" | "script_info" | "tx_info"
    )
}

#[cfg(test)]
mod tests;
