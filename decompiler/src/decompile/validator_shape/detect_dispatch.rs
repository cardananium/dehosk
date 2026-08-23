//! Detect V3 multi-purpose dispatch in a `PseudoExpr` body.
//!
//! Looks for the outermost `when` (or the head of a leading let
//! chain) whose arms are prelude `ScriptPurpose` / `ScriptInfo`
//! constructors (`Mint` / `Spend` / `Withdraw` / `Publish` /
//! `Vote` / `Propose`). [`PurposeDispatch::MultiPurpose`] when
//! those arms name ≥2 distinct purposes, in body order.

use crate::decompile::TypeHintId;
use crate::decompile::validator_meta::ValidatorPurpose;
use crate::pseudo::ast::{PseudoExpr, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};

/// Result of dispatch detection.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) enum PurposeDispatch {
    /// No multi-purpose dispatch detected.
    #[default]
    None,
    /// ≥2 distinct purpose constructors found in a When's arms.
    MultiPurpose { purposes: Vec<ValidatorPurpose> },
}

/// Walk `expr` for a multi-purpose dispatch When at the top of the
/// body — see `find_top_level_when` for the shapes that count.
pub(crate) fn detect_dispatch(expr: &PseudoExpr) -> PurposeDispatch {
    let when = find_top_level_when(expr);
    let Some((_, clauses)) = when else {
        return PurposeDispatch::None;
    };

    // Collect purpose constructors from arm patterns.
    //
    // Two recognition paths:
    // 1. `ConstructorShape::Known(known)` — `cardano/patterns.rs`
    //    already identified the prelude constructor.
    // 2. `ConstructorShape::Unknown { tag, .. }` — V3 ScriptInfo arms
    //    `Spending(TxOutRef, Option<Datum>)` (tag 1, arity 2) and
    //    `Certifying(Int, TxCert)` (tag 3, arity 2) land here because
    //    `KnownConstructor::Spend` / `Publish` are the V1/V2 arity-1
    //    forms; `purpose_from_unknown_tag` maps the tag.
    //
    // Unknown tags alone would read any 2-arm Constr When (an Option
    // matched as `Constr<0> | Constr<1>`) as a Mint+Spend dispatch,
    // so at least one arm must anchor the When in a Cardano type: a
    // `KnownConstructor` purpose, which `cardano/patterns.rs` emits
    // only where the subject really flows through a Cardano-domain
    // type, or a `script_info` / `script_purpose` type hint.
    let mut purposes: Vec<ValidatorPurpose> = Vec::new();
    let mut saw_strong_anchor = false;
    let mut saw_non_purpose_arm = false;
    for clause in clauses {
        match &clause.pattern {
            WhenPattern::Constructor {
                shape, type_hint, ..
            } => {
                // A Cardano `type_hint` anchors an Unknown
                // arm — V3 `Spending` (tag 1) and `Certifying`
                // (tag 3) never become a `KnownConstructor`.
                let cardano_hint = is_cardano_purpose_type_hint(type_hint.as_ref());
                let (resolved, is_purpose_arm) = match shape {
                    ConstructorShape::Known(known) => {
                        let p = purpose_from_known(known);
                        (p, p.is_some())
                    }
                    ConstructorShape::Unknown { tag, .. } => {
                        (purpose_from_unknown_tag(*tag), cardano_hint)
                    }
                };
                if is_purpose_arm {
                    saw_strong_anchor = true;
                }
                match resolved {
                    Some(p) => {
                        if !purposes.contains(&p) {
                            purposes.push(p);
                        }
                    }
                    None => {
                        saw_non_purpose_arm = true;
                    }
                }
            }
            WhenPattern::Wildcard => {
                // The trailing `_ -> fail` arm is expected — skip.
            }
            // Var / Literal / List / Tuple / Pair — non-purpose
            // shapes.
            _ => {
                saw_non_purpose_arm = true;
            }
        }
    }
    if !saw_strong_anchor {
        return PurposeDispatch::None;
    }
    if saw_non_purpose_arm || purposes.len() < 2 {
        return PurposeDispatch::None;
    }
    PurposeDispatch::MultiPurpose { purposes }
}

/// Does the pattern's `type_hint` mark it as a Cardano
/// ScriptPurpose / ScriptInfo constructor?
pub(crate) fn is_cardano_purpose_type_hint(hint: Option<&TypeHintId>) -> bool {
    hint.map(|h| {
        let s = h.as_str();
        matches!(s, "script_info" | "script_purpose")
    })
    .unwrap_or(false)
}

/// Map a Plutus ScriptPurpose/ScriptInfo constructor tag to a
/// `ValidatorPurpose`. CIP-0035 V3 layout is `0=Minting,
/// 1=Spending, 2=Rewarding, 3=Certifying, 4=Voting, 5=Proposing`;
/// V1/V2 ScriptPurpose shares tags 0..=3 (no Voting/Proposing).
pub(crate) fn purpose_from_unknown_tag(tag: usize) -> Option<ValidatorPurpose> {
    match tag {
        0 => Some(ValidatorPurpose::Mint),
        1 => Some(ValidatorPurpose::Spend),
        2 => Some(ValidatorPurpose::Withdraw),
        3 => Some(ValidatorPurpose::Certificate),
        4 => Some(ValidatorPurpose::Vote),
        // 5 = Proposing is V3 ScriptInfo only. It anchors a dispatch only
        // with the arm's Cardano `type_hint` (the `cardano_hint` gate in
        // `detect_dispatch`), so it can't over-promote a non-dispatch When.
        5 => Some(ValidatorPurpose::Propose),
        _ => None,
    }
}

/// Map a known prelude constructor to a `ValidatorPurpose`. Returns
/// `None` for constructors that aren't a script purpose.
pub(crate) fn purpose_from_known(known: &KnownConstructor) -> Option<ValidatorPurpose> {
    match known {
        KnownConstructor::Mint => Some(ValidatorPurpose::Mint),
        KnownConstructor::Spend => Some(ValidatorPurpose::Spend),
        KnownConstructor::Withdraw => Some(ValidatorPurpose::Withdraw),
        KnownConstructor::Publish => Some(ValidatorPurpose::Certificate),
        KnownConstructor::Vote => Some(ValidatorPurpose::Vote),
        KnownConstructor::Propose => Some(ValidatorPurpose::Propose),
        _ => None,
    }
}

/// Find the outermost When inside `expr`. The dispatch may sit
/// below a Let chain, inside an `Apply(expect!, [When, tail])` D4
/// expect, inside a Lambda body (validator entry), or in the VALUE
/// of a `Let(name, value, body = Unit)` — the hoisted-helpers
/// shape `let decompiled = <validator_body>; Unit` puts the entry
/// on the VALUE side.
fn find_top_level_when(
    expr: &PseudoExpr,
) -> Option<(&PseudoExpr, &[crate::pseudo::ast::WhenClause])> {
    descend(expr, 0)
}

const MAX_DESCEND_DEPTH: usize = 256;

fn descend(
    expr: &PseudoExpr,
    depth: usize,
) -> Option<(&PseudoExpr, &[crate::pseudo::ast::WhenClause])> {
    if depth > MAX_DESCEND_DEPTH {
        return None;
    }
    match expr {
        PseudoExpr::When {
            subject, clauses, ..
        } => Some((subject.as_ref(), clauses.as_slice())),
        PseudoExpr::Let { value, body, .. } => {
            // The body is the continuation chain; when nothing
            // in it is a When, fall back to the VALUE side, where
            // the hoisted validator entry lives.
            if let Some(found) = descend(body.as_ref(), depth + 1) {
                return Some(found);
            }
            descend(value.as_ref(), depth + 1)
        }
        // D4 form: `Apply(expect!, [When, tail])` — the When is
        // the first arg.
        PseudoExpr::Apply { function, args } => {
            if let PseudoExpr::Var { name, .. } = function.as_ref()
                && name.as_str() == "expect!"
                && !args.is_empty()
            {
                return descend(&args[0], depth + 1);
            }
            None
        }
        // Validator entry lambda — descend into body.
        PseudoExpr::Lambda { body, .. } => descend(body.as_ref(), depth + 1),
        _ => None,
    }
}
