//! Program-scoped church-bool polarity detection.
//!
//! Most Plutus scripts use the CIP / data-Bool ABI (`True = Constr<1>`,
//! `False = Constr<0>`). PlutusTx-compiled scripts use the inverse
//! (`church_true = Constr<0>`, `church_false = Constr<1>`). The
//! simplifier's [`Simplifier::is_true`]/[`Simplifier::is_false`]
//! (`simplify/helpers/shape.rs`) read a bare `DataTag` nullary Constr
//! with the CIP convention, so an inverse-CIP program gets every 2-arm
//! church-bool collapse branch-swapped and `church_true` printed as `Nil`.
//! Detect on the freshly-lowered MIR seed (before any simplify) and
//! carry the verdict by VALUE for the rest of the decompile: the
//! pipeline stores it in [`SimplifyState`], which seeds every
//! [`Simplifier`]'s `church_polarity` (read by `is_true`/`is_false`),
//! and hands it out on [`PipelineOutput`] for the render half, which
//! puts it in its [`RenderCtx`].
//!
//! [`SimplifyState`]: crate::decompile::simplify::SimplifyState
//! [`Simplifier`]: crate::decompile::simplify::Simplifier
//! [`PipelineOutput`]: crate::decompile::pipeline::PipelineOutput
//! [`RenderCtx`]: crate::decompile::RenderCtx
//!
//! Fail-safe: anything ambiguous → [`ChurchPolarity::Cip`], so CIP
//! output is unchanged unless a program is proven inverse-CIP.
//! [`ChurchPolarity::InverseCip`] needs all three structural signals
//! to agree that `Constr<0> = church_true`: (1) an inverse-CIP producer
//! `if c { Constr<0> } else { Constr<1> }`; (2) a tag-0 success oracle —
//! an `expect`-style `when` (`expect P = X` desugars to
//! `when X is { P -> k; _ -> fail }`) whose success arm matches nullary
//! `Constr<0>` while a sibling arm fails; (3) no tag-1 success oracle
//! (the CIP signature). (1) and (2) are individually tag-ambiguous — a
//! CIP `if c { False } else { True }` for `!c` also has `Constr<0>` on
//! the then-branch — so all three are required. `ScottPositional` origin
//! is structurally immune: `is_true`/`is_false` never read those with
//! either convention.

use std::collections::HashMap;

use crate::decompile::render_prep::scope_recurse::children;
use crate::pseudo::ast::{PseudoExpr, WhenPattern};
use crate::pseudo::var_id::VarId;

/// Which Plutus `Constr` tag a program uses for church/data `True`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum ChurchPolarity {
    /// CIP / data-Bool ABI: `True = Constr<1>`, `False = Constr<0>`. The
    /// default, and what almost every script uses.
    #[default]
    Cip,
    /// PlutusTx-style church bool: `church_true = Constr<0>`,
    /// `church_false = Constr<1>` (the inverse of CIP).
    InverseCip,
}

impl ChurchPolarity {
    /// The `DataTag` nullary `Constr` tag that means `False` under this
    /// convention. CIP → 0; inverse-CIP → 1.
    pub(crate) fn data_tag_for_false(self) -> usize {
        match self {
            ChurchPolarity::Cip => 0,
            ChurchPolarity::InverseCip => 1,
        }
    }

    /// The `DataTag` nullary `Constr` tag that means `True`. CIP → 1;
    /// inverse-CIP → 0.
    pub(crate) fn data_tag_for_true(self) -> usize {
        match self {
            ChurchPolarity::Cip => 1,
            ChurchPolarity::InverseCip => 0,
        }
    }
}

/// The three structural signals behind [`detect_church_polarity`]'s verdict,
/// captured for the `--emit polarity-report` diagnostic. Purely
/// observational; nothing in the render path reads these.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct ChurchPolaritySignals {
    /// Signal (1): an inverse-CIP producer `if c { Constr<0> } else
    /// { Constr<1> }` — a nullary church bool whose cond-true branch is tag 0.
    pub(crate) inverse_cip_producer: bool,
    /// Signal (2): a tag-0 success oracle (`expect Constr<0> = X; <success>`
    /// with a sibling fail arm).
    pub(crate) success_oracle_tag0: bool,
    /// Signal (3, as a veto): a tag-1 success oracle — the CIP signature that
    /// makes the convention ambiguous and forces the fail-safe `Cip` verdict.
    pub(crate) success_oracle_tag1: bool,
    /// The verdict [`detect_church_polarity`] returned given the above.
    pub(crate) verdict: ChurchPolarity,
}

impl ChurchPolaritySignals {
    /// The verdict alone — what everything but the report needs.
    pub(crate) fn verdict(&self) -> ChurchPolarity {
        self.verdict
    }
}

/// Header note prepended to default output for programs classified
/// [`ChurchPolarity::InverseCip`], warning that the polarity is a
/// heuristic and the rendered bools may be inverted. Empty for `Cip`.
pub(crate) fn inverse_cip_header_note(polarity: ChurchPolarity) -> String {
    match polarity {
        ChurchPolarity::Cip => String::new(),
        ChurchPolarity::InverseCip => "// Note: church-bool polarity detected as \
             InverseCip (PlutusTx inverse convention: church_true = Constr<0>) — a HEURISTIC. \
             `True`/`False`/`!` and church-derived pass/fail may be inverted if misdetected. \
             See `--emit polarity-report`.\n"
            .to_string(),
    }
}

/// Render the human-readable `--emit polarity-report` diagnostic from the
/// detection's [`ChurchPolaritySignals`] plus an EXECUTABLE oracle pass
/// over `program`'s closed church-lambda bools.
pub(crate) fn render_polarity_report(
    program: &uplc::ast::Program<uplc::ast::NamedDeBruijn>,
    signals: &ChurchPolaritySignals,
    data_args: &[uplc::PlutusData],
    oracle_tx: Option<&crate::decompile::polarity_oracle::OracleTxBundle>,
) -> String {
    let mut sections = vec![
        render_polarity_report_heuristic(signals),
        church_lambda_oracle_section(program),
        data_tag_oracle_section(program, signals.verdict(), data_args, oracle_tx),
    ];
    sections.retain(|s| !s.is_empty());
    sections.join("\n\n")
}

/// The closed church-LAMBDA oracle section — proof by evaluation.
fn church_lambda_oracle_section(program: &uplc::ast::Program<uplc::ast::NamedDeBruijn>) -> String {
    let oracle = crate::decompile::polarity_oracle::scan_church_lambda_bools(program);
    if oracle.total() == 0 {
        "Church-LAMBDA oracle (proof by CEK evaluation):\n\
         \x20 no closed church-LAMBDA bools found — this program likely encodes bools with the\n\
         \x20 data-tag convention (`Constr<0>`/`Constr<1>`, e.g. inverse-polarity scripts), which a bare value\n\
         \x20 cannot reveal. See the data-tag oracle below."
            .to_string()
    } else {
        format!(
            "Church-LAMBDA oracle (proof by CEK evaluation of closed church-LAMBDA bools):\n\
             \x20 inspected            : {}\n\
             \x20 proven true  (λt.λf.t): {}\n\
             \x20 proven false (λt.λf.f): {}\n\
             \x20 inconclusive         : {}\n\
             \x20 These are PROOFS (the machine reduced each to a sentinel), not heuristics.",
            oracle.total(),
            oracle.proven_true,
            oracle.proven_false,
            oracle.inconclusive,
        )
    }
}

/// The data-tag oracle section. Resolves the `Constr<0>`/`Constr<1>`
/// convention by RUNNING the validator: prefers a full phase-2
/// transaction bundle (`--oracle-tx`, the practical path — the ledger
/// rebuilds the ScriptContext), else applies raw `--oracle-arg` data.
/// With neither, the convention is unobservable and the section says so.
fn data_tag_oracle_section(
    program: &uplc::ast::Program<uplc::ast::NamedDeBruijn>,
    verdict: ChurchPolarity,
    data_args: &[uplc::PlutusData],
    oracle_tx: Option<&crate::decompile::polarity_oracle::OracleTxBundle>,
) -> String {
    if let Some(bundle) = oracle_tx {
        return data_tag_phase_two_section(bundle, verdict);
    }
    if data_args.is_empty() {
        return "Data-tag oracle (proof by running the validator):\n\
             \x20 SKIPPED — no runtime input provided. The `Constr<0>` = true/false convention is\n\
             \x20 only observable by executing the validator on a concrete input. Re-run with\n\
             \x20 `--oracle-tx <bundle.json>` (a real tx + resolved inputs — the practical path)\n\
             \x20 or `--oracle-arg <cbor-hex>` per argument to resolve it."
            .to_string();
    }
    let outcome = crate::decompile::polarity_oracle::run_with_data_args(program, data_args);
    let logs = if outcome.logs.is_empty() {
        "(none)".to_string()
    } else {
        outcome.logs.join(", ")
    };
    if outcome.success {
        let confirms = match verdict {
            ChurchPolarity::InverseCip => {
                "the tag-0 success path is reachable and was taken, \
                 CORROBORATING the InverseCip verdict"
            }
            ChurchPolarity::Cip => {
                "the success path is reachable and was taken, consistent with \
                 the Cip verdict"
            }
        };
        format!(
            "Data-tag oracle (proof by running the validator on {} provided arg(s)):\n\
             \x20 result: SUCCESS (the validator did not reject).\n\
             \x20 traces: {}\n\
             \x20 Every check on the executed path held, so {}.",
            outcome.applied, logs, confirms,
        )
    } else {
        format!(
            "Data-tag oracle (proof by running the validator on {} provided arg(s)):\n\
             \x20 result: FAILED — {}\n\
             \x20 traces: {}\n\
             \x20 If you expected this input to SUCCEED, either the args are invalid / in the\n\
             \x20 wrong order, or the polarity verdict (and thus the rendered True/False/!) is\n\
             \x20 wrong. If you expected failure, this run is consistent.",
            outcome.applied,
            outcome.error.as_deref().unwrap_or("unknown error"),
            logs,
        )
    }
}

/// Phase-2 evaluate a real transaction bundle and report per-script
/// SUCCESS/FAILURE — the sound data-tag resolution, on genuine data.
fn data_tag_phase_two_section(
    bundle: &crate::decompile::polarity_oracle::OracleTxBundle,
    verdict: ChurchPolarity,
) -> String {
    match crate::decompile::polarity_oracle::run_tx_phase_two(
        &bundle.tx_cbor,
        &bundle.resolved_inputs,
    ) {
        Err(e) => format!(
            "Data-tag oracle (phase-2 run of the provided transaction):\n\
             \x20 ERROR — could not evaluate: {e}\n\
             \x20 Check the bundle (tx CBOR + every spent/referenced input, incl. the\n\
             \x20 reference-script UTxO) is complete and well-formed.",
        ),
        Ok(outcomes) => {
            let mut lines = vec![format!(
                "Data-tag oracle (phase-2 run of the provided transaction — {} script(s)):",
                outcomes.len()
            )];
            let all_success = !outcomes.is_empty() && outcomes.iter().all(|o| o.success);
            for (i, o) in outcomes.iter().enumerate() {
                let logs = if o.logs.is_empty() {
                    "(none)".to_string()
                } else {
                    o.logs.join(", ")
                };
                if o.success {
                    lines.push(format!(
                        "\x20 script #{i}: SUCCESS (cpu {}, mem {}); traces: {}",
                        o.cpu, o.mem, logs
                    ));
                } else {
                    lines.push(format!(
                        "\x20 script #{i}: FAILED — {}; traces: {}",
                        o.error.as_deref().unwrap_or("unknown error"),
                        logs
                    ));
                }
            }
            if all_success {
                let confirms = match verdict {
                    ChurchPolarity::InverseCip => {
                        "the tag-0 success path is reachable and was \
                         taken on real data, CORROBORATING the InverseCip verdict"
                    }
                    ChurchPolarity::Cip => {
                        "the success path is reachable and was taken on real \
                         data, consistent with the Cip verdict"
                    }
                };
                lines.push(format!(
                    "\x20 Every check on the executed path held, so {confirms}."
                ));
            } else {
                lines.push(
                    "\x20 At least one script rejected — if this tx was accepted on-chain, the \
                     bundle is incomplete; otherwise the input genuinely fails."
                        .to_string(),
                );
            }
            lines.join("\n")
        }
    }
}

/// The heuristic half of the polarity report (structural signals only).
fn render_polarity_report_heuristic(s: &ChurchPolaritySignals) -> String {
    let yn = |b: bool| if b { "yes" } else { "no" };
    let (verdict, headline) = match s.verdict {
        ChurchPolarity::Cip => (
            "Cip (default)",
            "Booleans use the CIP/data ABI: True = Constr<1>, False = Constr<0>.",
        ),
        ChurchPolarity::InverseCip => (
            "InverseCip (detected — HEURISTIC)",
            "Booleans use the inverse PlutusTx convention: church_true = Constr<0>, \
             church_false = Constr<1>.",
        ),
    };
    let defaulted = matches!(s.verdict, ChurchPolarity::Cip)
        && !(s.inverse_cip_producer && s.success_oracle_tag0 && !s.success_oracle_tag1);
    format!(
        "CHURCH-BOOL POLARITY REPORT\n\
         ===========================\n\
         verdict: {verdict}\n\
         {headline}\n\
         {}\n\
         \n\
         Detection signals (structural, from the lowering seed):\n\
         \x20 (1) inverse-CIP producer  `if c {{ Constr<0> }} else {{ Constr<1> }}` : {}\n\
         \x20 (2) tag-0 success oracle   `expect Constr<0> = X; <success>`          : {}\n\
         \x20 (3) tag-1 success oracle   (CIP signature — vetoes inverse-CIP)       : {}\n\
         \n\
         Verdict rule: InverseCip requires (1) AND (2) AND NOT (3); otherwise Cip.\n\
         \n\
         WARNING: this is a program-scoped structural HEURISTIC, not a proof. If the\n\
         verdict is wrong, every church-bool `True`/`False`/`!` and the pass/fail\n\
         polarity of church-derived `when` verdicts is INVERTED. Cross-check a\n\
         suspicious site against `--emit uplc` or the script's on-chain behaviour.",
        if defaulted {
            "(fail-safe default: no positive inverse-CIP evidence)"
        } else {
            "(positive detection)"
        },
        yn(s.inverse_cip_producer),
        yn(s.success_oracle_tag0),
        yn(s.success_oracle_tag1),
    )
}

/// The nullary `Constr` tag that means `True` for THIS specific church
/// bool: the shape's own `church_true` witness when it carries one, else
/// the program-scoped [`data_tag_for_true`]. This is the read-path switch
/// that makes the church-bool consumers per-bool instead of whole-program.
pub(crate) fn true_tag_for_shape(
    shape: &crate::pseudo::constructor::ConstructorShape,
    polarity: ChurchPolarity,
) -> usize {
    shape
        .church_true()
        .unwrap_or_else(|| polarity.data_tag_for_true())
}

/// The nullary `Constr` tag that means `False` for THIS church bool — the
/// sibling of [`true_tag_for_shape`] when witnessed, else the program-scoped
/// [`data_tag_for_false`].
pub(crate) fn false_tag_for_shape(
    shape: &crate::pseudo::constructor::ConstructorShape,
    polarity: ChurchPolarity,
) -> usize {
    match shape.church_true() {
        // Church bools are 2-valued over {0,1}; the false tag is the other one.
        Some(0) => 1,
        Some(_) => 0,
        None => polarity.data_tag_for_false(),
    }
}

/// Detect the program's church-bool polarity from the MIR-lowered seed,
/// returning the verdict together with the three structural signals
/// behind it (the `--emit polarity-report` diagnostic renders those).
/// Fail-safe to [`ChurchPolarity::Cip`] (see the module docs for the gate).
pub(crate) fn detect_church_polarity(seed: &PseudoExpr) -> ChurchPolaritySignals {
    let consts = collect_nullary_constr_consts(seed);
    // Gate (3), NO tag-1 success oracle, is the consistency check: a genuine
    // CIP program — even one that legitimately `expect`s a predicate to be
    // False = tag 0 — almost always ALSO has normal `expect <True = tag 1>`
    // success checks, so a tag-1 oracle makes the convention ambiguous. A
    // uniformly inverse-CIP program has only tag-0 success oracles. The gate
    // covers the case where (1) and (2) co-occur INDEPENDENTLY in a CIP
    // program.
    //
    // Structural church-polarity detection can't be fully sound, so the two
    // residual failure modes are DELIBERATELY asymmetric — valid-looking-
    // wrong output is worse than honestly-invalid output:
    //   - FALSE NEGATIVE (gate (3) rejects a genuine inverse-CIP program that
    //     succeeds-on-false, since under inverse-CIP that has a tag-1 oracle):
    //     ACCEPTABLE — no fix applies, the honest church residue stays.
    //   - FALSE POSITIVE (a CIP program with PlutusTx-style church-bool Constr
    //     producers that only ever succeeds-on-false trips all three) would be
    //     program-wide-WRONG, so it is kept maximally unlikely: signal (1) is
    //     itself atypical of native-bool CIP output.
    // Both directions fail TOWARD Cip/honest, never toward a silent inversion.
    let producer = has_inverse_cip_producer(seed, &consts);
    let oracle_tag0 = has_success_oracle_with_tag(seed, 0);
    let oracle_tag1 = has_success_oracle_with_tag(seed, 1);
    let verdict = if producer && oracle_tag0 && !oracle_tag1 {
        ChurchPolarity::InverseCip
    } else {
        ChurchPolarity::Cip
    };
    ChurchPolaritySignals {
        inverse_cip_producer: producer,
        success_oracle_tag0: oracle_tag0,
        success_oracle_tag1: oracle_tag1,
        verdict,
    }
}

/// Top-level `let`-bound nullary `Constr` consts (e.g. `let e =
/// Constr<0>`), so a church bool referenced by name resolves to its tag.
fn collect_nullary_constr_consts(expr: &PseudoExpr) -> HashMap<VarId, usize> {
    let mut map = HashMap::new();
    let mut cur = expr;
    while let PseudoExpr::Let {
        id, value, body, ..
    } = cur
    {
        if let (Some(vid), PseudoExpr::Constr { tag, fields, .. }) = (id, value.as_ref())
            && fields.is_empty()
        {
            map.insert(*vid, *tag);
        }
        cur = body;
    }
    map
}

/// The tag of `expr` if it is a nullary `Constr` (inline) or a `Var`
/// bound to a nullary-`Constr` const.
fn nullary_constr_tag(expr: &PseudoExpr, consts: &HashMap<VarId, usize>) -> Option<usize> {
    match expr {
        PseudoExpr::Constr { tag, fields, .. } if fields.is_empty() => Some(*tag),
        PseudoExpr::Var { id: Some(vid), .. } => consts.get(vid).copied(),
        _ => None,
    }
}

/// Signal (1): an inverse-CIP church producer `if c { Constr<0> } else
/// { Constr<1> }` (nullary on both branches).
fn has_inverse_cip_producer(expr: &PseudoExpr, consts: &HashMap<VarId, usize>) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let PseudoExpr::If {
            then_branch,
            else_branch,
            ..
        } = current
            && nullary_constr_tag(then_branch, consts) == Some(0)
            && nullary_constr_tag(else_branch, consts) == Some(1)
        {
            return true;
        }
        pending.extend(children(current));
    }
    false
}

/// A success oracle for the nullary `Constr<tag>` branch — a `when` whose
/// non-fail arm matches `Constr<tag>` (nullary) while a sibling arm fails
/// (the desugaring of `expect <Constr<tag>> = X; <success>`). tag 0 is the
/// inverse-CIP success signature; tag 1 is the CIP one.
fn has_success_oracle_with_tag(expr: &PseudoExpr, want_tag: usize) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let PseudoExpr::When { clauses, .. } = current {
            let has_tag_success = clauses.iter().any(|cl| {
                cl.guard.is_none()
                    && matches!(
                        &cl.pattern,
                        WhenPattern::Constructor { tag, fields, .. }
                            if *tag == want_tag && fields.is_empty()
                    )
                    && !body_is_fail(&cl.body)
            });
            let has_fail_sibling = clauses.iter().any(|cl| body_is_fail(&cl.body));
            if has_tag_success && has_fail_sibling {
                return true;
            }
        }
        pending.extend(children(current));
    }
    false
}

/// Whether an expression's tail position is a hard failure (`error`).
fn body_is_fail(expr: &PseudoExpr) -> bool {
    let mut current = expr;
    loop {
        match current {
            PseudoExpr::Error { .. } => return true,
            PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => current = inner,
            PseudoExpr::Let { body, .. } => current = body,
            PseudoExpr::Trace { value, .. } => current = value,
            _ => return false,
        }
    }
}

#[cfg(test)]
mod tests;
