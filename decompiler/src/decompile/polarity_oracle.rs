//! Executable church-bool polarity oracle.
//!
//! [`church_polarity`](crate::decompile::church_polarity) is a
//! structural heuristic. This module proves polarity for closed
//! church-lambda bools (`λt.λf.t` / `λt.λf.f`) by evaluating them
//! on the UPLC CEK machine and seeing which argument they select.
//!
//! Data-tag polarity (`Constr<0>` = true or false) is a naming
//! convention a bare `Constr` cannot reveal — it needs a producing
//! or consuming site tied to a known-truth condition. Out of scope.
//!
//! Only closed two-lambda combinators whose body is a bound `Var`
//! are evaluated, so CEK cannot stick on a free variable. Anything
//! that does not reduce to one of the two integer sentinels is
//! `None` — never a guess.

use std::rc::Rc;

use uplc::PlutusData;
use uplc::ast::{Constant, NamedDeBruijn, Program, Term};
use uplc::machine::cost_model::ExBudget;
use uplc::tx::eval_phase_two_raw;

/// A UPLC program version triple (`(major, minor, patch)`).
pub(crate) type Version = (usize, usize, usize);

/// `uniq_id` for synthesized probe nodes: the CEK machine ignores this
/// source-mapping tag, and probe nodes are never mapped back to source.
const SYNTH_UNIQ: isize = -1;

fn int_sentinel(i: i64) -> Term<NamedDeBruijn> {
    Term::Constant {
        value: Rc::new(Constant::Integer(i.into())),
        uniq_id: SYNTH_UNIQ,
    }
}

fn apply(function: Term<NamedDeBruijn>, argument: Term<NamedDeBruijn>) -> Term<NamedDeBruijn> {
    Term::Apply {
        function: Rc::new(function),
        argument: Rc::new(argument),
        uniq_id: SYNTH_UNIQ,
    }
}

/// Evaluate a CLOSED UPLC term to its normal form via the CEK machine.
/// `None` if the machine errors, diverges, or exhausts the budget.
fn eval_closed(term: Term<NamedDeBruijn>, version: Version) -> Option<Term<NamedDeBruijn>> {
    let program = Program { version, term };
    program.eval(ExBudget::default()).result().ok()
}

/// Proof-based classification of a CLOSED church-**lambda** bool: apply the
/// term to the distinguishable integer sentinels `1` and `0`, evaluate, and
/// read off which one comes back.
///
/// - `Some(true)`  — reduced to `1`: returns its FIRST argument, i.e.
///   `λt.λf.t` = church_**true**.
/// - `Some(false)` — reduced to `0`: returns its SECOND argument (`λt.λf.f`
///   = church_**false**).
/// - `None`        — did not reduce to a sentinel (not a closed 2-arg church
///   bool, forced a lazy arg, diverged, …). Never guesses.
pub(crate) fn prove_church_lambda_bool(
    bool_term: Term<NamedDeBruijn>,
    version: Version,
) -> Option<bool> {
    // [[bool 1] 0]
    let probe = apply(apply(bool_term, int_sentinel(1)), int_sentinel(0));
    // Matched by reference: `Term` has a manual `Drop` (its derived one recurses
    // over a script-controlled depth), and a type with `Drop` cannot have a
    // field moved out of it.
    match &eval_closed(probe, version)? {
        Term::Constant { value, .. } => match value.as_ref() {
            Constant::Integer(i) => {
                if *i == 1.into() {
                    Some(true)
                } else if *i == 0.into() {
                    Some(false)
                } else {
                    None
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// What the oracle proved over a program's closed church-lambda bools.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct ChurchLambdaOracle {
    /// Closed church-lambda bool combinators proven to be `λt.λf.t` (true).
    pub(crate) proven_true: usize,
    /// Closed church-lambda bool combinators proven to be `λt.λf.f` (false).
    pub(crate) proven_false: usize,
    /// Candidate combinators the machine could not reduce to a sentinel.
    pub(crate) inconclusive: usize,
}

impl ChurchLambdaOracle {
    /// Total closed church-lambda bool combinators the oracle inspected.
    pub(crate) fn total(&self) -> usize {
        self.proven_true + self.proven_false + self.inconclusive
    }
}

/// Walk a program and PROVE by evaluation the polarity of every closed
/// church-lambda bool combinator it contains — the shape `λ.λ.Var(i)` with
/// `i ∈ {1, 2}`, which is trivially closed, so evaluation is always safe.
pub(crate) fn scan_church_lambda_bools(program: &Program<NamedDeBruijn>) -> ChurchLambdaOracle {
    let mut out = ChurchLambdaOracle::default();
    walk(&program.term, program.version, &mut out);
    out
}

fn walk(term: &Term<NamedDeBruijn>, version: Version, out: &mut ChurchLambdaOracle) {
    if let Some(index) = closed_church_bool_selector(term) {
        // Structurally a `λ.λ.Var(i)`: prove it by evaluation rather than
        // trusting the index. `index == 2` selects the first arg (true).
        match prove_church_lambda_bool(term.clone(), version) {
            Some(true) => out.proven_true += 1,
            Some(false) => out.proven_false += 1,
            None => out.inconclusive += 1,
        }
        // Sanity: the eval verdict must agree with the de Bruijn index for
        // this trivial shape. The body is a single `Var`, so there is
        // nothing nested to recurse into.
        debug_assert!(
            matches!(
                (index, prove_church_lambda_bool(term.clone(), version)),
                (2, Some(true)) | (1, Some(false)) | (_, None)
            ),
            "church-lambda eval disagreed with de Bruijn index {index}"
        );
        return;
    }
    for child in children(term) {
        walk(child, version, out);
    }
}

/// If `term` is the closed church-bool combinator `λ.λ.Var(i)`, return `i`
/// (`2` = selects first = true; `1` = selects second = false). Structural
/// only; the polarity itself is proven by evaluation.
fn closed_church_bool_selector(term: &Term<NamedDeBruijn>) -> Option<usize> {
    let Term::Lambda { body: outer, .. } = term else {
        return None;
    };
    let Term::Lambda { body: inner, .. } = outer.as_ref() else {
        return None;
    };
    let Term::Var { name, .. } = inner.as_ref() else {
        return None;
    };
    let index: usize = name.index.into();
    (index == 1 || index == 2).then_some(index)
}

fn children(term: &Term<NamedDeBruijn>) -> Vec<&Term<NamedDeBruijn>> {
    match term {
        Term::Delay { body, .. } | Term::Lambda { body, .. } | Term::Force { body, .. } => {
            vec![body.as_ref()]
        }
        Term::Apply {
            function, argument, ..
        } => vec![function.as_ref(), argument.as_ref()],
        Term::Constr { fields, .. } => fields.iter().collect(),
        Term::Case {
            constr, branches, ..
        } => {
            let mut cs = vec![constr.as_ref()];
            cs.extend(branches.iter());
            cs
        }
        Term::Var { .. } | Term::Constant { .. } | Term::Error { .. } | Term::Builtin { .. } => {
            vec![]
        }
    }
}

/// Outcome of applying data args and running the FULL program on the CEK
/// machine — the data-tag oracle.
#[derive(Debug, Clone)]
pub(crate) struct RunOutcome {
    /// How many data args were applied to the program.
    pub(crate) applied: usize,
    /// Whether the program evaluated to success (no `error`, budget intact).
    pub(crate) success: bool,
    /// The machine error string when it did not succeed.
    pub(crate) error: Option<String>,
    /// `trace` logs emitted during evaluation, often the fail label that
    /// pinpoints which check rejected the input.
    pub(crate) logs: Vec<String>,
}

/// Apply `args` (decoded CBOR `PlutusData`, in calling-convention order —
/// datum, redeemer, script_context) to `program` and evaluate it on the CEK
/// machine. Observing whether the success path is reachable on a concrete
/// input is the only sound way to resolve the data-tag bool convention.
pub(crate) fn run_with_data_args(
    program: &Program<NamedDeBruijn>,
    args: &[PlutusData],
) -> RunOutcome {
    let mut applied = program.clone();
    for arg in args {
        applied = applied.apply_data(arg.clone());
    }
    let result = applied.eval(ExBudget::default());
    let logs = result.logs();
    let (success, error) = match result.result() {
        // The machine returns `Err` on an `error` builtin or budget
        // exhaustion, so a plain `Ok` means the validator did NOT reject.
        Ok(_) => (true, None),
        Err(e) => (false, Some(format!("{e:?}"))),
    };
    RunOutcome {
        applied: args.len(),
        success,
        error,
        logs,
    }
}

/// A resolved UTxO for phase-2 evaluation: `(TransactionInput CBOR,
/// TransactionOutput CBOR)`.
pub(crate) type ResolvedUtxo = (Vec<u8>, Vec<u8>);

/// A phase-2 oracle bundle: a transaction plus the resolved inputs it
/// spends or references. `--oracle-tx` feeds one in to resolve the
/// data-tag convention by running the real validator.
#[derive(Debug, Clone, Default)]
pub struct OracleTxBundle {
    /// The target transaction, CBOR bytes.
    pub tx_cbor: Vec<u8>,
    /// Every input the tx spends or references, as `(input CBOR, output
    /// CBOR)` — including the reference-script UTxO that carries the script.
    pub resolved_inputs: Vec<ResolvedUtxo>,
}

/// The phase-2 outcome of ONE script in a transaction.
#[derive(Debug, Clone)]
pub(crate) struct TxScriptOutcome {
    /// Whether the script evaluated to success (no `error`, budget intact).
    pub(crate) success: bool,
    /// `trace` logs (often the fail label pinpointing the rejecting check).
    pub(crate) logs: Vec<String>,
    /// Machine error string when it did not succeed.
    pub(crate) error: Option<String>,
    /// CPU / memory units the evaluation consumed.
    pub(crate) cpu: i64,
    pub(crate) mem: i64,
}

/// Phase-2 evaluate a FULL transaction, one outcome per script it runs.
/// Unlike hand-provided `--oracle-arg` data, each script's ScriptContext is
/// reconstructed by the ledger rules from `tx_cbor` plus the resolved input
/// set, so a real accepted transaction needs no hand-built context.
pub(crate) fn run_tx_phase_two(
    tx_cbor: &[u8],
    resolved: &[ResolvedUtxo],
) -> Result<Vec<TxScriptOutcome>, String> {
    // Mainnet Shelley slot config + a generous phase-2 budget (the ledger
    // max); the oracle only cares about pass/fail, not exact metering.
    let slot_config = (1_596_059_091_000u64, 4_492_800u64, 1_000u32);
    let budget = (10_000_000_000u64, 14_000_000u64);
    let results = eval_phase_two_raw(
        tx_cbor,
        resolved,
        None, // default cost models
        budget,
        slot_config,
        false, // skip phase-1 — only the script results matter
        |_| {},
    )
    .map_err(|e| format!("{e:?}"))?;
    Ok(results
        .into_iter()
        .map(|(_redeemer, res)| {
            let cost = res.cost();
            let (success, error) = match res.result() {
                Ok(_) => (true, None),
                Err(err) => (false, Some(format!("{err:?}"))),
            };
            TxScriptOutcome {
                success,
                logs: res.logs(),
                error,
                cpu: cost.cpu,
                mem: cost.mem,
            }
        })
        .collect())
}

#[cfg(test)]
mod tests;
