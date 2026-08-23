//! Peel the outer Apply/Lambda chain of a UPLC program: applied
//! compile-time params, unapplied lambda count, and
//! over-application (pre-applied runtime args).
//!
//! The compiler's compiled validator UPLC has shape:
//! ```text
//! Apply^M (Lambda^N body) const_1 ... const_M
//! ```
//! `inspect_outer` peels the `Apply` chain right-to-left (each
//! constant arg, or a `NonConstant` summary), then the `Lambda`
//! chain on the curried inner term, and returns `OuterStructure`.
//!
//! Not every compiler emits that plain shape. PlutusTx hoists its
//! shared builtins and top-level values into a `let` chain, which
//! compiles to administrative redexes, and the OUTERMOST of those sit on
//! the same Apply spine as the real params:
//!
//! ```text
//! [(lam b [(lam h <rest>) (force headList)]) (force tailList) D1 D2]
//! ```
//!
//! Peeling the spine alone reads three applied params off a script that
//! has two. [`classify_spine_args`] separates them by the one property
//! that cannot be faked: **a compile-time parameter is always a
//! `Constant`.** Off-chain parameterisation applies `con data` and
//! nothing else — `uplc apply` has only CBOR to work with — so a spine
//! argument that is a builtin, a lambda, an application, or a `constr`
//! term is something the compiler put there, not a knob anyone turned.
//!
//! Those land in [`OuterStructure::compiler_binding_indices`], which the
//! param surface reports as compiled-in arguments rather than as
//! `param_N`. Nothing is hidden: the signal a caller needs — that the
//! spine carries them at all — stays in the note.

use uplc::ast::{NamedDeBruijn, Program, Term};

use super::{AppliedParam, OuterStructure};

/// Peel the outer Apply/Lambda chain of a raw UPLC program.
///
/// Default `runtime_arity = 1` (V3 calling convention).
/// Downstream callers refine this based on inferred version + purpose.
pub(crate) fn inspect_outer(program: &Program<NamedDeBruijn>) -> OuterStructure {
    // Step 1: peel the Apply chain right-to-left from the root —
    // `function` is the curried inner term, `argument` the param.
    let mut spine: Vec<&Term<NamedDeBruijn>> = Vec::new();
    let mut current: &Term<NamedDeBruijn> = &program.term;
    while let Term::Apply {
        function, argument, ..
    } = current
    {
        spine.push(argument.as_ref());
        current = function.as_ref();
    }
    // The outermost Apply peeled last, so reverse to put the first
    // param value at `applied[0]`.
    spine.reverse();
    let applied: Vec<AppliedParam> = spine.iter().map(|t| classify(t)).collect();

    // Which spine args cannot be compile-time params. Labeling only:
    // the plan still counts the whole spine, so no wrap decision moves.
    let compiler_binding_indices = classify_spine_args(&spine);

    // Step 2: peel Lambda chain.
    let mut lambda_count: usize = 0;
    while let Term::Lambda { body, .. } = current {
        lambda_count += 1;
        current = body.as_ref();
    }

    // Step 3: over-application (Apply > Lambda). The compiler emits N+1
    // lambdas (N params + 1 ctx) and applies at most N at compile
    // time, so a larger applied count means runtime args were
    // pre-applied.
    //
    // `lambda_chain_length` keeps the raw `lambda_count` even then:
    // it is the TOTAL chain length, from which
    // `build_plan.effective_lambda_count` subtracts
    // `applied_params.len()` for the remaining surface lambdas.
    // Zeroing it on over-apply collapses every disambiguation
    // diagnostic into the "0 lambdas" branch.
    let applied_count = applied.len();
    let pre_applied_runtime_args = applied_count.saturating_sub(lambda_count);

    OuterStructure {
        applied_params: applied,
        compiler_binding_indices,
        lambda_chain_length: lambda_count,
        // Refined downstream from inferred version + purpose.
        runtime_arity: 1,
        pre_applied_runtime_args,
    }
}

/// Spine positions whose argument cannot be a compile-time parameter.
///
/// The test is `Constant`-ness, and it is exact rather than heuristic:
/// every route that applies a parameter to a deployed script — `uplc
/// apply`, `applyParams`, a blueprint's parameter list — carries CBOR
/// and emits `Apply(script, Constant(Data …))`. A builtin, a lambda, an
/// application, or a 1.1.0 `constr` term on that spine was put there by
/// the compiler.
///
/// A plain `Apply^M (Lambda^N body)` from a compiler that hoists nothing
/// has only constants on its spine, so this returns empty.
fn classify_spine_args(spine: &[&Term<NamedDeBruijn>]) -> Vec<usize> {
    spine
        .iter()
        .enumerate()
        .filter(|(_, t)| !matches!(t, Term::Constant { .. }))
        .map(|(i, _)| i)
        .collect()
}

fn classify(term: &Term<NamedDeBruijn>) -> AppliedParam {
    match term {
        Term::Constant { value, .. } => AppliedParam::Constant((**value).clone()),
        other => AppliedParam::NonConstant {
            summary: describe_non_constant_term(other),
        },
    }
}

/// Short human-readable summary of a non-constant Term applied
/// as a compile-time param: `force builtin.<x>` (the surface's
/// pre-applied head/tail-list shape), `builtin.<x>`,
/// `var <name>`, `<apply chain>`, `force`/`delay <inner>`,
/// `constr <tag>` (the 1.1.0 SOP term), else `<term>`.
fn describe_non_constant_term(term: &Term<NamedDeBruijn>) -> String {
    match term {
        Term::Force { body, .. } => match body.as_ref() {
            Term::Builtin { fun, .. } => format!("force builtin.{}", builtin_name(fun)),
            other => format!("force {}", describe_non_constant_term(other)),
        },
        Term::Delay { body, .. } => format!("delay {}", describe_non_constant_term(body)),
        Term::Builtin { fun, .. } => format!("builtin.{}", builtin_name(fun)),
        Term::Var { name, .. } => format!("var {}", name.text),
        Term::Apply { .. } => "<apply chain>".to_string(),
        Term::Lambda { .. } => "<lambda>".to_string(),
        Term::Constant { .. } => "<constant>".to_string(),
        Term::Constr { tag, fields, .. } => {
            if fields.is_empty() {
                format!("constr {tag}")
            } else {
                format!("constr {tag}/{}", fields.len())
            }
        }
        _ => "<term>".to_string(),
    }
}

fn builtin_name(fun: &uplc::builtins::DefaultFunction) -> String {
    // `Debug` of `DefaultFunction` is the CamelCase variant name —
    // lowercase the first letter to match the surface's `builtin.<name>`
    // surface form (e.g. `HeadList` → `headList`).
    let s = format!("{fun:?}");
    let mut chars = s.chars();
    match chars.next() {
        Some(c) => format!("{}{}", c.to_ascii_lowercase(), chars.as_str()),
        None => s,
    }
}
