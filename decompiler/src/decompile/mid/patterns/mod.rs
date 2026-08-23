//! Pattern recognition for MidExpr.
//!
//! IfThenElse → MidExpr::If
//! Scott encoding → MidExpr::Case
//! ChooseList, ChooseData → MidExpr::Case
//! Trace builtin → MidExpr::Trace
//! Y-combinator → Closure.recursive

use uplc::builtins::DefaultFunction;

use super::fold::rewrite_bottom_up;
use crate::pseudo::mid::expr::{CaseEncoding, MidBranch, MidExpr};
use crate::pseudo::mid::expr_id::{MidExprId, ProvenanceBuilder};
use crate::pseudo::var_id::VarId;

/// Rewrite UPLC idioms into their MIR shapes (`If`, `Trace`, Scott encoding, …).
///
/// Bottom-up: a node is offered to the recognizers only once its children are
/// already in their recognized form, so a nested idiom is folded before the
/// enclosing one looks at it. Runs on the owned rewriter because that is the
/// only way to act on a node AFTER its children without a `&mut` that would
/// have to stay live across them — see [`rewrite_bottom_up`].
pub(crate) fn recognize_patterns(expr: &mut MidExpr, provenance: &mut ProvenanceBuilder) {
    let placeholder = MidExpr::Error { id: expr.id() };
    let taken = std::mem::replace(expr, placeholder);
    *expr = rewrite_bottom_up(taken, &mut |mut node| {
        try_recognize_if_then_else(&mut node, provenance);
        try_recognize_trace(&mut node, provenance);
        try_recognize_choose_list(&mut node, provenance);
        try_recognize_choose_data(&mut node, provenance);
        try_recognize_scott_encoding(&mut node, provenance);
        try_recognize_and_or(&mut node);
        node
    });
}

// ===== IfThenElse Pattern =====

/// Detect Builtin(IfThenElse, [cond, then, else]) → If.
/// V3 UPLC doesn't require Force for builtins, so forces are not checked.
fn try_recognize_if_then_else(expr: &mut MidExpr, provenance: &mut ProvenanceBuilder) {
    if let MidExpr::Builtin {
        id,
        fun: DefaultFunction::IfThenElse,
        args,
        ..
    } = expr
        && args.len() == 3
    {
        let mid_id = *id;
        let cond = std::mem::replace(&mut args[0], MidExpr::Error { id: mid_id });
        let then_b = unwrap_thunk_into_owner(
            std::mem::replace(&mut args[1], MidExpr::Error { id: mid_id }),
            provenance,
        );
        let else_b = unwrap_thunk_into_owner(
            std::mem::replace(&mut args[2], MidExpr::Error { id: mid_id }),
            provenance,
        );
        let rewritten_id = provenance.fresh_derived_from(mid_id);

        // Every shape emits as If; the lowerer reads And/Or/Not back out:
        // if(a, b, False) → And, if(a, True, b) → Or, if(x, False, True) → Not.
        *expr = MidExpr::If {
            id: rewritten_id,
            condition: Box::new(cond),
            then_branch: Box::new(then_b),
            else_branch: Box::new(else_b),
        };
    }

    // Also handle Force(Builtin(IfThenElse, ...)) — some forms have an outer Force
    if let MidExpr::Force {
        id,
        body,
        resolved: _,
    } = expr
        && let MidExpr::Builtin {
            id: builtin_id,
            fun: DefaultFunction::IfThenElse,
            args,
            ..
        } = body.as_mut()
        && args.len() == 3
    {
        let mid_id = *id;
        let cond = std::mem::replace(&mut args[0], MidExpr::Error { id: mid_id });
        let then_b = unwrap_thunk_into_owner(
            std::mem::replace(&mut args[1], MidExpr::Error { id: mid_id }),
            provenance,
        );
        let else_b = unwrap_thunk_into_owner(
            std::mem::replace(&mut args[2], MidExpr::Error { id: mid_id }),
            provenance,
        );
        let rewritten_id = provenance.fresh_derived_from_many(&[mid_id, *builtin_id]);

        *expr = MidExpr::If {
            id: rewritten_id,
            condition: Box::new(cond),
            then_branch: Box::new(then_b),
            else_branch: Box::new(else_b),
        };
    }
}

// ===== Trace Pattern =====

/// Detect Builtin(Trace, [message, value]) → Trace { message, body }
fn try_recognize_trace(expr: &mut MidExpr, provenance: &mut ProvenanceBuilder) {
    if let MidExpr::Builtin {
        id,
        fun: DefaultFunction::Trace,
        args,
        ..
    } = expr
        && args.len() == 2
    {
        let mid_id = *id;
        let message = std::mem::replace(&mut args[0], MidExpr::Error { id: mid_id });
        let body = unwrap_thunk_into_owner(
            std::mem::replace(&mut args[1], MidExpr::Error { id: mid_id }),
            provenance,
        );
        let rewritten_id = provenance.fresh_derived_from(mid_id);
        *expr = MidExpr::Trace {
            id: rewritten_id,
            message: Box::new(message),
            body: Box::new(body),
        };
    }
}

// ===== ChooseList Pattern =====

/// Detect Builtin(ChooseList, [list, nil_case, cons_case]) → Case with ChooseList encoding
fn try_recognize_choose_list(expr: &mut MidExpr, provenance: &mut ProvenanceBuilder) {
    // Handle both direct Builtin and Force(Builtin(...))
    let is_choose_list = match expr {
        MidExpr::Builtin {
            fun: DefaultFunction::ChooseList,
            args,
            ..
        } if args.len() == 3 => true,
        MidExpr::Force { body, .. } => matches!(
            body.as_ref(),
            MidExpr::Builtin {
                fun: DefaultFunction::ChooseList,
                args,
                ..
            } if args.len() == 3
        ),
        _ => false,
    };

    if !is_choose_list {
        return;
    }

    // Extract from either form
    let (root_ids, list, nil_case, cons_case) = match expr {
        MidExpr::Builtin { id, args, .. } if args.len() == 3 => {
            let mid_id = *id;
            let list = std::mem::replace(&mut args[0], MidExpr::Error { id: mid_id });
            let nil = unwrap_thunk_into_owner(
                std::mem::replace(&mut args[1], MidExpr::Error { id: mid_id }),
                provenance,
            );
            let cons = unwrap_thunk_into_owner(
                std::mem::replace(&mut args[2], MidExpr::Error { id: mid_id }),
                provenance,
            );
            (vec![mid_id], list, nil, cons)
        }
        MidExpr::Force { id, body, .. } => {
            if let MidExpr::Builtin {
                id: builtin_id,
                args,
                ..
            } = body.as_mut()
            {
                if args.len() == 3 {
                    let mid_id = *id;
                    let list = std::mem::replace(&mut args[0], MidExpr::Error { id: mid_id });
                    let nil = unwrap_thunk_into_owner(
                        std::mem::replace(&mut args[1], MidExpr::Error { id: mid_id }),
                        provenance,
                    );
                    let cons = unwrap_thunk_into_owner(
                        std::mem::replace(&mut args[2], MidExpr::Error { id: mid_id }),
                        provenance,
                    );
                    (vec![mid_id, *builtin_id], list, nil, cons)
                } else {
                    return;
                }
            } else {
                return;
            }
        }
        _ => return,
    };
    let rewritten_id = provenance.fresh_derived_from_many(&root_ids);

    *expr = MidExpr::Case {
        id: rewritten_id,
        scrutinee: Box::new(list),
        branches: vec![
            MidBranch {
                tag: 0,
                binders: vec![],
                body: nil_case,
            },
            MidBranch {
                tag: 1,
                binders: vec![],
                body: cons_case,
            },
        ],
        encoding: CaseEncoding::ChooseList,
    };
}

// ===== ChooseData Pattern =====

/// Detect `Builtin(ChooseData, [data, constr, map, list, int, bs, ...])`
/// → Case with IfChain encoding.
///
/// `ChooseData` dispatches on the top-level data constructor kind (Constr, Map,
/// List, Integer, ByteString), so it lowers to `CaseEncoding::IfChain` — a
/// type-based dispatch, not a positional constructor match. Extension handlers
/// beyond the canonical five stay explicit MIR branches instead of leaking
/// through as late `Data.case(...)` cleanup.
///
/// Also handles `Force(Builtin(ChooseData, ...))`.
fn try_recognize_choose_data(expr: &mut MidExpr, provenance: &mut ProvenanceBuilder) {
    let is_choose_data = match expr {
        MidExpr::Builtin {
            fun: DefaultFunction::ChooseData,
            args,
            ..
        } if args.len() >= 6 => true,
        MidExpr::Force { body, .. } => matches!(
            body.as_ref(),
            MidExpr::Builtin {
                fun: DefaultFunction::ChooseData,
                args,
                ..
            } if args.len() >= 6
        ),
        _ => false,
    };

    if !is_choose_data {
        return;
    }

    let (root_ids, data, cases) = match expr {
        MidExpr::Builtin { id, args, .. } if args.len() >= 6 => {
            let mid_id = *id;
            let data = std::mem::replace(&mut args[0], MidExpr::Error { id: mid_id });
            let cases: Vec<MidExpr> = args[1..]
                .iter_mut()
                .map(|a| {
                    unwrap_thunk_into_owner(
                        std::mem::replace(a, MidExpr::Error { id: mid_id }),
                        provenance,
                    )
                })
                .collect();
            (vec![mid_id], data, cases)
        }
        MidExpr::Force { id, body, .. } => {
            if let MidExpr::Builtin {
                id: builtin_id,
                args,
                ..
            } = body.as_mut()
            {
                if args.len() >= 6 {
                    let mid_id = *id;
                    let data = std::mem::replace(&mut args[0], MidExpr::Error { id: mid_id });
                    let cases: Vec<MidExpr> = args[1..]
                        .iter_mut()
                        .map(|a| {
                            unwrap_thunk_into_owner(
                                std::mem::replace(a, MidExpr::Error { id: mid_id }),
                                provenance,
                            )
                        })
                        .collect();
                    (vec![mid_id, *builtin_id], data, cases)
                } else {
                    return;
                }
            } else {
                return;
            }
        }
        _ => return,
    };
    let rewritten_id = provenance.fresh_derived_from_many(&root_ids);

    // Tags: 0 = Constr, 1 = Map, 2 = List, 3 = Integer, 4 = ByteString
    let branches: Vec<MidBranch> = cases
        .into_iter()
        .enumerate()
        .map(|(tag, body)| MidBranch {
            tag,
            binders: vec![],
            body,
        })
        .collect();

    *expr = MidExpr::Case {
        id: rewritten_id,
        scrutinee: Box::new(data),
        branches,
        encoding: CaseEncoding::IfChain,
    };
}

// ===== Y-Combinator Pattern =====

/// Mark the Closure recursive if `value` is a Y-combinator.
pub(crate) fn try_mark_recursive(let_var: VarId, value: &mut MidExpr) {
    if is_y_combinator(value) {
        // `let f = Y(body)` means `f` is a recursive function.
        mark_closure_recursive(value, let_var);
    }
}

fn is_y_combinator(expr: &MidExpr) -> bool {
    let inner = unwrap_thunks_ref(expr);

    // Must be a Closure with exactly 1 param
    if let MidExpr::Closure { params, body, .. } = inner {
        if params.len() != 1 {
            return false;
        }

        // Check for Let pattern with self-application
        if let MidExpr::Let {
            value,
            body: let_body,
            ..
        } = body.as_ref()
            && (contains_self_application(value) || contains_self_application(let_body))
        {
            return true;
        }

        // Check for direct self-application: f(f)
        if contains_self_application(body) {
            return true;
        }
    }
    false
}

/// Whether the tree contains a `f(f, …)` self-application — the Y-combinator
/// witness.
fn contains_self_application(expr: &MidExpr) -> bool {
    fn searched(expr: &MidExpr) -> Vec<&MidExpr> {
        match expr {
            MidExpr::Apply { function, args, .. } => {
                let mut c = vec![function.as_ref()];
                c.extend(args.iter());
                c
            }
            MidExpr::Closure { body, .. } => vec![body],
            MidExpr::Let { value, body, .. } => vec![value, body],
            MidExpr::Thunk { body, .. } | MidExpr::Force { body, .. } => vec![body],
            MidExpr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => vec![condition, then_branch, else_branch],
            _ => vec![],
        }
    }

    let mut pending: Vec<&MidExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        // Check for f(f, ...) — first arg same as function
        if let MidExpr::Apply { function, args, .. } = current
            && !args.is_empty()
            && let (MidExpr::Var { var: fn_var, .. }, MidExpr::Var { var: arg_var, .. }) =
                (function.as_ref(), &args[0])
            && fn_var == arg_var
        {
            return true;
        }
        pending.extend(searched(current));
    }
    false
}

/// Tag the closure under a chain of thunks as recursive on `self_var`.
///
/// A loop, not tail recursion: the thunk chain is as deep as the script makes
/// it, and this walk carried NO `stacker` guard — a `(delay (delay …))` spine,
/// which costs half a byte per level to write, would have overflowed here.
fn mark_closure_recursive(expr: &mut MidExpr, self_var: VarId) {
    let mut current = expr;
    loop {
        match current {
            MidExpr::Closure { recursive, .. } => {
                *recursive = Some(self_var);
                return;
            }
            MidExpr::Thunk { body, .. } => current = body,
            _ => return,
        }
    }
}

// ===== Validator Parameter Seeding =====

/// Detect top-level lambda parameters and assign semantic roles based on Plutus version.
pub(crate) fn seed_validator_params(
    expr: &MidExpr,
    script_version: Option<crate::decompile::ScriptVersion>,
    var_registry: &mut super::var_registry::VarRegistry,
) {
    use crate::decompile::ScriptVersion;

    let version = match script_version {
        Some(v) => v,
        None => return,
    };

    // Collect top-level lambda params
    let mut params: Vec<&VarId> = Vec::new();
    let mut current = expr;
    while let MidExpr::Closure {
        params: ps, body, ..
    } = current
    {
        params.extend(ps.iter());
        current = body;
    }

    match version {
        ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2 => {
            // 3 params: datum, redeemer, script_context
            if params.len() >= 3 {
                var_registry.set_semantic_role(*params[params.len() - 3], "datum".to_string());
                var_registry.set_semantic_role(*params[params.len() - 2], "redeemer".to_string());
                var_registry
                    .set_semantic_role(*params[params.len() - 1], "script_context".to_string());
            }
        }
        ScriptVersion::PlutusV3 => {
            // 2 params: redeemer, script_context
            if params.len() >= 2 {
                var_registry.set_semantic_role(*params[params.len() - 2], "redeemer".to_string());
                var_registry
                    .set_semantic_role(*params[params.len() - 1], "script_context".to_string());
            }
        }
    }
}

// ===== Scott Encoding Pattern =====

/// Detect Scott-encoded pattern matching:
/// `Force(Apply(Force(scrutinee), [branch0, branch1, ...]))`
/// where branches are Thunk(body), Closure(params, body), or Error.
///
/// TAGS ARE POSITIONS: the minted `MidBranch::tag` is the continuation's
/// argument index, NOT a data constructor tag. For shape-keyed ADTs
/// (Option/Result — payload arity disambiguates) the two coincide closely
/// enough, but for nullary/nullary pairs they do NOT: a church bool
/// (`\t f -> t` = true, the `ifThenElse` continuation order) has True at
/// POSITION 0, while the data Bool table has False at TAG 0. Downstream
/// labeling must never feed these position tags into a data-tag table —
/// the Scott 2x0 case is labeled only via `bool_orientation` witnesses
/// (see `mid/bool_orientation.rs`).
fn try_recognize_scott_encoding(expr: &mut MidExpr, provenance: &mut ProvenanceBuilder) {
    // Pattern: Force { body: Apply { function: Force(scrutinee), args: branches } }
    let is_scott = matches!(expr, MidExpr::Force {
        body, ..
    } if matches!(body.as_ref(), MidExpr::Apply {
        function, args, ..
    } if args.len() >= 2 && matches!(function.as_ref(), MidExpr::Force { .. })));

    if !is_scott {
        return;
    }

    if let MidExpr::Force { id, body, .. } = expr
        && let MidExpr::Apply {
            id: apply_id,
            function,
            args,
            ..
        } = body.as_mut()
        && let MidExpr::Force {
            id: scrutinee_force_id,
            body: scrutinee,
            ..
        } = function.as_mut()
    {
        let all_branches = args.iter().all(is_scott_branch);
        if !all_branches || args.is_empty() {
            return;
        }

        let mid_id = *id;
        let scrutinee_expr = std::mem::replace(scrutinee.as_mut(), MidExpr::Error { id: mid_id });
        provenance.absorb_mid(scrutinee_expr.id(), *scrutinee_force_id);
        let branch_exprs: Vec<MidExpr> = std::mem::take(args);

        let branches: Vec<MidBranch> = branch_exprs
            .into_iter()
            .enumerate()
            .map(|(tag, arg)| {
                let (binders, body) = extract_scott_branch(arg, provenance);
                MidBranch { tag, binders, body }
            })
            .collect();

        *expr = MidExpr::Case {
            id: provenance.fresh_derived_from_many(&[mid_id, *apply_id]),
            scrutinee: Box::new(scrutinee_expr),
            branches,
            encoding: CaseEncoding::Scott,
        };
    }
}

/// Check if an expression looks like a Scott-encoded branch.
fn is_scott_branch(expr: &MidExpr) -> bool {
    matches!(
        expr,
        MidExpr::Thunk { .. } | MidExpr::Closure { .. } | MidExpr::Error { .. }
    ) || matches!(expr, MidExpr::Var { .. })
}

/// Extract binders and body from a Scott branch.
fn extract_scott_branch(
    expr: MidExpr,
    provenance: &mut ProvenanceBuilder,
) -> (Vec<VarId>, MidExpr) {
    match expr {
        // Thunk(body) → 0-field constructor
        MidExpr::Thunk { id, body, .. } => {
            let body = *body;
            provenance.absorb_mid(body.id(), id);
            (vec![], body)
        }
        // Closure(params, body) → N-field constructor with params as binders
        MidExpr::Closure {
            id, params, body, ..
        } => {
            // Unwrap inner Thunk if present: Closure(params, Thunk(body))
            let body = match *body {
                MidExpr::Thunk {
                    id: thunk_id,
                    body: inner,
                    ..
                } => {
                    let body = *inner;
                    provenance.absorb_mid(body.id(), thunk_id);
                    body
                }
                other => other,
            };
            provenance.absorb_mid(body.id(), id);
            (params, body)
        }
        // Error or Var — 0-field branch
        other => (vec![], other),
    }
}

// ===== AND / OR Pattern =====

/// AND/OR/NOT recognition for If expressions — currently a no-op.
/// AND: If(cond, then, Lit(Bool(false))) → the lowerer emits BinOp(And).
/// OR: If(cond, Lit(Bool(true)), else) → the lowerer emits BinOp(Or).
/// NOT: If(cond, Lit(Bool(false)), Lit(Bool(true))) → the lowerer emits Not.
///
/// `try_recognize_if_then_else` already produces all three shapes, so nothing
/// needs rewriting here; this is the hook for MIR-level boolean optimisation
/// such as constant-folding `And(true, x) → x`.
fn try_recognize_and_or(_expr: &mut MidExpr) {}

// ===== Helpers =====

fn unwrap_thunk(expr: MidExpr, removed_ids: &mut Vec<MidExprId>) -> MidExpr {
    let mut current = expr;
    loop {
        match current {
            MidExpr::Thunk { id, body, .. } => {
                removed_ids.push(id);
                current = *body;
            }
            other => return other,
        }
    }
}

fn unwrap_thunk_into_owner(expr: MidExpr, provenance: &mut ProvenanceBuilder) -> MidExpr {
    let mut removed_ids = Vec::new();
    let expr = unwrap_thunk(expr, &mut removed_ids);
    absorb_removed_mid_ids(expr.id(), removed_ids, provenance);
    expr
}

fn absorb_removed_mid_ids(
    target_id: MidExprId,
    removed_ids: impl IntoIterator<Item = MidExprId>,
    provenance: &mut ProvenanceBuilder,
) {
    for removed_id in removed_ids {
        provenance.absorb_mid(target_id, removed_id);
    }
}

fn unwrap_thunks_ref(expr: &MidExpr) -> &MidExpr {
    let mut current = expr;
    loop {
        match current {
            MidExpr::Thunk { body, .. } => current = body,
            other => return other,
        }
    }
}

#[cfg(test)]
mod tests;
