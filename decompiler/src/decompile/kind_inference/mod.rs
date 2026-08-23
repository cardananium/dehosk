//! VarKind verifier: re-derive specific `VarKind`s from PseudoExpr shapes
//! and report where they disagree with the mint-site annotations already
//! in the `VarTable`. Nothing here adds or overwrites metadata — the mint
//! sites in MIR-lower / simplify are the only populators.
//!
//! Kinds recognised, and the shape each is read from:
//!
//! `VarKind::FieldIndexAlias { parent, index }` — `let field_N =
//!   X.fields[N]`, minted by
//!   `simplify::let_binding::aliases::introduce_field_index_aliases`.
//! `VarKind::SliceTailAlias { parent, depth }` — `List.tail(...)` chains
//!   and alias propagation.
//! `VarKind::CallResult { callee }` — `let {fn}_result = fn(...)`.
//! `VarKind::DataLiteralHoist` — `let data_literal_N = <large static data
//!   literal>`.
//! `VarKind::CardanoContext { context_type }` — known Cardano context
//!   binder names.

use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::nameless::{VarKind, VarTable};
use crate::pseudo::var_id::VarId;

/// Result of a shape-based `VarKind` verification walk.
#[derive(Debug, Clone, Default)]
pub(crate) struct KindVerificationReport {
    /// Mint-site annotations whose kind disagrees with the inferred shape.
    pub(crate) conflicts: Vec<KindVerificationConflict>,
}

/// One conflict between an existing specific `VarKind` and an inferred kind.
#[derive(Debug, Clone)]
#[allow(dead_code)] // fields read only by tests
pub(crate) struct KindVerificationConflict {
    pub(crate) id: VarId,
    pub(crate) existing: VarKind,
    pub(crate) inferred: VarKind,
}

/// Walk `expr` and report disagreements with existing specific mint-site
/// annotations without overwriting or adding them.
pub(crate) fn verify_var_kinds(expr: &PseudoExpr, table: &VarTable) -> KindVerificationReport {
    let mut report = KindVerificationReport::default();
    walk(expr, table, &mut report);
    report
}

fn walk(expr: &PseudoExpr, table: &VarTable, report: &mut KindVerificationReport) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                // Pattern: `let field_N = parent.fields[N]`.
                if let Some((parent_id, index)) = extract_field_index_alias(name, value) {
                    verify_existing_kind(
                        table,
                        *id,
                        VarKind::FieldIndexAlias {
                            parent: parent_id,
                            index,
                        },
                        report,
                    );
                }
                // Pattern: `let X = List.tail(...List.tail(Y))`; the
                // depth accumulates through a Y that is itself a
                // SliceTailAlias.
                if let Some((parent_id, depth)) = extract_slice_tail_alias(value, table) {
                    verify_existing_kind(
                        table,
                        *id,
                        VarKind::SliceTailAlias {
                            parent: parent_id,
                            depth,
                        },
                        report,
                    );
                }
                // Pattern: `let data_literal_N = <large static data
                // literal>`.
                if is_data_literal_hoist(name, value) {
                    verify_existing_kind(table, *id, VarKind::DataLiteralHoist, report);
                }
                // Pattern: `let {fn}_result = Apply(Var(callee), ...)`
                // where the binder name's stem matches `callee`.
                if let Some(callee_id) = extract_call_result(name, value) {
                    verify_existing_kind(
                        table,
                        *id,
                        VarKind::CallResult { callee: callee_id },
                        report,
                    );
                }
                // Pattern: binder named after a well-known Cardano
                // context type (script_context, tx_info, …).
                if let Some(ctx_type) = recognize_cardano_context_name(name) {
                    verify_existing_kind(
                        table,
                        *id,
                        VarKind::CardanoContext {
                            context_type: ctx_type.to_string(),
                        },
                        report,
                    );
                }
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { params, body } => {
                for binder in params {
                    tag_param_if_cardano_context(binder, table, report);
                }
                pending.push(body);
            }
            PseudoExpr::RecFn { params, body, .. } => {
                for binder in params {
                    tag_param_if_cardano_context(binder, table, report);
                }
                pending.push(body);
            }
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
                pending.push(function);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
                pending.push(condition);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for clause in clauses.iter().rev() {
                    pending.push(&clause.body);
                    if let Some(g) = &clause.guard {
                        pending.push(g);
                    }
                }
                pending.push(subject);
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    pending.push(t);
                }
                for e in elements.iter().rev() {
                    pending.push(e);
                }
            }
            PseudoExpr::Tuple(items) => {
                for i in items.iter().rev() {
                    pending.push(i);
                }
            }
            PseudoExpr::Pair(a, b) => {
                pending.push(b);
                pending.push(a);
            }
            PseudoExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    pending.push(f);
                }
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            PseudoExpr::Var { .. }
            | PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
        }
    }
}

fn verify_existing_kind(
    table: &VarTable,
    id: Option<VarId>,
    kind: VarKind,
    report: &mut KindVerificationReport,
) {
    let Some(id) = id else {
        return;
    };
    if let Some(existing) = table.get(id).map(|m| m.kind.clone())
        && is_specific_kind(&existing)
        && existing != kind
        && !is_compatible_refinement(&existing, &kind)
    {
        report.conflicts.push(KindVerificationConflict {
            id,
            existing,
            inferred: kind,
        });
    }
}

/// A Cardano naming pass may rename a `FieldIndexAlias` binder to a
/// context name (e.g. `tx_info`), leaving the mint-time kind
/// structurally correct while the verifier infers `CardanoContext`
/// from the new name. Both describe the same binder, so this is a
/// refinement, not a conflict.
fn is_compatible_refinement(existing: &VarKind, inferred: &VarKind) -> bool {
    matches!(
        (existing, inferred),
        (
            VarKind::FieldIndexAlias { .. },
            VarKind::CardanoContext { .. }
        )
    )
}

fn is_specific_kind(kind: &VarKind) -> bool {
    matches!(
        kind,
        VarKind::FieldIndexAlias { .. }
            | VarKind::SliceTailAlias { .. }
            | VarKind::CallResult { .. }
            | VarKind::DataLiteralHoist
            | VarKind::CardanoContext { .. }
            | VarKind::ConstrPayload { .. }
    )
}

/// Recognise `let field_N = parent.fields[N]`:
///
/// `IndexAccess { collection: FieldAccess { record: Var(parent),
/// selector: NamedField("fields") }, index: N }`
///
/// Returns `(parent_var_id, index)`. The binder name must follow
/// the `field_N` convention so user bindings of the same shape
/// are not matched.
fn extract_field_index_alias(name: &str, value: &PseudoExpr) -> Option<(VarId, usize)> {
    let suffix = name.strip_prefix("field_")?;
    if suffix.is_empty() || !suffix.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }

    let PseudoExpr::IndexAccess { collection, index } = value else {
        return None;
    };
    let PseudoExpr::FieldAccess { record, selector } = collection.as_ref() else {
        return None;
    };
    if !matches!(selector, FieldSelector::NamedField(s) if s == "fields") {
        return None;
    }
    let PseudoExpr::Var { id: parent_id, .. } = record.as_ref() else {
        return None;
    };

    Some(((*parent_id)?, *index))
}

/// Recognise `Apply(BuiltinCall("List.tail", []), [arg])` as one
/// slice step; returns the stripped arg.
fn strip_one_list_tail(expr: &PseudoExpr) -> Option<&PseudoExpr> {
    let PseudoExpr::Apply { function, args } = expr else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    let PseudoExpr::BuiltinCall {
        name,
        args: builtin_args,
    } = function.as_ref()
    else {
        return None;
    };
    if *name == crate::BuiltinId::ListTail && builtin_args.is_empty() {
        Some(&args[0])
    } else {
        None
    }
}

/// Recognise `let X = List.tail(...)` chains, possibly bottoming
/// out at a Var already tagged `SliceTailAlias`. Returns
/// `(parent_var_id, depth)`, where depth counts every
/// `List.tail` application **including** the depth carried by
/// that Var.
fn extract_slice_tail_alias(value: &PseudoExpr, table: &VarTable) -> Option<(VarId, usize)> {
    let mut current = value;
    let mut depth = 0usize;
    while let Some(inner) = strip_one_list_tail(current) {
        depth += 1;
        current = inner;
    }
    // Alias propagation `let Y = X`: no `List.tail` peeled, so
    // inherit parent and depth from X's SliceTailAlias.
    if depth == 0 {
        if let PseudoExpr::Var { id, .. } = current {
            let id = (*id)?;
            if let Some(VarKind::SliceTailAlias {
                parent,
                depth: existing_depth,
            }) = table.get(id).map(|m| &m.kind)
            {
                return Some((*parent, *existing_depth));
            }
        }
        return None;
    }
    // Resolve the bottom: if it's a Var that's already a slice
    // alias, accumulate depth + parent.
    match current {
        PseudoExpr::Var { id, .. } => {
            let id = (*id)?;
            if let Some(VarKind::SliceTailAlias {
                parent,
                depth: existing_depth,
            }) = table.get(id).map(|m| &m.kind)
            {
                Some((*parent, depth + existing_depth))
            } else {
                Some((id, depth))
            }
        }
        _ => None,
    }
}

/// Recognise `let data_literal_N = <large static data literal>`
/// shapes minted by
/// `simplify::apply::hoist::hoist_large_data_literals_from_apply_args`.
///
/// Requires both a `data_literal_N` binder name (so user bindings
/// are not matched) and a value that is static data all the way
/// down (Int/ByteArray/String/Bool/Unit/Data/List/Tuple/Pair/
/// Constr/`BuiltinCall("Data.Constr")`) of node count > 8, the
/// hoister's threshold.
fn is_data_literal_hoist(name: &str, value: &PseudoExpr) -> bool {
    let suffix = match name.strip_prefix("data_literal_") {
        Some(s) => s,
        None => return false,
    };
    if suffix.is_empty() || !suffix.chars().all(|c| c.is_ascii_digit()) {
        return false;
    }
    static_data_expr_node_count(value).is_some_and(|n| n > 8)
}

/// Recognise binder names that match a well-known Cardano
/// context type. Returns the canonical legacy name.
///
/// The list mirrors `ContextType::display_name` and the
/// `SumTypeId::display_name` set in
/// `simplify::postprocess::context_schema`. Anchoring on the
/// final binder name rather than re-running the Cardano
/// type-propagation walk is conservative: only bindings the
/// schema-aware naming pass already named are matched.
fn recognize_cardano_context_name(name: &str) -> Option<&'static str> {
    match name {
        // ContextType::display_name
        "script_context" => Some("script_context"),
        "tx_info" => Some("tx_info"),
        "tx_in_info" => Some("tx_in_info"),
        "tx_out" => Some("tx_out"),
        "tx_out_ref" => Some("tx_out_ref"),
        "address" => Some("address"),
        "interval" => Some("interval"),
        "lower_bound" => Some("lower_bound"),
        "upper_bound" => Some("upper_bound"),
        // SumTypeId::display_name
        "purpose" => Some("purpose"),
        "script_info" => Some("script_info"),
        "credential" => Some("credential"),
        "output_datum" => Some("output_datum"),
        "interval_bound_type" => Some("interval_bound_type"),
        "certificate" => Some("certificate"),
        "voter" => Some("voter"),
        "drep" => Some("drep"),
        "governance_action" => Some("governance_action"),
        "vote" => Some("vote"),
        _ => None,
    }
}

/// Verify a Lambda/RecFn parameter binder whose name matches a known
/// context type against its existing `VarKind::CardanoContext`.
fn tag_param_if_cardano_context(
    binder: &crate::pseudo::ast::Binder,
    table: &VarTable,
    report: &mut KindVerificationReport,
) {
    if let Some(ctx_type) = recognize_cardano_context_name(&binder.name) {
        verify_existing_kind(
            table,
            binder.id.get(),
            VarKind::CardanoContext {
                context_type: ctx_type.to_string(),
            },
            report,
        );
    }
}

/// Recognise `let {fn}_result = Apply(Var(callee), ...)` shapes
/// minted by `simplify::helpers::naming::suggest_generated_binding_name`.
/// Returns the callee's `VarId`.
///
/// Gates mirroring the mint site: the binder name ends in `_result`,
/// its sanitized stem equals the sanitized callee name, the Apply has
/// at least one argument, and the callee is not a bare generic helper
/// (`f`, `f_2`, `expect!*`) — those are skipped at the mint site to
/// avoid orphan-prone `f_N_result_M` aliases.
fn extract_call_result(name: &str, value: &PseudoExpr) -> Option<VarId> {
    let stem = name.strip_suffix("_result")?;
    if stem.is_empty() {
        return None;
    }
    let PseudoExpr::Apply { function, args } = value else {
        return None;
    };
    if args.is_empty() {
        return None;
    }
    let PseudoExpr::Var {
        name: fn_name,
        id: callee_id,
    } = function.as_ref()
    else {
        return None;
    };
    if is_bare_generic_fn_name(fn_name) || fn_name.starts_with("expect!") {
        return None;
    }
    let stem_norm = sanitize_name_stem_local(stem);
    let fn_norm = sanitize_name_stem_local(fn_name);
    if stem_norm != fn_norm {
        return None;
    }
    *callee_id
}

/// Local copy of `sanitize_name_stem` from
/// `simplify::helpers::readability`, too small to share.
fn sanitize_name_stem_local(name: &str) -> String {
    let mut out = String::new();
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
        } else if ch == '_' && !out.ends_with('_') {
            out.push('_');
        }
    }
    out = out.trim_matches('_').to_string();
    if out.is_empty() {
        return out;
    }
    if out
        .chars()
        .next()
        .map(|c| c.is_ascii_digit())
        .unwrap_or(false)
    {
        out.insert(0, 'c');
    }
    out
}

/// Recognise bare generic helper names like `f`, `f_2`,
/// `rec_fn_3`, `self_fn_4`. Mirrors `is_bare_generic_fn_name` in
/// `simplify::helpers::naming`, which skips these at the
/// `{fn}_result` mint site.
fn is_bare_generic_fn_name(name: &str) -> bool {
    if name == "f" {
        return true;
    }
    if let Some(rest) = name.strip_prefix("f_")
        && !rest.is_empty()
        && rest.chars().all(|c| c.is_ascii_digit())
    {
        return true;
    }
    if let Some(suffix) = name
        .strip_prefix("rec_fn_")
        .or_else(|| name.strip_prefix("self_fn_"))
    {
        return !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit());
    }
    false
}

/// Pure-function copy of
/// `simplify::helpers::readability::static_data_expr_node_count`.
/// Returns `None` if the expression contains any non-static node
/// (Var, Lambda, Apply, etc.), `Some(node_count)` otherwise.
fn static_data_expr_node_count(expr: &PseudoExpr) -> Option<usize> {
    let mut pending = vec![expr];
    let mut total = 0usize;
    while let Some(expr) = pending.pop() {
        match expr {
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit => total += 1,

            PseudoExpr::Data(_) => total += 1,
            // A `HelperSymbol` (`fix`) is a function-valued intrinsic, not
            // static data.
            PseudoExpr::HelperSymbol(_) => return None,

            PseudoExpr::List { elements, tail } => {
                if tail.is_some() {
                    return None;
                }
                total += 1;
                pending.extend(elements);
            }
            PseudoExpr::Tuple(items) => {
                total += 1;
                pending.extend(items);
            }
            PseudoExpr::Pair(a, b) => {
                total += 1;
                pending.push(a);
                pending.push(b);
            }
            PseudoExpr::Constr { fields, .. } => {
                total += 1;
                pending.extend(fields);
            }
            PseudoExpr::BuiltinCall { name, args } if *name == crate::BuiltinId::DataConstr => {
                total += 1;
                pending.extend(args);
            }
            _ => return None,
        }
    }
    Some(total)
}

#[cfg(test)]
mod tests;
