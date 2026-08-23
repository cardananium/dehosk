//! Post-processing naming and naming-adjacent analysis.
use crate::decompile::constructor_data::{
    extract_standard_option_some_fields, is_bool_false_like, is_bool_true_like,
    is_standard_option_none_candidate, is_standard_option_some_candidate,
};
use crate::decompile::helper::hoist::var_is_referenced_id_aware;
use crate::decompile::list_traversal::list_cons_parts;
use crate::decompile::pair_patterns::body_contains_pair_field_access;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::fold::{ExprFolder, ExprVisitor};
use crate::pseudo::var_id::VarId;
use std::collections::HashMap;
use std::collections::HashSet;

const DATA_BYTES_EXTRACTORS: &[&str] = &["Data.to_bytes", "Data.un_bytearray"];
const DATA_INT_EXTRACTORS: &[&str] = &["Data.to_int", "Data.un_int"];
const DATA_LIST_EXTRACTORS: &[&str] = &["Data.to_list", "Data.un_list"];
const DATA_MAP_EXTRACTORS: &[&str] = &["Data.to_map", "Data.un_map"];

// ============================================================
// Better Variable Naming
// ============================================================

/// Improve generic variable names based on body analysis.
///
/// Scans the AST for `let name = fn(...) { body }` and
/// `let name = rec fn ...` bindings, analyses their body to
/// generate a descriptive name, then applies the rename map
/// across the whole tree in a single pass.
pub(crate) fn improve_variable_names(expr: PseudoExpr) -> PseudoExpr {
    semantic_improve_variable_names(expr)
}

/// Semantic naming pass, run while later rewrites still depend on
/// stable display names.
pub(crate) fn semantic_improve_variable_names(expr: PseudoExpr) -> PseudoExpr {
    improve_variable_names_impl(expr, NamingPhase::Semantic)
}

/// Render-facing naming pass used after structural recovery and display
/// rewrites have established their final user-facing shape.
pub(crate) fn render_improve_variable_names(expr: PseudoExpr) -> PseudoExpr {
    improve_variable_names_impl(expr, NamingPhase::Render)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NamingPhase {
    Semantic,
    Render,
}

/// Shared implementation behind the semantic and render-facing wrappers.
/// `phase` is threaded through so a heuristic can become phase-specific
/// without adding another public entry point. Rename decisions use
/// body-based heuristics only — no type environment.
fn improve_variable_names_impl(expr: PseudoExpr, phase: NamingPhase) -> PseudoExpr {
    let mut rename_map: HashMap<String, String> = HashMap::new();
    let mut fallback_rename_map: HashMap<String, String> = HashMap::new();
    let mut let_rename_map: HashMap<VarId, String> = HashMap::new();
    let mut binder_rename_map: HashMap<VarId, String> = HashMap::new();
    let mut used_names: HashSet<String> = HashSet::new();

    collect_all_names(&expr, &mut used_names);

    scan_for_renames(
        &expr,
        &mut rename_map,
        &mut fallback_rename_map,
        &mut let_rename_map,
        &mut binder_rename_map,
        &mut used_names,
        phase,
    );

    if rename_map.is_empty() && let_rename_map.is_empty() && binder_rename_map.is_empty() {
        return expr;
    }

    // Refs whose nearest same-name binder shares their VarId are
    // the only ones the name-keyed rename may follow; the rest
    // would go dangling.
    let consistent_ref_ids = collect_consistent_ref_ids(&expr);

    let mut renamer = MapRenamer {
        fallback_rename_map: &fallback_rename_map,
        let_rename_map: &let_rename_map,
        binder_rename_map: &binder_rename_map,
        consistent_ref_ids: &consistent_ref_ids,
    };
    renamer.fold(expr)
}

mod hint_collection;
pub(crate) use hint_collection::*;
mod rename_scan;
use rename_scan::*;
mod binding_analysis;
use binding_analysis::*;
mod name_shapes;
pub(crate) use name_shapes::*;
mod function_body;
use function_body::*;
mod fold_map;
use fold_map::*;
mod list_recursion;
use list_recursion::*;
mod assoc_lookup;
use assoc_lookup::*;
mod list_shapes;
use list_shapes::*;
mod trace_hints;
use trace_hints::*;
mod when_body;
pub(crate) use when_body::*;
mod body_probes;
use body_probes::*;
mod map_renamer;
use map_renamer::*;

#[cfg(test)]
mod tests;
