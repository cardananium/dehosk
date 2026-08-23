//! Source-span bookkeeping and hidden-chain node-id collection helpers.
//!
//! The renderer in `pretty.rs` translates byte offsets in the emitted
//! text back into `SourceSpan` line/column ranges, maps every
//! `PseudoExpr` node to a stable `PseudoNodeId` via provenance, and
//! collects the ids of the "hidden" interior nodes a flattened chain
//! (seq/expect!/List.tail/if/delay-force/nested-let) omits from output;
//! those ids attach to the flattened parent so span lookups resolve.

use crate::decompile::render::helpers::traversal::is_expect_bang;
use crate::pseudo::ast::{PseudoExpr, PseudoNodeId};
use crate::pseudo::mid::expr_id::SourceSpan;
use std::collections::HashMap;

/// Byte offset at which each line of `source` begins.
///
/// A trailing newline TERMINATES the last line; it does not open another,
/// so the naive "one entry per `\n`, plus 0" table is wrong: its phantom
/// entry at `source.len()` is a line `source.lines()` does not count, and
/// any offset at the end of the document then numbers one line past the
/// text — a position no consumer showing a span's START can resolve.
/// Omitting it keeps `line_starts.len()` equal to
/// `source.lines().count()` for any non-empty source.
pub(in crate::decompile::render) fn collect_line_starts(source: &str) -> Vec<usize> {
    let mut line_starts = vec![0];

    for (offset, byte) in source.bytes().enumerate() {
        if byte == b'\n' && offset + 1 < source.len() {
            line_starts.push(offset + 1);
        }
    }

    line_starts
}

pub(in crate::decompile::render) fn byte_range_to_span(
    line_starts: &[usize],
    source_len: usize,
    start: usize,
    end: usize,
) -> SourceSpan {
    let (start_line, start_col) = byte_offset_to_line_col(line_starts, source_len, start);
    let (end_line, end_col) = if end > start {
        byte_offset_to_line_col(line_starts, source_len, end - 1)
    } else {
        (start_line, start_col)
    };

    SourceSpan {
        start_line,
        start_col,
        end_line,
        end_col,
    }
}

fn byte_offset_to_line_col(line_starts: &[usize], source_len: usize, offset: usize) -> (u32, u32) {
    let limit = offset.min(source_len);
    let line_index = line_starts.partition_point(|line_start| *line_start <= limit) - 1;
    let line_start = line_starts[line_index];

    ((line_index + 1) as u32, (limit - line_start + 1) as u32)
}

pub(in crate::decompile::render) fn collect_node_ids(
    expr: &PseudoExpr,
) -> HashMap<usize, PseudoNodeId> {
    let mut node_ids = HashMap::new();
    let mut stack = vec![(expr, PseudoExpr::provenance_root_path_hash())];

    while let Some((node, path_hash)) = stack.pop() {
        node_ids.insert(
            node as *const PseudoExpr as usize,
            node.provenance_node_id_from_path_hash(path_hash),
        );

        let children = node.provenance_children();
        for (index, child) in children.into_iter().enumerate().rev() {
            stack.push((
                child,
                PseudoExpr::provenance_child_path_hash(path_hash, index as u32),
            ));
        }
    }

    node_ids
}

pub(in crate::decompile::render) fn node_id_for(
    expr: &PseudoExpr,
    node_ids: &HashMap<usize, PseudoNodeId>,
) -> Option<PseudoNodeId> {
    node_ids.get(&(expr as *const PseudoExpr as usize)).copied()
}

pub(in crate::decompile::render) fn collect_hidden_seq_chain_node_ids(
    expr: &PseudoExpr,
    node_ids: &HashMap<usize, PseudoNodeId>,
) -> Vec<PseudoNodeId> {
    let mut hidden = Vec::new();
    let mut current = expr;
    let mut first = true;

    loop {
        match current {
            PseudoExpr::BuiltinCall { name, args }
                if *name == crate::BuiltinId::Seq && args.len() == 2 =>
            {
                if !first && let Some(node_id) = node_id_for(current, node_ids) {
                    hidden.push(node_id);
                }
                current = &args[1];
                first = false;
            }
            PseudoExpr::Apply { function, args }
                if args.len() == 2
                    && matches!(
                        function.as_ref(),
                        PseudoExpr::BuiltinCall { name, args: builtin_args }
                            if *name == crate::BuiltinId::Seq && builtin_args.is_empty()
                    ) =>
            {
                if !first && let Some(node_id) = node_id_for(current, node_ids) {
                    hidden.push(node_id);
                }
                current = &args[1];
                first = false;
            }
            _ => return hidden,
        }
    }
}

pub(in crate::decompile::render) fn collect_hidden_expect_chain_node_ids(
    expr: &PseudoExpr,
    node_ids: &HashMap<usize, PseudoNodeId>,
) -> Vec<PseudoNodeId> {
    let mut hidden = Vec::new();
    let mut current = expr;
    let mut first = true;

    loop {
        match current {
            PseudoExpr::Apply { function, args }
                if is_expect_bang(function.as_ref()) && (args.len() == 2 || args.len() == 3) =>
            {
                if !first && let Some(node_id) = node_id_for(current, node_ids) {
                    hidden.push(node_id);
                }
                current = &args[1];
                first = false;
            }
            _ => return hidden,
        }
    }
}

pub(in crate::decompile::render) fn collect_hidden_tail_chain_node_ids(
    expr: &PseudoExpr,
    node_ids: &HashMap<usize, PseudoNodeId>,
) -> Vec<PseudoNodeId> {
    let mut hidden = Vec::new();
    let mut current = expr;

    loop {
        match current {
            PseudoExpr::BuiltinCall { name, args }
                if *name == crate::BuiltinId::ListTail && args.len() == 1 =>
            {
                if let Some(node_id) = node_id_for(current, node_ids) {
                    hidden.push(node_id);
                }
                current = &args[0];
            }
            PseudoExpr::Apply { function, args }
                if args.len() == 1
                    && matches!(
                        function.as_ref(),
                        PseudoExpr::BuiltinCall { name, args: builtin_args }
                            if *name == crate::BuiltinId::ListTail && builtin_args.is_empty()
                    ) =>
            {
                if let Some(node_id) = node_id_for(current, node_ids) {
                    hidden.push(node_id);
                }
                current = &args[0];
            }
            _ => return hidden,
        }
    }
}

pub(in crate::decompile::render) fn collect_hidden_if_chain_node_ids(
    expr: &PseudoExpr,
    node_ids: &HashMap<usize, PseudoNodeId>,
) -> Vec<PseudoNodeId> {
    let mut hidden = Vec::new();
    let mut current = expr;

    while let PseudoExpr::If { else_branch, .. } = current {
        if let Some(node_id) = node_id_for(current, node_ids) {
            hidden.push(node_id);
        }
        current = else_branch.as_ref();
    }

    hidden
}

pub(in crate::decompile::render) fn collect_hidden_delay_force_chain_node_ids(
    expr: &PseudoExpr,
    node_ids: &HashMap<usize, PseudoNodeId>,
) -> Vec<PseudoNodeId> {
    let mut hidden = Vec::new();
    let mut current = expr;
    let mut first = true;

    loop {
        match current {
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                if !first && let Some(node_id) = node_id_for(current, node_ids) {
                    hidden.push(node_id);
                }
                current = inner.as_ref();
                first = false;
            }
            _ => return hidden,
        }
    }
}

pub(in crate::decompile::render) fn collect_hidden_nested_let_node_ids(
    expr: &PseudoExpr,
    node_ids: &HashMap<usize, PseudoNodeId>,
) -> Vec<PseudoNodeId> {
    let mut hidden = Vec::new();
    let mut current = expr;

    while let PseudoExpr::Let { value, .. } = current {
        if let Some(node_id) = node_id_for(current, node_ids) {
            hidden.push(node_id);
        }
        current = value.as_ref();
    }

    hidden
}
