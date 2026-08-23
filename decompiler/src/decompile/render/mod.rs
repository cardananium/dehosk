//! Pretty printing for PseudoExpr: high-level pseudocode.

pub(crate) mod helpers;
pub(crate) mod pattern;

use crate::builtins::{BuiltinDisplayStyle, BuiltinId};
use crate::decompile::BlueprintHintRegistry;
use crate::decompile::final_type_table::FinalTypeTable;
use crate::pseudo::ast::{
    BinaryOp, Binder, PseudoData, PseudoExpr, PseudoNodeId, PseudoType, UnaryOp, WhenClause,
    WhenPattern,
};
#[cfg(test)]
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::mid::expr_id::SourceSpan;
use crate::pseudo::root_layout::{
    RootHelper, RootLambdaWithHelpers, RootParameter, RootParametrizedScript, RootRenderLayout,
    prepare_root_render_layout, uses_var_as_control_subject,
};
use crate::pseudo::var_id::VarId;
use helpers::dispatch::{
    extract_expect_fail_message, extract_expect_pattern, when_subject_name_matches,
};
use helpers::formatting::{escape_string, format_byte_array};
use helpers::optional::{collect_expect_sugar_positions, try_match_sorted_assoc_lookup_if};
use helpers::sizing::{
    renders_as_statement_sequence, should_force_multiline_call_args, should_inline_let_value,
    should_multiline_delay_force_body, value_renders_as_function,
};
use helpers::spans::{
    byte_range_to_span, collect_hidden_delay_force_chain_node_ids,
    collect_hidden_expect_chain_node_ids, collect_hidden_if_chain_node_ids,
    collect_hidden_nested_let_node_ids, collect_hidden_seq_chain_node_ids,
    collect_hidden_tail_chain_node_ids, collect_line_starts, collect_node_ids, node_id_for,
};
use helpers::traversal::{
    collect_expect_chain, collect_logical_chain, collect_nested_let_bindings, collect_seq_chain,
    count_tail_chain_any, flatten_if_chain, is_expect_bang,
};
use pretty::{Arena, DocAllocator, DocBuilder, Render, RenderAnnotated};
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

/// Render a type for `: <type>` annotation contexts.
///
/// Identical to `PseudoType::Display` except under
/// `PseudoType::Function`, where nested `Unknown` params/ret render as
/// `_` rather than `Data`, so a partially-Unknown signature reads
/// `fn(_) -> _` instead of the meaningless `fn(Data) -> Data`. Outside
/// a `Function`, `Unknown` still renders as `"Data"` — the implicit
/// default `resolve_type` suppresses.
fn format_type_for_annotation(ty: &PseudoType) -> String {
    fn contains_function(ty: &PseudoType) -> bool {
        match ty {
            PseudoType::Function { .. } => true,
            PseudoType::List(inner) | PseudoType::Option(inner) => contains_function(inner),
            PseudoType::Tuple(items) => items.iter().any(|t| contains_function(t)),
            PseudoType::Pair(a, b) => contains_function(a) || contains_function(b),
            PseudoType::Result(ok, err) => contains_function(ok) || contains_function(err),
            _ => false,
        }
    }

    fn write_underscore_for_unknown(ty: &PseudoType, out: &mut String) {
        use std::fmt::Write as _;
        match ty {
            PseudoType::Function { params, ret } => {
                out.push_str("fn(");
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    write_underscore_for_unknown(p.as_ref(), out);
                }
                out.push_str(") -> ");
                write_underscore_for_unknown(ret.as_ref(), out);
            }
            PseudoType::Unknown => out.push('_'),
            // Recurse through wrappers so a nested Function still
            // gets its Unknowns rendered as `_`.
            PseudoType::List(inner) => {
                out.push_str("List<");
                write_underscore_for_unknown(inner.as_ref(), out);
                out.push('>');
            }
            PseudoType::Option(inner) => {
                out.push_str("Option<");
                write_underscore_for_unknown(inner.as_ref(), out);
                out.push('>');
            }
            PseudoType::Tuple(items) => {
                out.push('(');
                for (i, t) in items.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    write_underscore_for_unknown(t.as_ref(), out);
                }
                out.push(')');
            }
            PseudoType::Pair(a, b) => {
                out.push_str("Pair<");
                write_underscore_for_unknown(a.as_ref(), out);
                out.push_str(", ");
                write_underscore_for_unknown(b.as_ref(), out);
                out.push('>');
            }
            PseudoType::Result(ok, err) => {
                out.push_str("Result<");
                write_underscore_for_unknown(ok.as_ref(), out);
                out.push_str(", ");
                write_underscore_for_unknown(err.as_ref(), out);
                out.push('>');
            }
            other => {
                let _ = write!(out, "{}", other);
            }
        }
    }

    // Fast-path: with no Function anywhere in `ty`, `Display` is
    // correct: `Unknown → "Data"` is the implicit default. Recurse
    // through Function-aware printing only when it can differ.
    if contains_function(ty) {
        let mut out = String::new();
        write_underscore_for_unknown(ty, &mut out);
        return out;
    }
    ty.to_string()
}

/// True when the binder's name already conveys the church-decode tag
/// and the trailing `// church-X` comment would add nothing:
/// `pair_pack` for tag "church-pair", `pack_10` for "church-pack-10",
/// `church_cons` for "church-cons". A name without the tag's keyword
/// (`match_subject_9` with tag `identity`) keeps the comment.
fn is_church_tag_redundant(name: &str, tag: &str) -> bool {
    let name_l = name.to_ascii_lowercase();
    let keyword = tag.strip_prefix("church-").unwrap_or(tag);

    // Direct substring on the keyword as-is.
    if name_l.contains(keyword) {
        return true;
    }
    // Try `-` → `_` for multi-word tags ("always-fail" → "always_fail").
    let underscore_form = keyword.replace('-', "_");
    if underscore_form != keyword && name_l.contains(&underscore_form) {
        return true;
    }
    // For "pack-N", also accept "pack_N" form (the existing helper-naming
    // convention emits `pack_10`, `pack_3`).
    if let Some(n) = keyword.strip_prefix("pack-")
        && name_l.contains(&format!("pack_{}", n))
    {
        return true;
    }
    // For multi-word tags, check each sub-word (≥4 chars) as a fallback —
    // e.g. "always-fail" matches a name containing "fail".
    if keyword.contains('-') {
        for word in keyword.split('-') {
            if word.len() >= 4 && name_l.contains(word) {
                return true;
            }
        }
    }
    false
}

/// True for `Option<Option<X>>`, nearly always an inference artifact:
/// Bool literals share Constr-tag-0 encoding with `None`, so a `when`
/// arm returning `False` under an already-inferred `Option<X>`
/// double-wraps the binding even though the value is not nested.
fn is_nested_option(ty: &PseudoType) -> bool {
    if let PseudoType::Option(inner) = ty
        && matches!(inner.as_ref(), PseudoType::Option(_))
    {
        return true;
    }
    false
}

/// True when `ty` would render as `fn(_, ..., _) -> _`: a `Function`
/// whose every param is `Unknown`/`Data` and whose return is likewise
/// an Unknown/Data leaf or a recursively-uninformative `Function` (so
/// curried `fn(_) -> fn(_) -> _` counts). Anything concrete —
/// `fn(Int) -> _`, `fn(_) -> Int`, even `fn(_) -> List<_>` — is false.
/// Such an annotation says only "this is a function", which the
/// surface form already shows, so the let-binder and param gates drop
/// it.
fn is_uninformative_function_type(ty: &PseudoType) -> bool {
    let PseudoType::Function { params, ret } = ty else {
        return false;
    };
    // Recursion covers higher-order params too, e.g.
    // `fn(fn(_, _) -> _) -> _`.
    if !params.iter().all(|p| is_uninformative_or_leaf(p.as_ref())) {
        return false;
    }
    is_uninformative_or_leaf(ret.as_ref())
}

fn is_uninformative_or_leaf(t: &PseudoType) -> bool {
    matches!(t, PseudoType::Unknown | PseudoType::Data) || is_uninformative_function_type(t)
}

/// `true` if `value` is structurally something that can NEVER be a function —
/// a data aggregate (`Pair`/`Tuple`/`List`/`Constr`) or a scalar/Data literal.
///
/// Used to drop a `fn(..) -> ..` annotation the solver mis-inferred onto such
/// a binding (`let f_30: fn(_) -> _ = Pair(..)`). Everything that could be or
/// return a function is EXCLUDED — `Var`, `Apply`, `FieldAccess`/`IndexAccess`
/// (`pair_of_fns.fst` IS a function), `Lambda`/`RecFn`, `When`/`If`, `Force`,
/// `BuiltinCall` — so a genuine function annotation is never dropped.
fn value_is_definitely_not_function(value: &PseudoExpr) -> bool {
    if is_structural_fail_label(value) {
        return true;
    }
    matches!(
        value,
        PseudoExpr::Pair(..)
            | PseudoExpr::Tuple(..)
            | PseudoExpr::List { .. }
            | PseudoExpr::Constr { .. }
            | PseudoExpr::Int(..)
            | PseudoExpr::ByteArray(..)
            | PseudoExpr::String(..)
            | PseudoExpr::Bool(..)
            | PseudoExpr::Unit
            | PseudoExpr::Data(..)
    )
}

/// An `Error{..}` value, possibly behind `Trace`/`Delay`/`Force` wrappers
/// (`fail @"msg"` and its traced/delayed spellings). The solver types an
/// APPLIED fail-label binder as a function (`const a: fn(Bool) -> _ =
/// fail @"PT1"`), but such a value provably diverges and is never a
/// function. Only an innermost stripped expr that is exactly `Error`
/// qualifies — a `Trace` around a real lambda stays annotatable.
fn is_structural_fail_label(value: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![value];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Error { .. } => return true,
            PseudoExpr::Trace { value, .. } => pending.push(value),
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            _ => {}
        }
    }
    false
}

/// Does a fn body whose resolved return annotation says `Bool` PROVABLY
/// return a non-Bool? Return-leaf walk: `||`/`&&` return one operand, so
/// both recurse; comparison operators are opaque Bool leaves (their operands
/// are not return values); a raw `Constr` leaf not Known(True/False) —
/// directly or via a binding in `non_bool_constr_bindings` (`const d =
/// Unknown_E_0_1` reached via `x == y || d`) — contradicts the annotation.
/// Fail-closed: only an explicit non-bool constructor proof suppresses.
fn bool_return_annotation_contradicted(
    body: &PseudoExpr,
    non_bool_constr_bindings: &std::collections::HashSet<VarId>,
) -> bool {
    use crate::pseudo::ast::BinaryOp;
    use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
    let mut pending: Vec<&PseudoExpr> = vec![body];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Let { body, .. } => pending.push(body),
            PseudoExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
            }
            PseudoExpr::When { clauses, .. } => {
                for cl in clauses.iter().rev() {
                    pending.push(&cl.body);
                }
            }
            PseudoExpr::Trace { value, .. } => pending.push(value),
            PseudoExpr::Apply { function, args }
                if matches!(
                    function.as_ref(),
                    PseudoExpr::Var { name, .. } if name == "expect!"
                ) && args.len() >= 2 =>
            {
                pending.push(&args[1]);
            }
            PseudoExpr::BinOp {
                op: BinaryOp::Or | BinaryOp::And,
                left,
                right,
            } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::Constr { shape, .. } => {
                if !matches!(
                    shape,
                    ConstructorShape::Known(KnownConstructor::True)
                        | ConstructorShape::Known(KnownConstructor::False)
                ) {
                    return true;
                }
            }
            PseudoExpr::Var { id: Some(vid), .. } => {
                if non_bool_constr_bindings.contains(vid) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// Binders whose `let` value is a `Constr` that is NOT Known(True/False)
/// — the lookup set for [`bool_return_annotation_contradicted`]'s
/// `Var`-leaf case.
fn collect_non_bool_constr_bindings(expr: &PseudoExpr) -> std::collections::HashSet<VarId> {
    use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
    let mut out = std::collections::HashSet::new();
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(e) = pending.pop() {
        if let PseudoExpr::Let {
            id: Some(vid),
            value,
            ..
        } = e
        {
            if matches!(
                value.as_ref(),
                PseudoExpr::Constr { shape, .. } if !matches!(
                    shape,
                    ConstructorShape::Known(KnownConstructor::True)
                        | ConstructorShape::Known(KnownConstructor::False)
                )
            ) {
                out.insert(*vid);
            }
        }
        pending.extend(
            crate::decompile::render_prep::scope_recurse::children(e)
                .into_iter()
                .rev(),
        );
    }
    out
}

/// Every body use of `var_id` is a CALL — `v(args)` or the fabricated
/// pack-projection call `v.1st(args)`/`v.2nd(args)`. With a non-function
/// AGGREGATE annotation (Pair/Tuple) that usage proves the annotation reads
/// wrong at the surface (`const e: Pair<Data, Data>` whose only use is
/// `e.1st(v_160, v_164)`, a plain 2-arg call in the bytecode). Requires >= 1
/// use; any non-call use keeps the annotation (fail-closed).
fn every_use_is_called(body: &PseudoExpr, var_id: VarId) -> bool {
    let mut uses = 0usize;
    let mut bad = false;
    let mut pending: Vec<&PseudoExpr> = vec![body];
    while let Some(e) = pending.pop() {
        match e {
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
                match function.as_ref() {
                    PseudoExpr::Var { id: Some(i), .. } if *i == var_id => {
                        uses += 1;
                    }
                    PseudoExpr::FieldAccess { record, selector }
                        if matches!(
                            selector,
                            crate::pseudo::field_selector::FieldSelector::PairFst
                                | crate::pseudo::field_selector::FieldSelector::PairSnd
                        ) && matches!(
                            record.as_ref(),
                            PseudoExpr::Var { id: Some(i), .. } if *i == var_id
                        ) =>
                    {
                        uses += 1;
                    }
                    other => pending.push(other),
                }
            }
            PseudoExpr::Var { id: Some(i), .. } if *i == var_id => {
                bad = true;
            }
            other => {
                pending.extend(
                    crate::decompile::render_prep::scope_recurse::children(other)
                        .into_iter()
                        .rev(),
                );
            }
        }
    }
    uses >= 1 && !bad
}

fn strip_validator_entry_terminator(rendered: String) -> String {
    // Only strip when there is content BEFORE the trailing `Void`.
    // A standalone `Void` output (a real Unit literal) is preserved.
    let trimmed = rendered.trim_end_matches('\n');
    if let Some(prefix) = trimmed.strip_suffix("\nVoid") {
        let mut out = prefix.to_string();
        if rendered.ends_with('\n') {
            out.push('\n');
        }
        out
    } else {
        rendered
    }
}

/// Does the tree's `Let` spine end in a literal `Unit`? That signature —
/// `promote_validator_entry_first`'s terminator, `let decompiled = …; let
/// helper = …; Void` — is the only shape whose trailing `Void` is an AST
/// artefact [`strip_validator_entry_terminator`] should remove; any other
/// tree (a handler fragment ending in an expect-chain) owns its trailing
/// `Void` as the chain's honest value.
fn spine_ends_in_unit(expr: &PseudoExpr) -> bool {
    let mut current = expr;
    loop {
        match current {
            PseudoExpr::Let { body, .. } => current = body,
            PseudoExpr::Unit => return true,
            _ => return false,
        }
    }
}

/// Arity that a `WhenPattern::Constructor` must render with, given
/// the resolved label, its `type_hint`, and its `shape`.
///
/// Plutus `Data` variants (`Constr`, `Map`, `List`, `Int`,
/// `ByteString`) can carry `shape.arity()` = 0 when the source
/// `Data.case` only shape-tests the variant without binding its
/// fields; valid surface syntax still needs arity-matching wildcards —
/// `Constr(_, _)` for arity 2, `Map(_)` / `List(_)` for arity 1. The
/// override is gated on the `type_hint` resolving to the canonical
/// `"Data"` namespace (`blueprint_registry::DATA_TYPE_HINT_NAME`),
/// so a user-defined ADT with a constructor named `"Constr"` falls
/// through to `shape.arity()`.
fn expected_pattern_arity(
    label: Option<&str>,
    type_hint: Option<&crate::decompile::TypeHintId>,
    shape: crate::pseudo::constructor::ConstructorShape,
) -> usize {
    // The canonical `Data`-namespace string
    // (`blueprint_registry::DATA_TYPE_HINT_NAME`) is private to
    // `decompile`, so match the literal — a divergence surfaces as a
    // Data-arity regression-test failure.
    let is_data_namespace = type_hint.map(|t| t.as_str() == "Data").unwrap_or(false);
    if is_data_namespace {
        match label {
            Some("Constr") => return 2,
            Some("Map") | Some("List") | Some("Int") | Some("ByteString") => return 1,
            _ => {}
        }
    }
    // Plutus V3 `ScriptInfo` constructors have fixed arities; the decoder may
    // mint a shorter `Unknown` shape (only the accessed fields) which would
    // render an invalid under-arity pattern (e.g. `Spending(output_reference)`
    // — Spending is 2-ary). Pad to the canonical arity with `_` wildcards.
    let is_script_info = type_hint
        .map(|t| t.as_str() == "script_info")
        .unwrap_or(false);
    if is_script_info {
        match label {
            Some("Spending") | Some("Certifying") | Some("Proposing") => return 2,
            Some("Minting") | Some("Rewarding") | Some("Voting") => return 1,
            _ => {}
        }
    }
    // The prelude `Option::Some` is 1-ary. A shape-test that bound no
    // payload can resolve to the `Some` label off a 0-arity `Unknown` shape,
    // rendering a bare `Some` — invalid surface syntax. Pad to arity 1, gated on the
    // canonical `Option` namespace (stamped by `late/normalize/option`'s
    // recovery and by `with_cardano_seed`) rather than on the bare label, so a
    // user/blueprint ADT naming a constructor `Some` under another hint is not
    // mis-padded — mirroring the `Data` / `script_info` gates above. The
    // nullary sibling `None` keeps arity 0 and stays bare.
    let is_option = type_hint.map(|t| t.as_str() == "Option").unwrap_or(false);
    if is_option && label == Some("Some") {
        return 1;
    }
    shape.arity()
}

pub(crate) fn sanitize_identifier(name: &str) -> String {
    match name {
        // Language keywords
        "fn" | "let" | "when" | "if" | "else" | "use" | "pub" | "type" | "const" | "test"
        | "expect" | "trace" | "fail" | "validator" | "and" | "or" | "not"
        // Keyword-like identifiers
        | "as" | "is" | "once" | "opaque" | "todo" | "via" | "bench" | "error"
        // Built-in type/value names
        | "True" | "False" | "Void" | "Some" | "None" | "Ok" | "Err" => format!("{}_", name),
        // The validator-purpose words `mint`/`spend`/`withdraw`/`certificate`/`vote`
        // are NOT reserved value identifiers — they are contextual keywords only
        // at the validator handler-DECLARATION position (emitted via
        // `ValidatorPurpose::keyword`, which never routes through here). As
        // ordinary binders / field names they are legal under surface v1.1 (the
        // stdlib's `Transaction.mint` field, `let mint = …`, even a `mint`
        // binder inside the `mint` handler); escaping them would mangle the
        // canonical TxInfo field names, so they stay unescaped.
        _ => name.to_string(),
    }
}

/// If `function` applied to `args` is a recognizable Scott-encoded
/// data-constructor application, return reader-facing comment lines
/// describing it; otherwise an empty vec.
///
/// Shape: `Apply(λ field_0 … field_{m-1} h_0 … h_{k-1}. h_t field_0 …
/// field_{m-1}, [a_0, …, a_{m-1}])` — a lambda taking `m` field params
/// followed by `k` branch-handler params, whose body applies handler
/// `h_t` to the `m` fields in order, applied to exactly the `m` field
/// values: the Scott constructor for variant tag `t` of a `k`-variant
/// union carrying `m` fields. Annotating rather than rewriting avoids
/// naming the variant inconsistently with how consumers pattern-match
/// it. Pairs (`k == 1`) are decoded to `Pair` elsewhere and excluded.
fn scott_constructor_comment(function: &PseudoExpr, args: &[PseudoExpr]) -> Vec<String> {
    let PseudoExpr::Lambda { params, body } = function else {
        return Vec::new();
    };
    let PseudoExpr::Apply {
        function: head,
        args: body_args,
    } = body.as_ref()
    else {
        return Vec::new();
    };
    let PseudoExpr::Var {
        id: Some(head_id), ..
    } = head.as_ref()
    else {
        return Vec::new();
    };
    let m = body_args.len();
    if m == 0 || m >= params.len() {
        return Vec::new();
    }
    // Body must apply the handler to params[0..m] in order.
    for (i, ba) in body_args.iter().enumerate() {
        let PseudoExpr::Var { id: Some(v), .. } = ba else {
            return Vec::new();
        };
        if *v != params[i].id {
            return Vec::new();
        }
    }
    // Head must be one of the handler params (index >= m).
    let Some(j) = params.iter().position(|p| p.id == *head_id) else {
        return Vec::new();
    };
    if j < m {
        return Vec::new();
    }
    let variant_count = params.len() - m;
    // Single-variant (k == 1) is a pair/record, decoded to `Pair`
    // elsewhere — don't annotate it as a tagged union.
    if variant_count < 2 {
        return Vec::new();
    }
    // The application must supply exactly the m field values.
    if args.len() != m {
        return Vec::new();
    }
    let tag = j - m;

    let fields_clause = match args
        .iter()
        .map(simple_value_repr)
        .collect::<Option<Vec<_>>>()
    {
        Some(reprs) => format!("fields ({})", reprs.join(", ")),
        None if m == 1 => "1 field".to_string(),
        None => format!("{m} fields"),
    };
    let ordinal = ordinal_word(tag + 1);
    vec![
        format!("// Scott-encoded tagged union: tag {tag} of {variant_count}, {fields_clause}."),
        format!(
            "// A matcher supplies {variant_count} branch fns; this value invokes the {ordinal}."
        ),
    ]
}

/// True when `expr` is an `Apply` that `scott_constructor_comment`
/// would annotate. Used to force-break a containing tuple so the
/// leading `// …` lands on its own line.
fn is_scott_constructor_application(expr: &PseudoExpr) -> bool {
    if let PseudoExpr::Apply { function, args } = expr {
        let effective = match function.as_ref() {
            PseudoExpr::Force(inner) => inner.as_ref(),
            other => other,
        };
        !scott_constructor_comment(effective, args).is_empty()
    } else {
        false
    }
}

/// Best-effort one-token rendering of a simple value for inclusion in a
/// comment. `None` for compound expressions (caller falls back to a
/// plain field count so the comment stays short).
fn simple_value_repr(expr: &PseudoExpr) -> Option<String> {
    match expr {
        PseudoExpr::Var { name, .. } => Some(sanitize_identifier(name)),
        PseudoExpr::Int(n) => Some(n.to_string()),
        // Match the printer's boolean rendering (`True`/`False`), not
        // Rust's `true`/`false`, so the comment agrees with the code.
        PseudoExpr::Bool(b) => Some(if *b { "True" } else { "False" }.to_string()),
        _ => None,
    }
}

/// English ordinal: `1 -> "1st"`, `2 -> "2nd"`, `3 -> "3rd"`, with the
/// usual 11–13 exception, else `"{n}th"`.
fn ordinal_word(n: usize) -> String {
    let suffix = match (n % 10, n % 100) {
        (_, 11..=13) => "th",
        (1, _) => "st",
        (2, _) => "nd",
        (3, _) => "rd",
        _ => "th",
    };
    format!("{n}{suffix}")
}

/// Configuration for pretty printing.
#[derive(Debug, Clone)]
pub(crate) struct PrettyConfig {
    /// Indentation width (number of spaces).
    pub indent: usize,
    /// Maximum line width before wrapping.
    pub width: usize,
    /// Whether to show type annotations.
    pub show_types: bool,
    /// Whether to show raw UPLC fallbacks.
    pub show_raw: bool,
    /// The render session this printer belongs to: script versions plus
    /// the opt-in surface transforms (church→native decode, compilable
    /// data access, `expect … or fail`). Read both by the
    /// `prepare_for_render` pass the printer runs internally and by the
    /// display sites here, so the two cannot disagree. The default is the
    /// faithful version-agnostic view, which is what every non-pipeline
    /// caller (`to_pretty`, tests, debug bundles) wants; the pipeline
    /// overrides it for the real render.
    pub render_ctx: crate::decompile::RenderCtx,
}

impl Default for PrettyConfig {
    fn default() -> Self {
        Self {
            indent: 2,
            width: 80,
            show_types: false,
            show_raw: true,
            render_ctx: crate::decompile::RenderCtx::default(),
        }
    }
}

/// Whether a `cond || trace @"msg": False` may be collapsed to the surface `?`
/// soft-assert. The `?` emits its OWN trace — `@"<expr source> ? False"` — when
/// the condition is false, so the round-trip is lossless only when the message
/// already IS that auto-format (it ends with `" ? False"`), or is empty/unit.
/// A custom message (e.g. `@"Signer is not eligible"`) is NOT recoverable from
/// `?`, so collapsing would silently DROP it; those keep the explicit
/// `|| trace @"msg": False` form.
fn trace_message_is_droppable(message: &PseudoExpr) -> bool {
    match message {
        PseudoExpr::String(s) => s.is_empty() || s.ends_with(" ? False"),
        PseudoExpr::Unit => true,
        _ => false,
    }
}

/// Pretty printer for PseudoExpr.
pub(crate) struct PrettyPrinter {
    config: PrettyConfig,
    /// Render-time source of truth for constructor display names, queried
    /// at `PseudoExpr::Constr` and `WhenPattern::Constructor` display
    /// sites. [`Self::new`] installs the Cardano-seeded registry;
    /// [`Self::with_registry`] swaps in the pipeline's richer one.
    registry: Rc<BlueprintHintRegistry>,
    /// Render-time source of truth for `show_types` annotations. Keyed by
    /// **final** pseudo-AST `VarId`s from the pipeline's last solver run,
    /// frozen before hand-off. Absent, every binder renders unannotated.
    final_types: Option<Rc<FinalTypeTable>>,
}

type PrettyArena<'a> = Arena<'a, PseudoNodeId>;
type PrettyDoc<'a> = DocBuilder<'a, PrettyArena<'a>, PseudoNodeId>;

fn pop_doc<'a>(out: &mut Vec<PrettyDoc<'a>>) -> PrettyDoc<'a> {
    out.pop().expect("doc stack underflow")
}

/// Group when-clauses by identical body into clause-index groups;
/// `Task::ExitWhen` renders a group of >1 as `P1 | P2 -> body`.
///
/// - ADJACENT clauses group freely — no arm in between to reorder past.
/// - NON-adjacent clauses group only in the provably order-safe case:
///   candidate and group leader are binder-free `Constructor` patterns
///   with equal bodies, and EVERY clause strictly between them is a
///   `Constructor` (binders/guards allowed) whose tag differs from the
///   candidate's. A subject matching the candidate then matches none of
///   the intervening arms, so hoisting it to the leader's position
///   cannot change which arm fires. Anything non-Constructor in between
///   vetoes — fail-closed, since `Literal`/`Var`/`Wildcard`/list
///   patterns can overlap a constructor subject in Data-land.
/// - Clauses with a `guard` are NEVER group members — guards may differ
///   per arm even when bodies match.
/// - Binder patterns (`Some(x)`) stay singletons: grouping them needs
///   alpha-equivalence on the body.
fn compute_when_body_groups(clauses: &[WhenClause]) -> Vec<Vec<usize>> {
    use crate::pseudo::ast::WhenPattern;
    fn pattern_has_binders(p: &WhenPattern) -> bool {
        match p {
            WhenPattern::Constructor { fields, .. } => !fields.is_empty(),
            WhenPattern::List { elements, tail } => !elements.is_empty() || tail.is_some(),
            WhenPattern::Tuple(fs) => !fs.is_empty(),
            WhenPattern::Pair(_, _) => true,
            WhenPattern::Var(_) => true,
            WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
        }
    }
    fn constructor_tag(p: &WhenPattern) -> Option<usize> {
        match p {
            WhenPattern::Constructor { tag, .. } => Some(*tag),
            _ => None,
        }
    }
    let mut groups: Vec<Vec<usize>> = Vec::new();
    'clauses: for (i, clause) in clauses.iter().enumerate() {
        let can_join = clause.guard.is_none() && !pattern_has_binders(&clause.pattern);
        if can_join {
            // Adjacent join: any binder-free pattern.
            if let Some(last) = groups.last_mut() {
                let leader = last[0];
                let leader_clause = &clauses[leader];
                if leader_clause.guard.is_none()
                    && !pattern_has_binders(&leader_clause.pattern)
                    && leader_clause.body == clause.body
                {
                    last.push(i);
                    continue;
                }
            }
            // Non-adjacent join: disjoint-tag Constructors only.
            if let Some(c_tag) = constructor_tag(&clause.pattern) {
                // Nearest eligible group first (minimizes the span the
                // disjointness proof must cover). Skip the last group —
                // the adjacent join above already rejected it.
                for g_idx in (0..groups.len().saturating_sub(1)).rev() {
                    let leader = groups[g_idx][0];
                    let leader_clause = &clauses[leader];
                    if leader_clause.guard.is_some()
                        || pattern_has_binders(&leader_clause.pattern)
                        || leader_clause.body != clause.body
                    {
                        continue;
                    }
                    let Some(l_tag) = constructor_tag(&leader_clause.pattern) else {
                        continue;
                    };
                    if l_tag == c_tag {
                        continue;
                    }
                    // Every clause strictly between leader and
                    // candidate must be a differently-tagged
                    // Constructor, in any group.
                    let span_disjoint = clauses[leader + 1..i].iter().all(|between| {
                        constructor_tag(&between.pattern).is_some_and(|t| t != c_tag)
                    });
                    if span_disjoint {
                        groups[g_idx].push(i);
                        continue 'clauses;
                    }
                }
            }
        }
        groups.push(vec![i]);
    }
    groups
}

fn annotate_doc_with_node_ids<'a>(doc: PrettyDoc<'a>, node_ids: &[PseudoNodeId]) -> PrettyDoc<'a> {
    node_ids
        .iter()
        .copied()
        .fold(doc, |doc, node_id| doc.annotate(node_id))
}

/// Wrap a rendered doc in a single-arg surface call: `name(inner)`.
/// Used to render the raw list spine as compilable `builtin` calls
/// (`builtin.head_list(...)` / `builtin.tail_list(...)`).
fn wrap_in_call<'a>(arena: &'a PrettyArena<'a>, name: &str, inner: PrettyDoc<'a>) -> PrettyDoc<'a> {
    arena
        .text(name.to_string())
        .append(arena.text("("))
        .append(inner)
        .append(arena.text(")"))
        .group()
}

/// Surface name for a builtin. The four un-recovered raw-`Data`-access
/// builtins (`ConstrUnpack`, `ListHead`, `ListTail`, `ListIsEmpty`) honor
/// the compilable-data-access toggle: OFF (default) gives the readable
/// `canonical_name` (`Constr.unpack` / `List.head` / `List.tail` /
/// `List.is_empty`), which is NOT valid surface syntax; ON gives the
/// compilable `display_name(Pretty)` (`builtin.un_constr_data` /
/// `builtin.head_list` / `builtin.tail_list` / `builtin.null_list`).
/// Every other builtin uses `display_name(Pretty)` unchanged.
fn data_access_builtin_name(name: BuiltinId, compilable_data_access: bool) -> &'static str {
    if !compilable_data_access
        && matches!(
            name,
            BuiltinId::ConstrUnpack
                | BuiltinId::ListHead
                | BuiltinId::ListTail
                | BuiltinId::ListIsEmpty
        )
    {
        name.display_name(BuiltinDisplayStyle::Canonical)
    } else {
        name.display_name(BuiltinDisplayStyle::Pretty)
    }
}

/// Wrap `inner` in `depth` nested `builtin.tail_list(...)` calls; `depth == 0`
/// returns `inner`. The name comes from the display map so it never drifts
/// from the canonical `builtin.*` rendering. ON-mode only — the OFF path
/// renders `[N..]` itself.
fn wrap_in_tail_list<'a>(
    arena: &'a PrettyArena<'a>,
    inner: PrettyDoc<'a>,
    depth: usize,
) -> PrettyDoc<'a> {
    let tail_name = BuiltinId::ListTail.display_name(BuiltinDisplayStyle::Pretty);
    let mut doc = inner;
    for _ in 0..depth {
        doc = wrap_in_call(arena, tail_name, doc);
    }
    doc
}

// GATE A (fail-closed): `coll[N]` lowers to
// `builtin.head_list(builtin.tail_list^N(coll))` ONLY on a STRUCTURAL list
// proof — `IndexAccess` is ALSO used for tuple/pair indexing, and a solver
// mis-type would turn a tuple index into `head_list(tuple)`
// (valid-looking-wrong). `pretty_helpers::list_proof` runs the fail-closed
// FIXPOINT over (a) let binders with provably-list values, (b) `[h, ..t]`
// tail binders of provably-list subjects, and (c) params of ENUMERABLE fns
// whose EVERY call site passes a provably-list arg — recursive self-calls
// participate through the fixpoint. `[N..]` slices need no gate: you cannot
// slice a tuple.

#[derive(Default)]
struct SpanWriter {
    output: String,
    active_annotations: Vec<(PseudoNodeId, usize)>,
    finished_annotations: Vec<(PseudoNodeId, usize, usize)>,
}

impl Render for SpanWriter {
    type Error = fmt::Error;

    fn write_str(&mut self, s: &str) -> Result<usize, Self::Error> {
        self.output.push_str(s);
        Ok(s.len())
    }

    fn write_str_all(&mut self, s: &str) -> Result<(), Self::Error> {
        self.output.push_str(s);
        Ok(())
    }

    fn fail_doc(&self) -> Self::Error {
        fmt::Error
    }
}

impl<'a> RenderAnnotated<'a, PseudoNodeId> for SpanWriter {
    fn push_annotation(&mut self, annotation: &'a PseudoNodeId) -> Result<(), Self::Error> {
        self.active_annotations
            .push((*annotation, self.output.len()));
        Ok(())
    }

    fn pop_annotation(&mut self) -> Result<(), Self::Error> {
        let Some((node_id, start)) = self.active_annotations.pop() else {
            return Err(fmt::Error);
        };
        self.finished_annotations
            .push((node_id, start, self.output.len()));
        Ok(())
    }
}

impl SpanWriter {
    /// Number the collected annotations against the text a reader will see.
    ///
    /// `post` is the renderer's last edit of the text — today
    /// [`strip_validator_entry_terminator`]. It runs BEFORE byte offsets
    /// become line/column pairs: an annotation ending inside a region the
    /// edit removes would otherwise keep an offset past the new end and
    /// yield a span starting one line past the document.
    fn finish(
        mut self,
        post: impl FnOnce(String) -> String,
    ) -> (String, Vec<(PseudoNodeId, SourceSpan)>) {
        self.finished_annotations.sort_by(|a, b| {
            a.1.cmp(&b.1)
                .then_with(|| b.2.cmp(&a.2))
                .then_with(|| a.0.cmp(&b.0))
        });
        self.finished_annotations
            .dedup_by(|a, b| a.0 == b.0 && a.1 == b.1 && a.2 == b.2);

        let output = post(self.output);
        let line_starts = collect_line_starts(&output);
        let spans = self
            .finished_annotations
            .into_iter()
            .map(|(node_id, start, end)| {
                (
                    node_id,
                    byte_range_to_span(&line_starts, output.len(), start, end),
                )
            })
            .collect();

        (output, spans)
    }
}

impl PrettyPrinter {
    /// Defaults to the Cardano-seeded registry, so a plain `to_pretty()`
    /// resolves the user-namespace names the AST's `type_hint`s assert —
    /// Data, Option, `IntervalBoundType`, `Credential`, `StakeCredential`.
    /// Purpose/ScriptInfo are seeded only in the Cardano namespace, which
    /// `resolve` does not consult; the full `decompile_program` path
    /// resolves those through the early pass's on-demand `register_user`.
    /// `with_registry` overrides this for callers threading the pipeline's
    /// own richer registry.
    pub(crate) fn new() -> Self {
        Self {
            config: PrettyConfig::default(),
            registry: Rc::new(BlueprintHintRegistry::with_cardano_seed(None)),
            final_types: None,
        }
    }

    /// Create a pretty printer with custom config. Seeds the Cardano
    /// registry by default — see [`Self::new`].
    pub(crate) fn with_config(config: PrettyConfig) -> Self {
        Self {
            config,
            registry: Rc::new(BlueprintHintRegistry::with_cardano_seed(None)),
            final_types: None,
        }
    }

    /// Attach a populated [`BlueprintHintRegistry`] to this printer,
    /// replacing the Cardano-seeded default.
    ///
    /// Consulted at `PseudoExpr::Constr` and `WhenPattern::Constructor`
    /// display sites; an unresolved shape renders `Constr<tag>`. Pass a
    /// shared `Rc` so one instance seeds render passes without copying.
    pub(crate) fn with_registry(mut self, registry: Rc<BlueprintHintRegistry>) -> Self {
        self.registry = registry;
        self
    }

    /// Attach a populated [`FinalTypeTable`] to this printer.
    ///
    /// It is the source of truth for `show_types` annotations on `let`
    /// bindings and named lambdas. Pass a shared `Rc<FinalTypeTable>` so
    /// pipeline-produced tables flow into render without copying entries.
    pub(crate) fn with_final_types(mut self, final_types: Rc<FinalTypeTable>) -> Self {
        self.final_types = Some(final_types);
        self
    }

    /// Pretty print a PseudoExpr to a string.
    pub(crate) fn print(&self, expr: &PseudoExpr) -> String {
        self.print_with_spans(expr).0
    }

    /// Pretty print a PseudoExpr and return per-node source spans.
    pub(crate) fn print_with_spans(
        &self,
        expr: &PseudoExpr,
    ) -> (String, Vec<(PseudoNodeId, SourceSpan)>) {
        // The church-decode notes come back with the tree: their `VarId`
        // keys match THIS prepare's binders and no other's.
        let prepared = crate::stack::grow_deep(|| {
            crate::decompile::render_prep::prepare_for_render_with_notes(
                expr,
                &self.config.render_ctx,
            )
        });
        let (disambiguated, church_notes) = (prepared.expr, prepared.church_notes);
        let node_ids = collect_node_ids(&disambiguated);
        let arena: PrettyArena<'_> = Arena::new();
        let doc = crate::stack::grow_deep(|| {
            self.to_doc(&arena, &disambiguated, &node_ids, &church_notes)
        });
        let mut writer = SpanWriter::default();
        crate::stack::grow_deep(|| {
            doc.render_raw(self.config.width, &mut writer).unwrap();
        });
        let strip_terminator = spine_ends_in_unit(&disambiguated);
        writer.finish(|rendered| {
            if strip_terminator {
                strip_validator_entry_terminator(rendered)
            } else {
                rendered
            }
        })
    }

    /// Resolve the rendered type of a `VarId` for `show_types` annotations.
    ///
    /// `PseudoType::Data` and `PseudoType::Unknown` both render as `"Data"`,
    /// the implicit default, so an annotation that degenerates to it is pure
    /// noise (`let o: Data = payload.fields[1]…` immediately consumed by
    /// `expect Constr<N>(…) = o`) — return `None` so the call site renders
    /// the binder bare. Refined types (`ByteArray`, `Int`, `List<…>`, named
    /// types …) still annotate.
    fn resolve_type(&self, var_id: VarId) -> Option<String> {
        let ty = self.final_types.as_ref()?.type_of_var(var_id)?;
        if matches!(&*ty, PseudoType::Data | PseudoType::Unknown) {
            return None;
        }
        // Suppress nested `Option<Option<X>>`: almost always wrong inference
        // rather than intentional double-wrapping (see `is_nested_option`).
        // Hiding the annotation is less misleading than printing a wrong
        // one, and the value structure itself stays visible.
        if is_nested_option(&ty) {
            return None;
        }
        Some(format_type_for_annotation(&ty))
    }

    /// `true` iff `var_id`'s resolved final type is a
    /// `PseudoType::Function` — the evidence that survives the
    /// annotation suppression on function-rendered `let` values
    /// (`value_renders_as_function`), which masks use-site-inferred
    /// wrong types like `Pair<Data, Data>`.
    fn resolved_is_function(&self, var_id: VarId) -> bool {
        self.final_types
            .as_ref()
            .and_then(|ft| ft.type_of_var(var_id))
            .is_some_and(|ty| matches!(&*ty, PseudoType::Function { .. }))
    }

    /// Returns true iff the resolved final type is a `Function` whose every
    /// component (params + ret) is `Unknown`/`Data` — rendering as the
    /// fully-underscored `fn(_, ..., _) -> _`.
    ///
    /// Widens suppression past the `resolved_is_function` gate: when the
    /// value renders as a function (Lambda / RecFn / Y-comb application)
    /// and the solver produced only this uninformative constraint, the
    /// annotation is pure noise. A generic `let f = g`, without
    /// `value_renders_as_function` evidence, still annotates.
    fn resolved_function_type_is_uninformative(&self, var_id: VarId) -> bool {
        let Some(ft) = self.final_types.as_ref() else {
            return false;
        };
        let Some(ty) = ft.type_of_var(var_id) else {
            return false;
        };
        is_uninformative_function_type(&ty)
    }

    /// `true` when the solver typed `var_id` as a `Pair`/`Tuple` but the body
    /// only ever CALLS it. The type may be faithful to the church encoding,
    /// yet `const e: Pair<Data, Data>` over uses like `e.1st(a, b)` reads as
    /// data-on-a-callable — suppress the annotation. Structural pair / tuple /
    /// constr / list literals keep theirs.
    fn aggregate_type_on_called_binder(
        &self,
        var_id: VarId,
        value: &PseudoExpr,
        body: &PseudoExpr,
    ) -> bool {
        let Some(ty) = self
            .final_types
            .as_ref()
            .and_then(|t| t.type_of_var(var_id))
        else {
            return false;
        };
        if !matches!(ty.as_ref(), PseudoType::Pair(..) | PseudoType::Tuple(..)) {
            return false;
        }
        if matches!(
            value,
            PseudoExpr::Pair(..)
                | PseudoExpr::Tuple(..)
                | PseudoExpr::Constr { .. }
                | PseudoExpr::List { .. }
        ) {
            return false;
        }
        every_use_is_called(body, var_id)
    }

    fn function_type_on_non_function_value(&self, var_id: VarId, value: &PseudoExpr) -> bool {
        self.resolved_is_function(var_id) && value_is_definitely_not_function(value)
    }

    /// Detect the type-vs-value mismatch where the `FinalTypeTable`
    /// resolves a let-binder to `Bool` but the value is a `Constr`
    /// whose `shape` is `Unknown { tag, arity }` — not the surface's
    /// `True`/`False` shape. That constructor lives in a user-defined
    /// sum type (rendered `Unknown_E_X_Y`), so the `Bool` annotation is
    /// a stale inference from elsewhere and is suppressed. A genuine
    /// `let x: Bool = True` carries `Known(KnownConstructor::True)` and
    /// passes the guard.
    fn bool_annotation_misses_constr_shape(&self, var_id: VarId, value: &PseudoExpr) -> bool {
        let Some(ft) = self.final_types.as_ref() else {
            return false;
        };
        let Some(ty) = ft.type_of_var(var_id) else {
            return false;
        };
        if !matches!(&*ty, PseudoType::Bool) {
            return false;
        }
        match value {
            PseudoExpr::Constr { shape, .. } => {
                use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
                !matches!(
                    shape,
                    ConstructorShape::Known(KnownConstructor::True | KnownConstructor::False)
                )
            }
            _ => false,
        }
    }

    /// Format a named-fn param, adding `: <type>` when `show_types`
    /// is on and the param's `VarId` has a non-default resolved
    /// type — so validator-entry params surface their seeded types
    /// (e.g. `script_context: ScriptContext`).
    fn format_named_fn_param(&self, binder: &Binder) -> String {
        let name = sanitize_identifier(binder.as_ref());
        if !self.config.show_types {
            return name;
        }
        // Suppress `fn(_, ..., _) -> _` param types where every
        // leaf is `_`: they say nothing beyond "this is a
        // function", and `fn name(p1, p2)` already puts them in
        // input positions, so callability is implied.
        if self.resolved_function_type_is_uninformative(binder.var_id()) {
            return name;
        }
        match self.resolve_type(binder.var_id()) {
            Some(ty) => format!("{name}: {ty}"),
            None => name,
        }
    }

    /// When rendering `fn name(args) -> T { ... }` the binder's
    /// own type is the WHOLE function; unwrap `Function.ret` for
    /// the return-type slot, else the renderer emits
    /// `fn name(args) -> fn(_) -> _ { ... }` and doubles the
    /// function shape.
    fn resolve_return_type_for_named_fn(&self, var_id: VarId) -> Option<String> {
        let ty = self.final_types.as_ref()?.type_of_var(var_id)?;
        let ret = match ty.as_ref() {
            PseudoType::Function { ret, .. } => ret.clone(),
            _ => return self.resolve_type(var_id),
        };
        // Drop the return-type annotation when it's an
        // Unknown/Data leaf OR an uninformative function shape like
        // `fn(_) -> _` / `fn(_, _) -> _`.
        if is_uninformative_or_leaf(ret.as_ref()) {
            return None;
        }
        Some(format_type_for_annotation(&ret))
    }

    fn to_doc<'a>(
        &self,
        arena: &'a PrettyArena<'a>,
        expr: &PseudoExpr,
        node_ids: &HashMap<usize, PseudoNodeId>,
        church_notes: &crate::decompile::render_prep::ChurchLetComments,
    ) -> PrettyDoc<'a> {
        enum WrapperKind {
            Delay,
            Force,
        }

        enum Task<'b> {
            Enter(&'b PseudoExpr),
            FinalizeNode(PseudoNodeId),
            ExitAnnotateNodes {
                node_ids: Vec<PseudoNodeId>,
            },
            ExitLambda {
                params: &'b [Binder],
                lambda_node_id: Option<PseudoNodeId>,
                extra_node_ids: Vec<PseudoNodeId>,
            },
            ExitRecFn {
                name: &'b str,
                params: &'b [Binder],
            },
            ExitApply {
                args_len: usize,
                force_multiline: bool,
                extra_node_ids: Vec<PseudoNodeId>,
                /// Rendered as `// …` comment lines before the call.
                /// Non-empty only for recognizable Scott-encoded
                /// constructor applications.
                leading_comment: Vec<String>,
            },
            ExitLetRecFnSameName,
            ExitLetLambda {
                name: &'b str,
                var_id: VarId,
                params: &'b [Binder],
                lambda_node_id: Option<PseudoNodeId>,
                /// The lambda body AST: a `-> Bool` return annotation is
                /// dropped when a return leaf contradicts it.
                fn_body: &'b PseudoExpr,
            },
            ExitLetSimple {
                name: &'b str,
                var_id: VarId,
                inline_value: bool,
                /// When true, the value renders as a statement sequence
                /// (`let`/`expect`/`seq` chain) and must be wrapped in
                /// `{ … }` to be a legal single-expression `let` value.
                wrap_value_in_block: bool,
                /// When true, suppress the `: <type>` annotation.
                /// Set at the push site when the annotation would
                /// lie — e.g. a function-rendering value typed
                /// `Pair<Data, Data>` from its use sites.
                suppress_type: bool,
            },
            ExitLetFlattened {
                name: &'b str,
                var_id: VarId,
                bindings: Vec<(&'b str, VarId, &'b PseudoExpr)>,
                resolved_value: &'b PseudoExpr,
                /// See `ExitLetSimple::wrap_value_in_block`: the
                /// post-flattening resolved value renders as a statement
                /// sequence and needs `{ … }` braces.
                wrap_value_in_block: bool,
                /// Computed at push, where the let BODY is in scope:
                /// suppress a Pair/Tuple annotation on a binder the
                /// body only ever calls.
                aggregate_called_suppress: bool,
                extra_node_ids: Vec<PseudoNodeId>,
            },
            ExitIfChain {
                branches: Vec<(&'b PseudoExpr, &'b PseudoExpr)>,
                extra_node_ids: Vec<PseudoNodeId>,
            },
            ExitSortedAssocLookupIf {
                cutoff_op: BinaryOp,
                extra_node_ids: Vec<PseudoNodeId>,
            },
            ExitWhenExpect {
                pattern: &'b WhenPattern,
                subject_name: Option<&'b str>,
                has_subject_expr: bool,
                body_is_true: bool,
                /// Opt-in: the dropped fail-arm message, rendered as
                /// `expect P = X or fail @"msg"` when `expect_or_fail` is on.
                fail_message: Option<&'b str>,
                extra_node_ids: Vec<PseudoNodeId>,
            },
            ExitWhen {
                subject_name: Option<&'b str>,
                clauses: &'b [WhenClause],
                has_subject_expr: bool,
                /// When true, the subject renders as a statement
                /// sequence (`let`/`expect`/`seq` chain) and must be
                /// wrapped in `{ … }` to be a legal `when` subject.
                wrap_subject_in_block: bool,
                extra_node_ids: Vec<PseudoNodeId>,
                /// Body-groups from `compute_when_body_groups`: each
                /// inner Vec lists clause indices sharing one body
                /// (not necessarily adjacent). A group of >1 renders
                /// as `P1 | P2 | … -> body`.
                ///
                /// Body tasks are pushed for ALL clauses to keep the
                /// stack balanced — at ExitWhen the bodies popped for
                /// non-leader indices are discarded.
                body_groups: Vec<Vec<usize>>,
            },
            ExitList {
                elements_len: usize,
                has_tail: bool,
            },
            ExitTuple {
                len: usize,
                /// Render one element per line. Forced when an element
                /// carries a leading annotation comment (a Scott-
                /// constructor application), so the `// …` lines land
                /// on their own line rather than crammed after `(x, `.
                force_multiline: bool,
            },
            ExitPair,
            ExitConstr {
                name: Option<Rc<str>>,
                tag: usize,
                fields_len: usize,
                /// `KnownConstructor::Cons` with 2 fields → render the
                /// expression as the list-spread sugar `[head, ..tail]`
                /// (mirrors the pattern-position sugar) instead of `Cons(h, t)`.
                is_cons: bool,
            },
            ExitFieldAccess {
                field: &'b str,
                /// When true, the record renders as a statement
                /// sequence and must be wrapped in `{ … }` so
                /// `record.field` parses (e.g. `{ let … }.fst`).
                wrap_record_in_block: bool,
            },
            ExitIndexAccess {
                index: usize,
                /// See `ExitFieldAccess::wrap_record_in_block`.
                wrap_collection_in_block: bool,
                /// GATE A: lower `coll[N]` to
                /// `builtin.head_list(builtin.tail_list^N(coll))` when the
                /// collection is provably list-like; false keeps the bracket
                /// render (Tuple/Pair). See the Enter site.
                as_list: bool,
            },
            ExitSliceFrom {
                start: usize,
                /// See `ExitFieldAccess::wrap_record_in_block`: wrap a
                /// statement-sequence collection so `collection[n..]` parses.
                wrap_collection_in_block: bool,
                extra_node_ids: Vec<PseudoNodeId>,
            },
            /// Render a `FieldAccess` with the `ListHead` selector
            /// (`.head`) as `builtin.head_list(record)`. `.head` is always a
            /// list accessor, so no gate is needed.
            ExitListHeadAccessor {
                /// See `ExitFieldAccess::wrap_record_in_block`.
                wrap_record_in_block: bool,
            },
            ExitWrapOperand {
                needs_paren: bool,
                force_block_parens: bool,
            },
            ExitBinOpTraceIfFalse {
                needs_parens: bool,
            },
            ExitBinOpTraceIfTrue {
                needs_parens: bool,
            },
            ExitBinOpDefault {
                op: BinaryOp,
            },
            ExitBinOpLogicalChain {
                op: BinaryOp,
                parts_len: usize,
            },
            ExitUnOpNot {
                needs_parens: bool,
            },
            ExitUnOpNegate,
            ExitUnOpLength,
            ExitBuiltinCall {
                name: BuiltinId,
                args_len: usize,
                force_multiline: bool,
            },
            ExitListPrependSugar,
            ExitSeqChain {
                len: usize,
                extra_node_ids: Vec<PseudoNodeId>,
            },
            ExitExpectChain {
                /// For each condition in the chain, `true` if it carries a
                /// 3rd-arg fail message (rendered as `, @"msg"` trailer).
                has_messages: Vec<bool>,
                extra_node_ids: Vec<PseudoNodeId>,
            },
            ExitDelayForceChain {
                wrappers: Vec<WrapperKind>,
                multiline: bool,
                extra_node_ids: Vec<PseudoNodeId>,
            },
            ExitTrace,
            ExitRootLambdaThenHelpers {
                helper_len: usize,
            },
            ExitRootNamedLambda {
                name: &'b str,
                var_id: VarId,
                params: &'b [Binder],
                lambda_node_id: Option<PseudoNodeId>,
                /// Lambda body AST, read by the `-> Bool` gate.
                fn_body: &'b PseudoExpr,
            },
            ExitParameterLet {
                name: &'b str,
                var_id: VarId,
            },
            ExitParametrizedScript {
                param_count: usize,
                helper_count: usize,
            },
        }

        crate::stack::grow_deep(|| {
            let expect_sugar_positions = collect_expect_sugar_positions(expr);
            // From the display map, so the name never drifts from `builtin.*`.
            let head_list_name = BuiltinId::ListHead.display_name(BuiltinDisplayStyle::Pretty);
            let needs_paren_for =
                |child: &PseudoExpr, parent_op: BinaryOp, is_left: bool| match child {
                    // Control-flow expressions as operands should be explicit.
                    PseudoExpr::If { .. } | PseudoExpr::When { .. } => true,
                    PseudoExpr::BinOp { op, .. } => {
                        let child_prec = op.precedence();
                        let parent_prec = parent_op.precedence();

                        if child_prec < parent_prec {
                            true
                        } else if child_prec == parent_prec {
                            if is_left {
                                parent_op.is_right_assoc()
                            } else {
                                !parent_op.is_right_assoc()
                            }
                        } else {
                            false
                        }
                    }
                    _ => false,
                };

            // Fixpoint list proof (see `pretty_helpers::list_proof`) so a
            // `Var` index `coll[i]` lowers to `head_list(tail_list^i(coll))`
            // like a direct list shape does. Skipped in OFF mode.
            let list_proof: Option<helpers::list_proof::ListProof> =
                if self.config.render_ctx.compilable_data_access() {
                    Some(helpers::list_proof::collect_list_proof(expr))
                } else {
                    None
                };

            // Lookup set for the `-> Bool` contradiction gate below.

            let non_bool_constr_bindings = collect_non_bool_constr_bindings(expr);

            let mut tasks = match prepare_root_render_layout(expr) {
                RootRenderLayout::LambdaWithHelpers(RootLambdaWithHelpers {
                    lambda_expr,
                    params,
                    body,
                    helpers,
                }) => {
                    let root_lambda_node_id = node_ids
                        .get(&(lambda_expr as *const PseudoExpr as usize))
                        .copied();
                    let mut tasks = vec![Task::ExitRootLambdaThenHelpers {
                        helper_len: helpers.len(),
                    }];
                    for helper in helpers.into_iter().rev() {
                        match helper {
                            RootHelper::RecFn { let_expr, expr } => {
                                if let Some(node_id) = node_ids
                                    .get(&(let_expr as *const PseudoExpr as usize))
                                    .copied()
                                {
                                    tasks.push(Task::ExitAnnotateNodes {
                                        node_ids: vec![node_id],
                                    });
                                }
                                tasks.push(Task::Enter(expr));
                            }
                            RootHelper::Lambda {
                                let_expr,
                                expr,
                                name,
                                var_id,
                                params,
                                body,
                            } => {
                                if let Some(node_id) = node_ids
                                    .get(&(let_expr as *const PseudoExpr as usize))
                                    .copied()
                                {
                                    tasks.push(Task::ExitAnnotateNodes {
                                        node_ids: vec![node_id],
                                    });
                                }
                                tasks.push(Task::ExitRootNamedLambda {
                                    name,
                                    var_id,
                                    params,
                                    lambda_node_id: node_ids
                                        .get(&(expr as *const PseudoExpr as usize))
                                        .copied(),
                                    fn_body: body,
                                });
                                tasks.push(Task::Enter(body));
                            }
                        }
                    }
                    tasks.push(Task::ExitLambda {
                        params,
                        lambda_node_id: root_lambda_node_id,
                        extra_node_ids: Vec::new(),
                    });
                    tasks.push(Task::Enter(body));
                    tasks
                }
                RootRenderLayout::Parametrized(RootParametrizedScript {
                    parameters,
                    main:
                        RootLambdaWithHelpers {
                            lambda_expr,
                            params,
                            body,
                            helpers,
                        },
                }) => {
                    let root_lambda_node_id = node_ids
                        .get(&(lambda_expr as *const PseudoExpr as usize))
                        .copied();
                    let mut tasks = vec![Task::ExitParametrizedScript {
                        param_count: parameters.len(),
                        helper_count: helpers.len(),
                    }];
                    for helper in helpers.into_iter().rev() {
                        match helper {
                            RootHelper::RecFn { let_expr, expr } => {
                                if let Some(node_id) = node_ids
                                    .get(&(let_expr as *const PseudoExpr as usize))
                                    .copied()
                                {
                                    tasks.push(Task::ExitAnnotateNodes {
                                        node_ids: vec![node_id],
                                    });
                                }
                                tasks.push(Task::Enter(expr));
                            }
                            RootHelper::Lambda {
                                let_expr,
                                expr,
                                name,
                                var_id,
                                params,
                                body,
                            } => {
                                if let Some(node_id) = node_ids
                                    .get(&(let_expr as *const PseudoExpr as usize))
                                    .copied()
                                {
                                    tasks.push(Task::ExitAnnotateNodes {
                                        node_ids: vec![node_id],
                                    });
                                }
                                tasks.push(Task::ExitRootNamedLambda {
                                    name,
                                    var_id,
                                    params,
                                    lambda_node_id: node_ids
                                        .get(&(expr as *const PseudoExpr as usize))
                                        .copied(),
                                    fn_body: body,
                                });
                                tasks.push(Task::Enter(body));
                            }
                        }
                    }
                    tasks.push(Task::ExitLambda {
                        params,
                        lambda_node_id: root_lambda_node_id,
                        extra_node_ids: Vec::new(),
                    });
                    tasks.push(Task::Enter(body));
                    for parameter in parameters.into_iter().rev() {
                        let RootParameter {
                            let_expr,
                            name,
                            var_id,
                            value,
                        } = parameter;
                        if let Some(node_id) = node_ids
                            .get(&(let_expr as *const PseudoExpr as usize))
                            .copied()
                        {
                            tasks.push(Task::ExitAnnotateNodes {
                                node_ids: vec![node_id],
                            });
                        }
                        tasks.push(Task::ExitParameterLet { name, var_id });
                        tasks.push(Task::Enter(value));
                    }
                    tasks
                }
                RootRenderLayout::Plain(expr) => vec![Task::Enter(expr)],
            };
            let mut out: Vec<PrettyDoc<'a>> = Vec::new();

            while let Some(task) = tasks.pop() {
                match task {
                    Task::Enter(node) => {
                        if let Some(node_id) = node_ids.get(&(node as *const PseudoExpr as usize)) {
                            tasks.push(Task::FinalizeNode(*node_id));
                        }

                        match node {
                            PseudoExpr::Int(n) => out.push(arena.text(n.to_string())),

                            PseudoExpr::ByteArray(bytes) => {
                                out.push(arena.text(format_byte_array(bytes)))
                            }

                            PseudoExpr::String(s) => {
                                out.push(arena.text(format!("@\"{}\"", escape_string(s))))
                            }

                            PseudoExpr::Bool(b) => {
                                out.push(arena.text(if *b { "True" } else { "False" }))
                            }

                            PseudoExpr::Unit => out.push(arena.text("Void")),

                            PseudoExpr::Var { name, id: _ } => {
                                // Variable references never emit `: Type` —
                                // annotations belong on declaration sites
                                // (Let, Lambda params, RecFn signatures).
                                // At a reference they render as nonsense:
                                // `script_context_fields: List<Data>.redeemer`.
                                out.push(arena.text(sanitize_identifier(name)));
                            }

                            PseudoExpr::Lambda { params, body } => {
                                // Unwrap the top-level expect!(cond, Void): validator entry
                                // points wrap the body in force(if cond {()} else {error}), so
                                // the assertion is implied and only the condition renders.
                                let (actual_body, extra_node_ids) = match body.as_ref() {
                                    PseudoExpr::Apply { function, args }
                                        if args.len() == 2
                                            && matches!(args[1], PseudoExpr::Unit)
                                            && matches!(
                                                function.as_ref(),
                                                PseudoExpr::Var { name, .. } if name == "expect!"
                                            ) =>
                                    {
                                        (
                                            &args[0],
                                            node_id_for(body.as_ref(), node_ids)
                                                .into_iter()
                                                .collect(),
                                        )
                                    }
                                    _ => (body.as_ref(), Vec::new()),
                                };
                                tasks.push(Task::ExitLambda {
                                    params,
                                    lambda_node_id: None,
                                    extra_node_ids,
                                });
                                tasks.push(Task::Enter(actual_body));
                            }

                            PseudoExpr::RecFn { name, params, body } => {
                                tasks.push(Task::ExitRecFn {
                                    name: name.as_str(),
                                    params,
                                });
                                tasks.push(Task::Enter(body.as_ref()));
                            }

                            PseudoExpr::Apply { function, args } => {
                                if let PseudoExpr::BuiltinCall {
                                    name,
                                    args: builtin_args,
                                } = function.as_ref()
                                    && *name == crate::BuiltinId::Seq
                                    && builtin_args.is_empty()
                                    && args.len() == 2
                                {
                                    let stmts = collect_seq_chain(node);
                                    tasks.push(Task::ExitSeqChain {
                                        len: stmts.len(),
                                        extra_node_ids: collect_hidden_seq_chain_node_ids(
                                            node, node_ids,
                                        ),
                                    });
                                    for stmt in stmts.into_iter().rev() {
                                        tasks.push(Task::Enter(stmt));
                                    }
                                    continue;
                                }

                                if let PseudoExpr::BuiltinCall {
                                    name,
                                    args: builtin_args,
                                } = function.as_ref()
                                    && *name == crate::BuiltinId::ListPrepend
                                    && builtin_args.is_empty()
                                    && args.len() == 2
                                    && !matches!(args[1], PseudoExpr::List { .. })
                                {
                                    tasks.push(Task::ExitListPrependSugar);
                                    tasks.push(Task::Enter(&args[1]));
                                    tasks.push(Task::Enter(&args[0]));
                                    continue;
                                }

                                // Apply(BuiltinCall("List.tail", []), [arg]) → arg[1..]
                                if let PseudoExpr::BuiltinCall {
                                    name,
                                    args: builtin_args,
                                } = function.as_ref()
                                    && *name == crate::BuiltinId::ListTail
                                    && builtin_args.is_empty()
                                    && args.len() == 1
                                {
                                    let (inner, depth) = count_tail_chain_any(&args[0]);
                                    tasks.push(Task::ExitSliceFrom {
                                        start: depth + 1,
                                        wrap_collection_in_block: renders_as_statement_sequence(
                                            inner,
                                        ),
                                        extra_node_ids: collect_hidden_tail_chain_node_ids(
                                            &args[0], node_ids,
                                        ),
                                    });
                                    tasks.push(Task::Enter(inner));
                                    continue;
                                }

                                // Flatten expect!(c1, expect!(c2, ..., value)) chains
                                // into `expect! c1; expect! c2; value`. The optional 3rd
                                // arg carries a fail message: `expect! cond, @"msg"`.
                                if is_expect_bang(function.as_ref())
                                    && (args.len() == 2 || args.len() == 3)
                                {
                                    let (entries, final_value) = collect_expect_chain(node);
                                    let has_messages: Vec<bool> =
                                        entries.iter().map(|(_, m)| m.is_some()).collect();
                                    tasks.push(Task::ExitExpectChain {
                                        has_messages,
                                        extra_node_ids: collect_hidden_expect_chain_node_ids(
                                            node, node_ids,
                                        ),
                                    });
                                    tasks.push(Task::Enter(final_value));
                                    for (cond, msg_opt) in entries.into_iter().rev() {
                                        if let Some(msg) = msg_opt {
                                            tasks.push(Task::Enter(msg));
                                        }
                                        tasks.push(Task::Enter(cond));
                                    }
                                    continue;
                                }

                                // Absorb force into call: Apply(Force(f), args) → f(args)
                                // instead of force(f)(args) — forcing a thunk is a call.
                                let effective_fn =
                                    if let PseudoExpr::Force(inner) = function.as_ref() {
                                        inner.as_ref()
                                    } else {
                                        function.as_ref()
                                    };
                                let mut extra_node_ids = Vec::new();
                                if matches!(function.as_ref(), PseudoExpr::Force(_))
                                    && let Some(node_id) = node_id_for(function.as_ref(), node_ids)
                                {
                                    extra_node_ids.push(node_id);
                                }
                                if let PseudoExpr::Var { .. } = effective_fn
                                    && let Some(node_id) = node_id_for(effective_fn, node_ids)
                                {
                                    extra_node_ids.push(node_id);
                                }
                                tasks.push(Task::ExitApply {
                                    args_len: args.len(),
                                    force_multiline: should_force_multiline_call_args(args),
                                    extra_node_ids,
                                    leading_comment: scott_constructor_comment(effective_fn, args),
                                });
                                for arg in args.iter().rev() {
                                    // A statement-sequence argument (`expect …; e`,
                                    // `let …; e`, delay/force-wrapped chains) must be
                                    // block-wrapped — spliced bare, its statements
                                    // blur the argument boundaries.
                                    if renders_as_statement_sequence(arg) {
                                        tasks.push(Task::ExitWrapOperand {
                                            needs_paren: false,
                                            force_block_parens: true,
                                        });
                                    }
                                    tasks.push(Task::Enter(arg));
                                }
                                // Suppress type annotation on function Var in call position:
                                // `rec_fn_8: Bool(args)` is confusing — render as `rec_fn_8(args)`.
                                if let PseudoExpr::Var { name, .. } = effective_fn {
                                    out.push(arena.text(sanitize_identifier(name)));
                                } else {
                                    tasks.push(Task::Enter(effective_fn));
                                }
                            }

                            PseudoExpr::Let {
                                name,
                                id,
                                value,
                                body,
                            } => {
                                if let PseudoExpr::RecFn { name: fn_name, .. } = value.as_ref()
                                    && fn_name.as_str() == name.as_str()
                                {
                                    tasks.push(Task::ExitLetRecFnSameName);
                                    tasks.push(Task::Enter(body.as_ref()));
                                    tasks.push(Task::Enter(value.as_ref()));
                                    continue;
                                }

                                // Inverted rec-fn let (readability only):
                                //   let f = f(args) in rec fn f(...) { ... }
                                // renders as the declaration first, then `f(args)`.
                                if let PseudoExpr::Apply { function, .. } = value.as_ref()
                                    && let PseudoExpr::Var {
                                        name: call_name, ..
                                    } = function.as_ref()
                                    && let PseudoExpr::RecFn { name: fn_name, .. } = body.as_ref()
                                {
                                    let rec_name = fn_name.as_str();
                                    let let_name = name.as_str();
                                    let let_name_matches_rec = let_name == rec_name
                                        || let_name.strip_suffix("_result") == Some(rec_name);
                                    if call_name.as_str() == rec_name && let_name_matches_rec {
                                        tasks.push(Task::ExitLetRecFnSameName);
                                        tasks.push(Task::Enter(value.as_ref()));
                                        tasks.push(Task::Enter(body.as_ref()));
                                        continue;
                                    }
                                }

                                let id_concrete =
                                    id.unwrap_or_else(VarId::fresh_compat_placeholder);
                                if let PseudoExpr::Lambda {
                                    params,
                                    body: fn_body,
                                } = value.as_ref()
                                    && !uses_var_as_control_subject(
                                        body.as_ref(),
                                        id_concrete,
                                        name,
                                    )
                                {
                                    tasks.push(Task::ExitLetLambda {
                                        name: name.as_str(),
                                        var_id: id_concrete,
                                        params,
                                        lambda_node_id: node_ids
                                            .get(&(value.as_ref() as *const PseudoExpr as usize))
                                            .copied(),
                                        fn_body: fn_body.as_ref(),
                                    });
                                    tasks.push(Task::Enter(body.as_ref()));
                                    tasks.push(Task::Enter(fn_body.as_ref()));
                                    continue;
                                }

                                let mut bindings = Vec::new();
                                let resolved_value =
                                    collect_nested_let_bindings(value, &mut bindings);

                                if bindings.is_empty() {
                                    tasks.push(Task::ExitLetSimple {
                                        name: name.as_str(),
                                        var_id: id_concrete,
                                        inline_value: should_inline_let_value(value.as_ref()),
                                        wrap_value_in_block: renders_as_statement_sequence(
                                            value.as_ref(),
                                        ),
                                        // Suppress the `: <type>` annotation when the
                                        // value ultimately renders as a function —
                                        // Lambda, RecFn, or a Let chain terminating
                                        // in one (`let X = (let Y = Lambda in Y)`,
                                        // whose let-head keeps a use-site-inferred
                                        // type that is wrong for a function). Keep
                                        // it when the resolved final type is
                                        // `Function`, surfacing as `: fn(_) -> _`.
                                        suppress_type: (value_renders_as_function(value.as_ref())
                                            && (!self.resolved_is_function(id_concrete)
                                                || self.resolved_function_type_is_uninformative(
                                                    id_concrete,
                                                )))
                                            || self.bool_annotation_misses_constr_shape(
                                                id_concrete,
                                                value.as_ref(),
                                            )
                                            || self.function_type_on_non_function_value(
                                                id_concrete,
                                                value.as_ref(),
                                            )
                                            || self.aggregate_type_on_called_binder(
                                                id_concrete,
                                                value.as_ref(),
                                                body.as_ref(),
                                            ),
                                    });
                                    tasks.push(Task::Enter(body.as_ref()));
                                    tasks.push(Task::Enter(value.as_ref()));
                                } else {
                                    let binding_values: Vec<&PseudoExpr> =
                                        bindings.iter().map(|(_, _, bvalue)| *bvalue).collect();
                                    tasks.push(Task::ExitLetFlattened {
                                        name: name.as_str(),
                                        var_id: id_concrete,
                                        bindings,
                                        resolved_value,
                                        wrap_value_in_block: renders_as_statement_sequence(
                                            resolved_value,
                                        ),
                                        aggregate_called_suppress: self
                                            .aggregate_type_on_called_binder(
                                                id_concrete,
                                                resolved_value,
                                                body.as_ref(),
                                            ),
                                        extra_node_ids: collect_hidden_nested_let_node_ids(
                                            value.as_ref(),
                                            node_ids,
                                        ),
                                    });
                                    tasks.push(Task::Enter(body.as_ref()));
                                    tasks.push(Task::Enter(resolved_value));
                                    for bvalue in binding_values.into_iter().rev() {
                                        tasks.push(Task::Enter(bvalue));
                                    }
                                }
                            }

                            PseudoExpr::If {
                                condition,
                                then_branch,
                                else_branch,
                            } => {
                                if let Some(sorted_lookup) = try_match_sorted_assoc_lookup_if(
                                    condition.as_ref(),
                                    then_branch.as_ref(),
                                    else_branch.as_ref(),
                                ) {
                                    tasks.push(Task::ExitSortedAssocLookupIf {
                                        cutoff_op: sorted_lookup.cutoff_op,
                                        extra_node_ids: node_id_for(then_branch.as_ref(), node_ids)
                                            .into_iter()
                                            .collect(),
                                    });
                                    tasks.push(Task::Enter(sorted_lookup.final_else));
                                    tasks.push(Task::Enter(sorted_lookup.none_branch));
                                    tasks.push(Task::Enter(sorted_lookup.cutoff_right));
                                    tasks.push(Task::Enter(sorted_lookup.cutoff_left));
                                    tasks.push(Task::Enter(sorted_lookup.some_branch));
                                    tasks.push(Task::Enter(sorted_lookup.eq_condition));
                                    continue;
                                }

                                let (branches, final_else) = flatten_if_chain(
                                    condition.as_ref(),
                                    then_branch.as_ref(),
                                    else_branch.as_ref(),
                                );

                                let branch_nodes = branches.clone();
                                tasks.push(Task::ExitIfChain {
                                    branches,
                                    extra_node_ids: collect_hidden_if_chain_node_ids(
                                        else_branch.as_ref(),
                                        node_ids,
                                    ),
                                });
                                tasks.push(Task::Enter(final_else));
                                for (cond, then_expr) in branch_nodes.into_iter().rev() {
                                    tasks.push(Task::Enter(then_expr));
                                    tasks.push(Task::Enter(cond));
                                }
                            }

                            PseudoExpr::When {
                                subject,
                                subject_name,
                                clauses,
                            } => {
                                let rendered_subject_name =
                                    subject_name.as_deref().filter(|name| {
                                        when_subject_name_matches(subject.as_ref(), name)
                                    });
                                let allow_expect_sugar = expect_sugar_positions
                                    .contains(&(node as *const PseudoExpr as usize));
                                if allow_expect_sugar
                                    && let Some((pattern, body_expr)) =
                                        extract_expect_pattern(clauses)
                                {
                                    let has_subject_expr = rendered_subject_name.is_none();
                                    let body_is_true = matches!(body_expr, PseudoExpr::Bool(true));
                                    let mut extra_node_ids = Vec::new();
                                    if !has_subject_expr
                                        && let Some(node_id) =
                                            node_id_for(subject.as_ref(), node_ids)
                                    {
                                        extra_node_ids.push(node_id);
                                    }
                                    if body_is_true
                                        && let Some(node_id) = node_id_for(body_expr, node_ids)
                                    {
                                        extra_node_ids.push(node_id);
                                    }
                                    // Opt-in: keep the fail-arm message
                                    // the default `expect` sugar drops,
                                    // rendered as `… or fail @"msg"`.
                                    let fail_message = if self.config.render_ctx.expect_or_fail() {
                                        extract_expect_fail_message(clauses)
                                    } else {
                                        None
                                    };
                                    tasks.push(Task::ExitWhenExpect {
                                        pattern,
                                        subject_name: rendered_subject_name,
                                        has_subject_expr,
                                        body_is_true,
                                        fail_message,
                                        extra_node_ids,
                                    });
                                    if !body_is_true {
                                        tasks.push(Task::Enter(body_expr));
                                    }
                                    if has_subject_expr {
                                        tasks.push(Task::Enter(subject.as_ref()));
                                    }
                                    continue;
                                }

                                let has_subject_expr = rendered_subject_name.is_none();
                                let body_groups = compute_when_body_groups(clauses);
                                tasks.push(Task::ExitWhen {
                                    subject_name: rendered_subject_name,
                                    clauses: clauses.as_slice(),
                                    has_subject_expr,
                                    wrap_subject_in_block: has_subject_expr
                                        && renders_as_statement_sequence(subject.as_ref()),
                                    extra_node_ids: if has_subject_expr {
                                        Vec::new()
                                    } else {
                                        node_id_for(subject.as_ref(), node_ids)
                                            .into_iter()
                                            .collect()
                                    },
                                    body_groups,
                                });
                                if has_subject_expr {
                                    tasks.push(Task::Enter(subject.as_ref()));
                                }
                                for clause in clauses.iter().rev() {
                                    tasks.push(Task::Enter(&clause.body));
                                    if let Some(guard) = &clause.guard {
                                        tasks.push(Task::Enter(guard));
                                    }
                                }
                            }

                            PseudoExpr::List { elements, tail } => {
                                if elements.is_empty() && tail.is_none() {
                                    out.push(arena.text("[]"));
                                } else {
                                    tasks.push(Task::ExitList {
                                        elements_len: elements.len(),
                                        has_tail: tail.is_some(),
                                    });
                                    if let Some(t) = tail {
                                        tasks.push(Task::Enter(t.as_ref()));
                                    }
                                    for element in elements.iter().rev() {
                                        tasks.push(Task::Enter(element));
                                    }
                                }
                            }

                            PseudoExpr::Tuple(elements) => {
                                tasks.push(Task::ExitTuple {
                                    len: elements.len(),
                                    force_multiline: elements
                                        .iter()
                                        .any(is_scott_constructor_application),
                                });
                                for element in elements.iter().rev() {
                                    tasks.push(Task::Enter(element));
                                }
                            }

                            PseudoExpr::Pair(first, second) => {
                                tasks.push(Task::ExitPair);
                                tasks.push(Task::Enter(second.as_ref()));
                                tasks.push(Task::Enter(first.as_ref()));
                            }

                            PseudoExpr::Constr {
                                type_hint,
                                tag,
                                fields,
                                shape,
                                ..
                            } => {
                                let pretty_label =
                                    self.registry.resolve(*shape, type_hint.as_ref());
                                if fields.is_empty() {
                                    let name_doc = match pretty_label.as_deref() {
                                        Some(n) => arena.text(n.to_string()),
                                        None => arena.text(format!("Constr<{}>", tag)),
                                    };
                                    out.push(name_doc);
                                } else {
                                    tasks.push(Task::ExitConstr {
                                        name: pretty_label,
                                        tag: *tag,
                                        fields_len: fields.len(),
                                        is_cons: matches!(
                                            shape,
                                            crate::pseudo::constructor::ConstructorShape::Known(
                                                crate::pseudo::constructor::KnownConstructor::Cons
                                            )
                                        ) && fields.len() == 2,
                                    });
                                    for field in fields.iter().rev() {
                                        // Statement-sequence constructor args get the
                                        // same block wrap as call args (see ExitApply).
                                        if renders_as_statement_sequence(field) {
                                            tasks.push(Task::ExitWrapOperand {
                                                needs_paren: false,
                                                force_block_parens: true,
                                            });
                                        }
                                        tasks.push(Task::Enter(field));
                                    }
                                }
                            }

                            PseudoExpr::FieldAccess {
                                record, selector, ..
                            } => {
                                // `.head` renders as `builtin.head_list(record)`
                                // only when compilable-data-access is ON; OFF
                                // (default) keeps the readable pseudo accessor via
                                // `ExitFieldAccess`. `ListHead` is always a list
                                // accessor, so no list-vs-tuple gate is needed.
                                if matches!(selector, FieldSelector::ListHead)
                                    && self.config.render_ctx.compilable_data_access()
                                {
                                    tasks.push(Task::ExitListHeadAccessor {
                                        wrap_record_in_block: renders_as_statement_sequence(
                                            record.as_ref(),
                                        ),
                                    });
                                    tasks.push(Task::Enter(record.as_ref()));
                                } else {
                                    tasks.push(Task::ExitFieldAccess {
                                        field: selector.as_surface_accessor(),
                                        wrap_record_in_block: renders_as_statement_sequence(
                                            record.as_ref(),
                                        ),
                                    });
                                    tasks.push(Task::Enter(record.as_ref()));
                                }
                            }

                            PseudoExpr::IndexAccess { collection, index } => {
                                // GATE A: lower `coll[N]` to
                                // `builtin.head_list(builtin.tail_list^N(coll))`
                                // only on a STRUCTURAL list proof — a direct list
                                // shape, or a binder `list_proof` proved (let-bound
                                // list values, when list-tails, fn params whose EVERY
                                // call site passes a provably-list arg).
                                // `IndexAccess` also indexes tuples and pairs, and
                                // neither `type_resolution()` (`Unknown` for Var,
                                // Apply, FieldAccess, BuiltinCall) nor a
                                // `FinalTypeTable` `List<_>` is trusted here: either
                                // would lower a tuple index to `head_list`, which is
                                // valid-looking and wrong. Everything else — OFF
                                // mode, binders no structural proof covers — keeps
                                // the honest bracket render.
                                let as_list = list_proof
                                    .as_ref()
                                    .is_some_and(|p| p.is_provably_list(collection.as_ref()));
                                tasks.push(Task::ExitIndexAccess {
                                    index: *index,
                                    wrap_collection_in_block: renders_as_statement_sequence(
                                        collection.as_ref(),
                                    ),
                                    as_list,
                                });
                                tasks.push(Task::Enter(collection.as_ref()));
                            }

                            PseudoExpr::BinOp { op, left, right } => {
                                if matches!(op, BinaryOp::Or)
                                    && let PseudoExpr::Trace { message, value } = right.as_ref()
                                    && matches!(value.as_ref(), PseudoExpr::Bool(false))
                                    && trace_message_is_droppable(message)
                                {
                                    tasks.push(Task::ExitBinOpTraceIfFalse {
                                        needs_parens: matches!(
                                            left.as_ref(),
                                            PseudoExpr::BinOp { .. } | PseudoExpr::If { .. }
                                        ),
                                    });
                                    tasks.push(Task::Enter(left.as_ref()));
                                    continue;
                                }

                                if matches!(op, BinaryOp::And)
                                    && let PseudoExpr::Trace { message: _, value } = right.as_ref()
                                    && matches!(value.as_ref(), PseudoExpr::Bool(true))
                                {
                                    tasks.push(Task::ExitBinOpTraceIfTrue {
                                        needs_parens: matches!(
                                            left.as_ref(),
                                            PseudoExpr::BinOp { .. } | PseudoExpr::If { .. }
                                        ),
                                    });
                                    tasks.push(Task::Enter(left.as_ref()));
                                    continue;
                                }

                                if matches!(op, BinaryOp::And | BinaryOp::Or) {
                                    let mut parts = Vec::new();
                                    collect_logical_chain(*op, left, &mut parts);
                                    collect_logical_chain(*op, right, &mut parts);

                                    if parts.len() >= 3 {
                                        tasks.push(Task::ExitBinOpLogicalChain {
                                            op: *op,
                                            parts_len: parts.len(),
                                        });
                                        for i in (0..parts.len()).rev() {
                                            let part = parts[i];
                                            tasks.push(Task::ExitWrapOperand {
                                                needs_paren: needs_paren_for(part, *op, i == 0),
                                                // In logical chains (&&/||), render Let blocks
                                                // inline without parentheses for flat readability.
                                                force_block_parens: false,
                                            });
                                            tasks.push(Task::Enter(part));
                                        }
                                        continue;
                                    }
                                }

                                tasks.push(Task::ExitBinOpDefault { op: *op });
                                tasks.push(Task::ExitWrapOperand {
                                    needs_paren: needs_paren_for(right.as_ref(), *op, false),
                                    // Block-wrap ANY statement-sequence operand
                                    // (`let …; e`, `expect …; e`, `seq(a, b)`,
                                    // or those under delay/force): an unwrapped
                                    // `expect c; b` operand is not valid surface syntax
                                    // and mis-parses against the operator.
                                    force_block_parens: renders_as_statement_sequence(
                                        right.as_ref(),
                                    ),
                                });
                                tasks.push(Task::Enter(right.as_ref()));
                                tasks.push(Task::ExitWrapOperand {
                                    needs_paren: needs_paren_for(left.as_ref(), *op, true),
                                    force_block_parens: renders_as_statement_sequence(
                                        left.as_ref(),
                                    ),
                                });
                                tasks.push(Task::Enter(left.as_ref()));
                            }

                            PseudoExpr::UnOp { op, operand } => match op {
                                UnaryOp::Not => {
                                    tasks.push(Task::ExitUnOpNot {
                                        needs_parens: matches!(
                                            operand.as_ref(),
                                            PseudoExpr::BinOp { .. }
                                                | PseudoExpr::If { .. }
                                                | PseudoExpr::Apply { .. }
                                        ),
                                    });
                                    tasks.push(Task::Enter(operand.as_ref()));
                                }
                                UnaryOp::Negate => {
                                    tasks.push(Task::ExitUnOpNegate);
                                    tasks.push(Task::Enter(operand.as_ref()));
                                }
                                UnaryOp::Length => {
                                    tasks.push(Task::ExitUnOpLength);
                                    tasks.push(Task::Enter(operand.as_ref()));
                                }
                            },

                            PseudoExpr::BuiltinCall { name, args } => {
                                if *name == crate::BuiltinId::Seq && args.len() == 2 {
                                    let stmts = collect_seq_chain(node);
                                    tasks.push(Task::ExitSeqChain {
                                        len: stmts.len(),
                                        extra_node_ids: collect_hidden_seq_chain_node_ids(
                                            node, node_ids,
                                        ),
                                    });
                                    for stmt in stmts.into_iter().rev() {
                                        tasks.push(Task::Enter(stmt));
                                    }
                                    continue;
                                }

                                if *name == crate::BuiltinId::ListPrepend
                                    && args.len() == 2
                                    && !matches!(args[1], PseudoExpr::List { .. })
                                {
                                    tasks.push(Task::ExitListPrependSugar);
                                    tasks.push(Task::Enter(&args[1]));
                                    tasks.push(Task::Enter(&args[0]));
                                    continue;
                                }

                                // List.tail(x) → x[1..], with chain collapsing
                                if *name == crate::BuiltinId::ListTail && args.len() == 1 {
                                    let (inner, depth) = count_tail_chain_any(&args[0]);
                                    tasks.push(Task::ExitSliceFrom {
                                        start: depth + 1,
                                        wrap_collection_in_block: renders_as_statement_sequence(
                                            inner,
                                        ),
                                        extra_node_ids: collect_hidden_tail_chain_node_ids(
                                            &args[0], node_ids,
                                        ),
                                    });
                                    tasks.push(Task::Enter(inner));
                                    continue;
                                }

                                if args.is_empty() {
                                    out.push(
                                        arena.text(
                                            data_access_builtin_name(
                                                *name,
                                                self.config.render_ctx.compilable_data_access(),
                                            )
                                            .to_string(),
                                        ),
                                    );
                                } else {
                                    tasks.push(Task::ExitBuiltinCall {
                                        name: *name,
                                        args_len: args.len(),
                                        force_multiline: should_force_multiline_call_args(args),
                                    });
                                    for arg in args.iter().rev() {
                                        tasks.push(Task::Enter(arg));
                                    }
                                }
                            }

                            PseudoExpr::Error { message } => {
                                out.push(match message {
                                    Some(msg) => {
                                        arena.text(format!("fail @\"{}\"", escape_string(msg)))
                                    }
                                    None => arena.text("fail"),
                                });
                            }

                            PseudoExpr::Delay(_) | PseudoExpr::Force(_) => {
                                let mut wrappers = Vec::new();
                                let mut current = node;
                                loop {
                                    match current {
                                        PseudoExpr::Delay(inner) => {
                                            wrappers.push(WrapperKind::Delay);
                                            current = inner.as_ref();
                                        }
                                        PseudoExpr::Force(inner) => {
                                            wrappers.push(WrapperKind::Force);
                                            current = inner.as_ref();
                                        }
                                        _ => break,
                                    }
                                }

                                // Standalone Force(x) → x() — thunk eval as zero-arg call.
                                // Only when the chain is a single Force (no delays mixed in).
                                if wrappers.len() == 1 && matches!(wrappers[0], WrapperKind::Force)
                                {
                                    tasks.push(Task::ExitApply {
                                        args_len: 0,
                                        force_multiline: false,
                                        extra_node_ids: if let PseudoExpr::Var { .. } = current {
                                            node_id_for(current, node_ids).into_iter().collect()
                                        } else {
                                            Vec::new()
                                        },
                                        leading_comment: Vec::new(),
                                    });
                                    // Suppress type annotation on Var in call position.
                                    if let PseudoExpr::Var { name, .. } = current {
                                        out.push(arena.text(sanitize_identifier(name)));
                                    } else {
                                        tasks.push(Task::Enter(current));
                                    }
                                    continue;
                                }

                                // Strip pure Delay chains: Delay(x), Delay(Delay(x)), etc.
                                // the surface has no `delay` keyword — thunking is UPLC-level noise.
                                if wrappers.iter().all(|w| matches!(w, WrapperKind::Delay)) {
                                    let extra_node_ids =
                                        collect_hidden_delay_force_chain_node_ids(node, node_ids);
                                    if !extra_node_ids.is_empty() {
                                        tasks.push(Task::ExitAnnotateNodes {
                                            node_ids: extra_node_ids,
                                        });
                                    }
                                    tasks.push(Task::Enter(current));
                                    continue;
                                }

                                tasks.push(Task::ExitDelayForceChain {
                                    wrappers,
                                    multiline: should_multiline_delay_force_body(current),
                                    extra_node_ids: collect_hidden_delay_force_chain_node_ids(
                                        node, node_ids,
                                    ),
                                });
                                tasks.push(Task::Enter(current));
                            }

                            PseudoExpr::Trace { message, value } => {
                                tasks.push(Task::ExitTrace);
                                tasks.push(Task::Enter(value.as_ref()));
                                tasks.push(Task::Enter(message.as_ref()));
                            }

                            PseudoExpr::Raw { uplc, reason } => {
                                if self.config.show_raw {
                                    out.push(
                                        arena
                                            .text("/* ")
                                            .append(arena.text(reason.clone()))
                                            .append(arena.text(" */"))
                                            .append(arena.hardline())
                                            .append(arena.text(uplc.clone())),
                                    );
                                } else {
                                    out.push(arena.text("<raw>"));
                                }
                            }

                            PseudoExpr::Data(data) => out.push(self.data_to_doc(arena, data)),

                            // The Y-comb intrinsic renders as bare
                            // `fix`, position-unaware: a misplaced
                            // `HelperSymbol(Fix)` (a `when` subject,
                            // say) also surfaces as a bare `fix`, so
                            // emit sites must always Apply-wrap it.
                            PseudoExpr::HelperSymbol(intrinsic) => {
                                out.push(arena.text(match intrinsic {
                                    crate::pseudo::ast::HelperIntrinsic::Fix => "fix",
                                }))
                            }
                        }
                    }

                    Task::FinalizeNode(node_id) => {
                        let doc = pop_doc(&mut out).annotate(node_id);
                        out.push(doc);
                    }

                    Task::ExitAnnotateNodes { node_ids } => {
                        let doc = pop_doc(&mut out);
                        out.push(annotate_doc_with_node_ids(doc, &node_ids));
                    }

                    Task::ExitLambda {
                        params,
                        lambda_node_id,
                        extra_node_ids,
                    } => {
                        let body_doc = pop_doc(&mut out);
                        let params_doc = arena.intersperse(
                            params
                                .iter()
                                .map(|p| arena.text(self.format_named_fn_param(p))),
                            arena.text(", "),
                        );

                        let doc = arena
                            .text("fn(")
                            .append(params_doc)
                            .append(arena.text(") {"))
                            .append(
                                arena
                                    .line()
                                    .append(body_doc)
                                    .nest(self.config.indent as isize),
                            )
                            .append(arena.line())
                            .append(arena.text("}"))
                            .group();

                        let doc = annotate_doc_with_node_ids(doc, &extra_node_ids);
                        out.push(if let Some(node_id) = lambda_node_id {
                            doc.annotate(node_id)
                        } else {
                            doc
                        });
                    }

                    Task::ExitRecFn { name, params } => {
                        let body_doc = pop_doc(&mut out);
                        let params_doc = arena.intersperse(
                            params
                                .iter()
                                .map(|p| arena.text(self.format_named_fn_param(p))),
                            arena.text(", "),
                        );

                        // `.nest`, not `.indent`: `.indent` ALWAYS
                        // adds leading whitespace, so it would
                        // indent the body in single-line "fits"
                        // mode; `.nest` adds it only after a line
                        // break. Matches the `ExitLambda` render.
                        out.push(
                            arena
                                .text("rec fn ")
                                .append(arena.text(sanitize_identifier(name)))
                                .append(arena.text("("))
                                .append(params_doc)
                                .append(arena.text(") {"))
                                .append(
                                    arena
                                        .line()
                                        .append(body_doc)
                                        .nest(self.config.indent as isize),
                                )
                                .append(arena.line())
                                .append(arena.text("}"))
                                .group(),
                        );
                    }

                    Task::ExitApply {
                        args_len,
                        force_multiline,
                        extra_node_ids,
                        leading_comment,
                    } => {
                        if args_len == 0 {
                            let func_doc = pop_doc(&mut out);
                            let doc = func_doc.append(arena.text("()"));
                            out.push(annotate_doc_with_node_ids(doc, &extra_node_ids));
                            continue;
                        }

                        let mut arg_docs = Vec::with_capacity(args_len);
                        for _ in 0..args_len {
                            arg_docs.push(pop_doc(&mut out));
                        }
                        arg_docs.reverse();
                        let func_doc = pop_doc(&mut out);

                        let doc = if force_multiline {
                            let args_doc = arena
                                .intersperse(arg_docs, arena.text(",").append(arena.hardline()));
                            func_doc
                                .append(arena.text("("))
                                .append(
                                    arena
                                        .hardline()
                                        .append(args_doc)
                                        .nest(self.config.indent as isize),
                                )
                                .append(arena.hardline())
                                .append(arena.text(")"))
                                .group()
                        } else {
                            let args_doc =
                                arena.intersperse(arg_docs, arena.text(",").append(arena.line()));
                            func_doc
                                .append(arena.text("("))
                                .append(args_doc.nest(self.config.indent as isize))
                                .append(arena.text(")"))
                                .group()
                        };
                        let doc = annotate_doc_with_node_ids(doc, &extra_node_ids);
                        let doc = if leading_comment.is_empty() {
                            doc
                        } else {
                            let mut prefixed = arena.nil();
                            for line in &leading_comment {
                                prefixed = prefixed
                                    .append(arena.text(line.clone()))
                                    .append(arena.hardline());
                            }
                            prefixed.append(doc)
                        };
                        out.push(doc);
                    }

                    Task::ExitLetRecFnSameName => {
                        let body_doc = pop_doc(&mut out);
                        let value_doc = pop_doc(&mut out);
                        out.push(value_doc.append(arena.hardline()).append(body_doc).group());
                    }

                    Task::ExitLetLambda {
                        name,
                        var_id,
                        params,
                        lambda_node_id,
                        fn_body,
                    } => {
                        let body_doc = pop_doc(&mut out);
                        let fn_body_doc = pop_doc(&mut out);
                        let params_doc = arena.intersperse(
                            params
                                .iter()
                                .map(|p| arena.text(self.format_named_fn_param(p))),
                            arena.text(", "),
                        );

                        let type_annotation = if self.config.show_types {
                            self.resolve_return_type_for_named_fn(var_id)
                                .filter(|t| {
                                    // Drop a `-> Bool` that a return
                                    // leaf provably contradicts.
                                    t != "Bool"
                                        || !bool_return_annotation_contradicted(
                                            fn_body,
                                            &non_bool_constr_bindings,
                                        )
                                })
                                .map(|t| format!(" -> {}", t))
                                .unwrap_or_default()
                        } else {
                            String::new()
                        };

                        // Church-decode marker (see ExitLetSimple) — for
                        // a function-style let it sits inline next to the
                        // closing `}`; skipped when the name conveys it.
                        let church_comment = church_notes
                            .get(var_id)
                            .filter(|tag| !is_church_tag_redundant(name, tag));

                        let doc = arena
                            .text("fn ")
                            .append(arena.text(sanitize_identifier(name)))
                            .append(arena.text("("))
                            .append(params_doc)
                            .append(arena.text(")"))
                            .append(arena.text(type_annotation))
                            .append(arena.text(" {"))
                            .append(arena.line())
                            .append(fn_body_doc.indent(self.config.indent))
                            .append(arena.line())
                            .append(arena.text("}"));
                        let doc = if let Some(tag) = church_comment {
                            doc.append(arena.text(format!("  // {}", tag)))
                        } else {
                            doc
                        };
                        let doc = doc.append(arena.hardline()).append(body_doc).group();

                        out.push(if let Some(node_id) = lambda_node_id {
                            doc.annotate(node_id)
                        } else {
                            doc
                        });
                    }

                    Task::ExitLetSimple {
                        name,
                        var_id,
                        inline_value,
                        wrap_value_in_block,
                        suppress_type,
                    } => {
                        let body_doc = pop_doc(&mut out);
                        let value_doc = pop_doc(&mut out);
                        let type_annotation = if self.config.show_types && !suppress_type {
                            self.resolve_type(var_id)
                                .map(|t| format!(": {}", t))
                                .unwrap_or_default()
                        } else {
                            String::new()
                        };

                        let mut binding_doc = arena
                            .text("let ")
                            .append(arena.text(sanitize_identifier(name)))
                            .append(arena.text(type_annotation))
                            .append(arena.text(" ="));

                        binding_doc = if wrap_value_in_block {
                            // Statement-sequence value (`let`/`expect`/`seq`
                            // chain) — brace it so `let X = …` parses.
                            binding_doc
                                .append(arena.text(" {"))
                                .append(
                                    arena
                                        .hardline()
                                        .append(value_doc)
                                        .nest(self.config.indent as isize),
                                )
                                .append(arena.hardline())
                                .append(arena.text("}"))
                        } else if inline_value {
                            binding_doc.append(arena.space()).append(value_doc)
                        } else {
                            binding_doc.append(
                                arena
                                    .line()
                                    .append(value_doc)
                                    .nest(self.config.indent as isize),
                            )
                        };

                        let binding_doc = binding_doc.group();

                        // Church-decode marker: `decode_church_to_native`
                        // stamps the VarId of every let value it rewrote,
                        // so a trailing `// <tag>` can show the encoding
                        // origin. Skipped when the name already conveys it.
                        let comment = church_notes
                            .get(var_id)
                            .filter(|tag| !is_church_tag_redundant(name, tag));
                        let binding_doc = if let Some(tag) = comment {
                            binding_doc.append(arena.text(format!("  // {}", tag)))
                        } else {
                            binding_doc
                        };

                        out.push(binding_doc.append(arena.hardline()).append(body_doc));
                    }

                    Task::ExitLetFlattened {
                        name,
                        var_id,
                        bindings,
                        resolved_value,
                        wrap_value_in_block,
                        aggregate_called_suppress,
                        extra_node_ids,
                    } => {
                        let body_doc = pop_doc(&mut out);
                        let resolved_doc = pop_doc(&mut out);
                        let mut binding_value_docs = Vec::with_capacity(bindings.len());
                        for _ in 0..bindings.len() {
                            binding_value_docs.push(pop_doc(&mut out));
                        }
                        binding_value_docs.reverse();

                        let mut doc = arena.nil();
                        for ((bname, bvar_id, bvalue), bvalue_doc) in
                            bindings.iter().zip(binding_value_docs)
                        {
                            // Drop the `: <type>` annotation when the
                            // value renders as a function (Lambda, RecFn,
                            // or a Let chain terminating in one) — unless
                            // the resolved final type is `Function`.
                            let suppress_type = (value_renders_as_function(bvalue)
                                && (!self.resolved_is_function(*bvar_id)
                                    || self.resolved_function_type_is_uninformative(*bvar_id)))
                                || self.bool_annotation_misses_constr_shape(*bvar_id, bvalue)
                                || self.function_type_on_non_function_value(*bvar_id, bvalue);
                            let type_annotation = if self.config.show_types && !suppress_type {
                                self.resolve_type(*bvar_id)
                                    .map(|t| format!(": {}", t))
                                    .unwrap_or_default()
                            } else {
                                String::new()
                            };

                            let inline_value = should_inline_let_value(bvalue);
                            doc = doc
                                .append(arena.text("let "))
                                .append(arena.text(sanitize_identifier(bname)))
                                .append(arena.text(type_annotation))
                                .append(arena.text(" ="));
                            doc = if renders_as_statement_sequence(bvalue) {
                                // Statement-sequence binding value — brace it
                                // so this flattened `let` parses.
                                doc.append(arena.space())
                                    .append(self.wrap_doc_in_block(arena, bvalue_doc))
                            } else if inline_value {
                                doc.append(arena.space()).append(bvalue_doc)
                            } else {
                                doc.append(
                                    arena
                                        .line()
                                        .append(bvalue_doc)
                                        .nest(self.config.indent as isize),
                                )
                            }
                            .group()
                            .append(arena.hardline());
                        }

                        // Same suppression for the final flattened-let head,
                        // plus the case where `resolved_value` is a Var
                        // referencing an inner binding whose value renders
                        // as a function (`value_renders_as_function` again,
                        // so Let chains peek through uniformly).
                        let suppress_final_type = ((value_renders_as_function(resolved_value)
                            || matches!(resolved_value, PseudoExpr::Var { id: Some(target_id), .. }
                            if bindings.iter().any(|(_, bid, bval)| {
                                bid == target_id && value_renders_as_function(bval)
                            })))
                            && (!self.resolved_is_function(var_id)
                                || self.resolved_function_type_is_uninformative(var_id)))
                            || self.function_type_on_non_function_value(var_id, resolved_value)
                            || aggregate_called_suppress;
                        let type_annotation = if self.config.show_types && !suppress_final_type {
                            self.resolve_type(var_id)
                                .map(|t| format!(": {}", t))
                                .unwrap_or_default()
                        } else {
                            String::new()
                        };

                        let inline_resolved = should_inline_let_value(resolved_value);
                        doc = doc
                            .append(arena.text("let "))
                            .append(arena.text(sanitize_identifier(name)))
                            .append(arena.text(type_annotation))
                            .append(arena.text(" ="));
                        doc = if wrap_value_in_block {
                            // Statement-sequence resolved value — wrap in
                            // `{ … }` (see ExitLetSimple).
                            doc.append(arena.text(" {"))
                                .append(
                                    arena
                                        .hardline()
                                        .append(resolved_doc)
                                        .nest(self.config.indent as isize),
                                )
                                .append(arena.hardline())
                                .append(arena.text("}"))
                        } else if inline_resolved {
                            doc.append(arena.space()).append(resolved_doc)
                        } else {
                            doc.append(
                                arena
                                    .line()
                                    .append(resolved_doc)
                                    .nest(self.config.indent as isize),
                            )
                        }
                        .group()
                        .append(arena.hardline())
                        .append(body_doc);

                        out.push(annotate_doc_with_node_ids(doc, &extra_node_ids));
                    }

                    Task::ExitIfChain {
                        branches,
                        extra_node_ids,
                    } => {
                        let else_doc = pop_doc(&mut out);
                        let mut branch_docs = Vec::with_capacity(branches.len());
                        for _ in 0..branches.len() {
                            let then_doc = pop_doc(&mut out);
                            let cond_doc = pop_doc(&mut out);
                            branch_docs.push((cond_doc, then_doc));
                        }
                        branch_docs.reverse();

                        let (first_cond, first_then) = branch_docs.remove(0);
                        let mut doc = arena
                            .text("if ")
                            .append(first_cond)
                            .append(arena.text(" {"))
                            .append(arena.hardline())
                            .append(first_then.indent(self.config.indent))
                            .append(arena.hardline());

                        for (cond_doc, then_doc) in branch_docs {
                            doc = doc
                                .append(arena.text("} else if "))
                                .append(cond_doc)
                                .append(arena.text(" {"))
                                .append(arena.hardline())
                                .append(then_doc.indent(self.config.indent))
                                .append(arena.hardline());
                        }

                        let doc = doc
                            .append(arena.text("} else {"))
                            .append(arena.hardline())
                            .append(else_doc.indent(self.config.indent))
                            .append(arena.hardline())
                            .append(arena.text("}"));
                        out.push(annotate_doc_with_node_ids(doc, &extra_node_ids));
                    }

                    Task::ExitSortedAssocLookupIf {
                        cutoff_op,
                        extra_node_ids,
                    } => {
                        let else_doc = pop_doc(&mut out);
                        let none_doc = pop_doc(&mut out);
                        let cutoff_right_doc = pop_doc(&mut out);
                        let cutoff_left_doc = pop_doc(&mut out);
                        let some_doc = pop_doc(&mut out);
                        let eq_doc = pop_doc(&mut out);

                        let cutoff_doc = cutoff_left_doc
                            .append(arena.text(format!(" {} ", cutoff_op.symbol())))
                            .append(cutoff_right_doc)
                            .group();

                        let doc = arena
                            .text("if ")
                            .append(eq_doc)
                            .append(arena.text(" {"))
                            .append(arena.hardline())
                            .append(some_doc.indent(self.config.indent))
                            .append(arena.hardline())
                            .append(arena.text("} else if "))
                            .append(cutoff_doc)
                            .append(arena.text(" {"))
                            .append(arena.hardline())
                            .append(none_doc.indent(self.config.indent))
                            .append(arena.hardline())
                            .append(arena.text("} else {"))
                            .append(arena.hardline())
                            .append(else_doc.indent(self.config.indent))
                            .append(arena.hardline())
                            .append(arena.text("}"));
                        out.push(annotate_doc_with_node_ids(doc, &extra_node_ids));
                    }

                    Task::ExitWhenExpect {
                        pattern,
                        subject_name,
                        has_subject_expr,
                        body_is_true,
                        fail_message,
                        extra_node_ids,
                    } => {
                        let body_doc = if body_is_true {
                            None
                        } else {
                            Some(pop_doc(&mut out))
                        };
                        let subject_doc = if has_subject_expr {
                            pop_doc(&mut out)
                        } else {
                            arena.text(sanitize_identifier(
                                subject_name.expect("subject_name missing for named expect"),
                            ))
                        };
                        let pattern_doc =
                            self.pattern_to_doc(arena, pattern, node_ids, church_notes);

                        let mut expect_line = arena
                            .text("expect ")
                            .append(pattern_doc)
                            .append(arena.text(" = "))
                            .append(subject_doc);
                        // Opt-in: re-attach the dropped fail-arm message as
                        // `or fail @"msg"`, matching the `Error` render.
                        if let Some(msg) = fail_message {
                            expect_line = expect_line.append(
                                arena.text(format!(" or fail @\"{}\"", escape_string(msg))),
                            );
                        }
                        let doc = if let Some(body_doc) = body_doc {
                            expect_line.append(arena.hardline()).append(body_doc)
                        } else {
                            // Body is True — just emit the expect assertion
                            expect_line
                        };
                        out.push(annotate_doc_with_node_ids(doc, &extra_node_ids));
                    }

                    Task::ExitWhen {
                        subject_name,
                        clauses,
                        has_subject_expr,
                        wrap_subject_in_block,
                        extra_node_ids,
                        body_groups,
                    } => {
                        let subject_doc = if has_subject_expr {
                            let popped = pop_doc(&mut out);
                            if wrap_subject_in_block {
                                // Statement-sequence subject (`let`/`expect`/
                                // `seq` chain) — brace it so the `when`
                                // subject is one expression.
                                arena
                                    .text("{")
                                    .append(
                                        arena
                                            .hardline()
                                            .append(popped)
                                            .nest(self.config.indent as isize),
                                    )
                                    .append(arena.hardline())
                                    .append(arena.text("}"))
                            } else {
                                popped
                            }
                        } else {
                            arena.text(sanitize_identifier(
                                subject_name.expect("subject_name missing for named when"),
                            ))
                        };

                        // Pop bodies (and guards) in reverse, so
                        // `popped_bodies[i]` belongs to clauses[i].
                        // Non-leader bodies in a group are discarded.
                        let mut popped_bodies: Vec<DocBuilder<'_, _, _>> =
                            Vec::with_capacity(clauses.len());
                        let mut popped_guards: Vec<Option<DocBuilder<'_, _, _>>> =
                            Vec::with_capacity(clauses.len());
                        for clause in clauses.iter().rev() {
                            popped_bodies.push(pop_doc(&mut out));
                            popped_guards.push(clause.guard.as_ref().map(|_| pop_doc(&mut out)));
                        }
                        popped_bodies.reverse();
                        popped_guards.reverse();

                        let mut clause_docs = Vec::with_capacity(body_groups.len());
                        for group in &body_groups {
                            let leader = group[0];
                            let leader_clause = &clauses[leader];
                            let body_doc = popped_bodies[leader].clone();
                            // Build alt-pattern doc: `P1 | P2 | … `.
                            let pattern_docs: Vec<_> = group
                                .iter()
                                .map(|&idx| {
                                    self.pattern_to_doc(
                                        arena,
                                        &clauses[idx].pattern,
                                        node_ids,
                                        church_notes,
                                    )
                                })
                                .collect();
                            let pattern_doc = arena.intersperse(pattern_docs, arena.text(" | "));
                            let with_guard = if leader_clause.guard.is_some() {
                                let guard_doc = popped_guards[leader].clone().expect("guard");
                                pattern_doc.append(arena.text(" if ")).append(guard_doc)
                            } else {
                                pattern_doc
                            };

                            clause_docs.push(
                                with_guard
                                    .append(arena.text(" ->"))
                                    .append(
                                        arena
                                            .line()
                                            .append(body_doc)
                                            .nest(self.config.indent as isize),
                                    )
                                    .group(),
                            );
                        }

                        let clauses_doc = arena.intersperse(clause_docs, arena.hardline());
                        let doc = arena
                            .text("when ")
                            .append(subject_doc)
                            .append(arena.text(" is {"))
                            .append(arena.hardline())
                            .append(clauses_doc.indent(self.config.indent))
                            .append(arena.hardline())
                            .append(arena.text("}"));
                        out.push(annotate_doc_with_node_ids(doc, &extra_node_ids));
                    }

                    Task::ExitList {
                        elements_len,
                        has_tail,
                    } => {
                        let mut items = Vec::with_capacity(elements_len + usize::from(has_tail));
                        let tail_doc = if has_tail {
                            Some(pop_doc(&mut out))
                        } else {
                            None
                        };

                        let mut element_docs = Vec::with_capacity(elements_len);
                        for _ in 0..elements_len {
                            element_docs.push(pop_doc(&mut out));
                        }
                        element_docs.reverse();
                        items.extend(element_docs);
                        if let Some(t) = tail_doc {
                            items.push(arena.text("..").append(t));
                        }

                        // The comma join offers no break opportunity, so a
                        // wide literal renders as one mega-line. Measure the
                        // list's OWN flat width and emit one element per
                        // line past the configured width. The own-width (not
                        // column-aware) trigger keeps short nested literals
                        // (`[d_result_result]`) flat instead of cascading
                        // breaks through every nesting level.
                        let flat = arena
                            .text("[")
                            .append(arena.intersperse(items.clone(), arena.text(", ")))
                            .append(arena.text("]"))
                            .group();
                        let flat_len = {
                            let mut s = String::new();
                            flat.clone().render_fmt(self.config.width, &mut s).unwrap();
                            s.lines().map(str::len).max().unwrap_or(0)
                        };
                        let doc = if flat_len > self.config.width {
                            let elems =
                                arena.intersperse(items, arena.text(",").append(arena.hardline()));
                            arena
                                .text("[")
                                .append(
                                    arena
                                        .hardline()
                                        .append(elems)
                                        .nest(self.config.indent as isize),
                                )
                                .append(arena.hardline())
                                .append(arena.text("]"))
                        } else {
                            flat
                        };
                        out.push(doc);
                    }

                    Task::ExitTuple {
                        len,
                        force_multiline,
                    } => {
                        let mut docs = Vec::with_capacity(len);
                        for _ in 0..len {
                            docs.push(pop_doc(&mut out));
                        }
                        docs.reverse();

                        let doc = if force_multiline {
                            let elems =
                                arena.intersperse(docs, arena.text(",").append(arena.hardline()));
                            arena
                                .text("(")
                                .append(
                                    arena
                                        .hardline()
                                        .append(elems)
                                        .nest(self.config.indent as isize),
                                )
                                .append(arena.hardline())
                                .append(arena.text(")"))
                                .group()
                        } else {
                            arena
                                .text("(")
                                .append(arena.intersperse(docs, arena.text(", ")))
                                .append(arena.text(")"))
                                .group()
                        };
                        out.push(doc);
                    }

                    Task::ExitPair => {
                        let second_doc = pop_doc(&mut out);
                        let first_doc = pop_doc(&mut out);
                        out.push(
                            arena
                                .text("Pair(")
                                .append(first_doc)
                                .append(arena.text(", "))
                                .append(second_doc)
                                .append(arena.text(")"))
                                .group(),
                        );
                    }

                    Task::ExitConstr {
                        name,
                        tag,
                        fields_len,
                        is_cons,
                    } => {
                        let mut field_docs = Vec::with_capacity(fields_len);
                        for _ in 0..fields_len {
                            field_docs.push(pop_doc(&mut out));
                        }
                        field_docs.reverse();

                        if is_cons && field_docs.len() == 2 {
                            // `[head, ..tail]` list-spread sugar (expression
                            // position), mirroring the pattern-position render.
                            let tail = field_docs.pop().expect("cons tail doc");
                            let head = field_docs.pop().expect("cons head doc");
                            out.push(
                                arena
                                    .text("[")
                                    .append(head)
                                    .append(arena.text(", .."))
                                    .append(tail)
                                    .append(arena.text("]"))
                                    .group(),
                            );
                        } else {
                            let name_doc = match name {
                                Some(n) => arena.text(n.to_string()),
                                None => arena.text(format!("Constr<{}>", tag)),
                            };

                            out.push(
                                name_doc
                                    .append(arena.text("("))
                                    .append(arena.intersperse(field_docs, arena.text(", ")))
                                    .append(arena.text(")"))
                                    .group(),
                            );
                        }
                    }

                    Task::ExitFieldAccess {
                        field,
                        wrap_record_in_block,
                    } => {
                        let record_doc = pop_doc(&mut out);
                        let record_doc = if wrap_record_in_block {
                            self.wrap_doc_in_block(arena, record_doc)
                        } else {
                            record_doc
                        };
                        out.push(
                            record_doc
                                .append(arena.text("."))
                                .append(arena.text(field.to_string())),
                        );
                    }

                    Task::ExitIndexAccess {
                        index,
                        wrap_collection_in_block,
                        as_list,
                    } => {
                        let collection_doc = pop_doc(&mut out);
                        let collection_doc = if wrap_collection_in_block {
                            self.wrap_doc_in_block(arena, collection_doc)
                        } else {
                            collection_doc
                        };
                        if as_list {
                            // GATE A: list-like `coll[N]` →
                            // `builtin.head_list(builtin.tail_list^N(coll))`.
                            let tailed = wrap_in_tail_list(arena, collection_doc, index);
                            out.push(wrap_in_call(arena, head_list_name, tailed));
                        } else {
                            // Tuple/Pair index: keep the bracket render.
                            out.push(collection_doc.append(arena.text(format!("[{}]", index))));
                        }
                    }

                    Task::ExitSliceFrom {
                        start,
                        wrap_collection_in_block,
                        extra_node_ids,
                    } => {
                        let collection_doc = pop_doc(&mut out);
                        let collection_doc = if wrap_collection_in_block {
                            self.wrap_doc_in_block(arena, collection_doc)
                        } else {
                            collection_doc
                        };
                        // The `[N..]` slice (a `ListTail` chain) is
                        // list-only, so it needs no gate. ON renders N nested
                        // `builtin.tail_list(coll)`; OFF keeps `coll[N..]`.
                        let doc = if self.config.render_ctx.compilable_data_access() {
                            wrap_in_tail_list(arena, collection_doc, start)
                        } else {
                            collection_doc.append(arena.text(format!("[{}..]", start)))
                        };
                        out.push(annotate_doc_with_node_ids(doc, &extra_node_ids));
                    }

                    Task::ExitListHeadAccessor {
                        wrap_record_in_block,
                    } => {
                        // `.head` → `builtin.head_list(record)`.
                        let record_doc = pop_doc(&mut out);
                        let record_doc = if wrap_record_in_block {
                            self.wrap_doc_in_block(arena, record_doc)
                        } else {
                            record_doc
                        };
                        out.push(wrap_in_call(arena, head_list_name, record_doc));
                    }

                    Task::ExitWrapOperand {
                        needs_paren,
                        force_block_parens,
                    } => {
                        let doc = pop_doc(&mut out);
                        if force_block_parens {
                            out.push(
                                arena
                                    .text("(")
                                    .append(
                                        arena
                                            .hardline()
                                            .append(doc)
                                            .nest(self.config.indent as isize),
                                    )
                                    .append(arena.hardline())
                                    .append(arena.text(")")),
                            );
                        } else if needs_paren {
                            out.push(arena.text("(").append(doc).append(arena.text(")")));
                        } else {
                            out.push(doc);
                        }
                    }

                    Task::ExitBinOpTraceIfFalse { needs_parens } => {
                        let left_doc = pop_doc(&mut out);
                        if needs_parens {
                            out.push(arena.text("(").append(left_doc).append(arena.text(")?")));
                        } else {
                            out.push(left_doc.append(arena.text("?")));
                        }
                    }

                    Task::ExitBinOpTraceIfTrue { needs_parens } => {
                        let left_doc = pop_doc(&mut out);
                        if needs_parens {
                            out.push(arena.text("!(").append(left_doc).append(arena.text(")?")));
                        } else {
                            out.push(arena.text("!").append(left_doc).append(arena.text("?")));
                        }
                    }

                    Task::ExitBinOpDefault { op } => {
                        let right_doc = pop_doc(&mut out);
                        let left_doc = pop_doc(&mut out);
                        out.push(
                            left_doc
                                .append(arena.text(format!(" {} ", op.symbol())))
                                .append(right_doc)
                                .group(),
                        );
                    }

                    Task::ExitBinOpLogicalChain { op, parts_len } => {
                        let mut docs = Vec::with_capacity(parts_len);
                        for _ in 0..parts_len {
                            docs.push(pop_doc(&mut out));
                        }
                        docs.reverse();

                        let sep = arena
                            .text(format!(" {}", op.symbol()))
                            .append(arena.hardline());
                        out.push(arena.intersperse(docs, sep).group());
                    }

                    Task::ExitUnOpNot { needs_parens } => {
                        let operand_doc = pop_doc(&mut out);
                        if needs_parens {
                            out.push(arena.text("!(").append(operand_doc).append(arena.text(")")));
                        } else {
                            out.push(arena.text("!").append(operand_doc));
                        }
                    }

                    Task::ExitUnOpNegate => {
                        let operand_doc = pop_doc(&mut out);
                        out.push(arena.text("-").append(operand_doc));
                    }

                    Task::ExitUnOpLength => {
                        let operand_doc = pop_doc(&mut out);
                        out.push(
                            arena
                                .text("length(")
                                .append(operand_doc)
                                .append(arena.text(")")),
                        );
                    }

                    Task::ExitBuiltinCall {
                        name,
                        args_len,
                        force_multiline,
                    } => {
                        // OFF (default) renders the pseudo `Constr.unpack` /
                        // `List.head` / `List.tail` / `List.is_empty`; ON the
                        // compilable `builtin.*` surface.
                        let display_name = data_access_builtin_name(
                            name,
                            self.config.render_ctx.compilable_data_access(),
                        );
                        let mut arg_docs = Vec::with_capacity(args_len);
                        for _ in 0..args_len {
                            arg_docs.push(pop_doc(&mut out));
                        }
                        arg_docs.reverse();

                        if force_multiline {
                            let args_doc = arena
                                .intersperse(arg_docs, arena.text(",").append(arena.hardline()));
                            out.push(
                                arena
                                    .text(display_name.to_string())
                                    .append(arena.text("("))
                                    .append(
                                        arena
                                            .hardline()
                                            .append(args_doc)
                                            .nest(self.config.indent as isize),
                                    )
                                    .append(arena.hardline())
                                    .append(arena.text(")"))
                                    .group(),
                            );
                        } else {
                            let args_doc =
                                arena.intersperse(arg_docs, arena.text(",").append(arena.line()));
                            out.push(
                                arena
                                    .text(display_name.to_string())
                                    .append(arena.text("("))
                                    .append(args_doc.nest(self.config.indent as isize))
                                    .append(arena.text(")"))
                                    .group(),
                            );
                        }
                    }

                    Task::ExitListPrependSugar => {
                        let tail_doc = pop_doc(&mut out);
                        let elem_doc = pop_doc(&mut out);
                        out.push(
                            arena
                                .text("[")
                                .append(elem_doc)
                                .append(arena.text(", .."))
                                .append(tail_doc)
                                .append(arena.text("]"))
                                .group(),
                        );
                    }

                    Task::ExitSeqChain {
                        len,
                        extra_node_ids,
                    } => {
                        let mut docs = Vec::with_capacity(len);
                        for _ in 0..len {
                            docs.push(pop_doc(&mut out));
                        }
                        docs.reverse();
                        let doc = arena.intersperse(docs, arena.hardline());
                        out.push(annotate_doc_with_node_ids(doc, &extra_node_ids));
                    }

                    Task::ExitExpectChain {
                        has_messages,
                        extra_node_ids,
                    } => {
                        let value_doc = pop_doc(&mut out);
                        let mut cond_entries: Vec<(PrettyDoc, Option<PrettyDoc>)> =
                            Vec::with_capacity(has_messages.len());
                        for has_msg in has_messages.iter().rev() {
                            let msg = if *has_msg {
                                Some(pop_doc(&mut out))
                            } else {
                                None
                            };
                            let cond = pop_doc(&mut out);
                            cond_entries.push((cond, msg));
                        }
                        cond_entries.reverse();

                        let mut parts = Vec::with_capacity(cond_entries.len() + 1);
                        for (cond_doc, msg_doc) in cond_entries {
                            // Render the surface `expect <bool_cond>`. The internal helper
                            // symbol stays "expect!", a non-identifier marker.
                            let line = arena.text("expect").append(arena.space()).append(cond_doc);
                            let line = if let Some(msg_doc) = msg_doc {
                                line.append(arena.text(", ")).append(msg_doc)
                            } else {
                                line
                            };
                            parts.push(line);
                        }
                        // The final value prints even when it is `Void`: a
                        // chain ending the surrounding block would otherwise
                        // close on a bare `expect …`, an assertion with no
                        // result. The `Void` is the chain's honest value.
                        parts.push(value_doc);
                        let doc = arena.intersperse(parts, arena.hardline());
                        out.push(annotate_doc_with_node_ids(doc, &extra_node_ids));
                    }

                    Task::ExitDelayForceChain {
                        wrappers,
                        multiline,
                        extra_node_ids,
                    } => {
                        let mut doc = pop_doc(&mut out);
                        for wrapper in wrappers.into_iter().rev() {
                            let name = match wrapper {
                                WrapperKind::Delay => "delay(",
                                WrapperKind::Force => "force(",
                            };
                            doc = if multiline {
                                arena
                                    .text(name)
                                    .append(
                                        arena
                                            .hardline()
                                            .append(doc)
                                            .nest(self.config.indent as isize),
                                    )
                                    .append(arena.hardline())
                                    .append(arena.text(")"))
                                    .group()
                            } else {
                                arena.text(name).append(doc).append(arena.text(")"))
                            };
                        }
                        out.push(annotate_doc_with_node_ids(doc, &extra_node_ids));
                    }

                    Task::ExitTrace => {
                        let value_doc = pop_doc(&mut out);
                        let message_doc = pop_doc(&mut out);
                        // Render the 2-arg trace as `trace MSG: VAL`. The
                        // colon ties VAL to the trace; without it the two
                        // read as unrelated expressions inside a larger one
                        // (Apply arg, BinOp arm), hiding that
                        // `Bool || trace MSG VAL` is `Bool || VAL`.
                        out.push(
                            arena
                                .text("trace ")
                                .append(message_doc)
                                .append(arena.text(": "))
                                .append(value_doc),
                        );
                    }

                    Task::ExitRootLambdaThenHelpers { helper_len } => {
                        let mut helper_docs = Vec::with_capacity(helper_len);
                        for _ in 0..helper_len {
                            helper_docs.push(pop_doc(&mut out));
                        }
                        helper_docs.reverse();
                        let lambda_doc = pop_doc(&mut out);

                        let doc = helper_docs.into_iter().fold(lambda_doc, |doc, helper_doc| {
                            doc.append(arena.hardline()).append(helper_doc)
                        });
                        out.push(doc.group());
                    }

                    Task::ExitRootNamedLambda {
                        name,
                        var_id,
                        params,
                        lambda_node_id,
                        fn_body,
                    } => {
                        let fn_body_doc = pop_doc(&mut out);
                        let params_doc = arena.intersperse(
                            params
                                .iter()
                                .map(|p| arena.text(self.format_named_fn_param(p))),
                            arena.text(", "),
                        );

                        let type_annotation = if self.config.show_types {
                            self.resolve_return_type_for_named_fn(var_id)
                                .filter(|t| {
                                    // Drop a `-> Bool` that a return
                                    // leaf provably contradicts.
                                    t != "Bool"
                                        || !bool_return_annotation_contradicted(
                                            fn_body,
                                            &non_bool_constr_bindings,
                                        )
                                })
                                .map(|t| format!(" -> {}", t))
                                .unwrap_or_default()
                        } else {
                            String::new()
                        };

                        let doc = arena
                            .text("fn ")
                            .append(arena.text(sanitize_identifier(name)))
                            .append(arena.text("("))
                            .append(params_doc)
                            .append(arena.text(")"))
                            .append(arena.text(type_annotation))
                            .append(arena.text(" {"))
                            .append(arena.line())
                            .append(fn_body_doc.indent(self.config.indent))
                            .append(arena.line())
                            .append(arena.text("}"))
                            .group();

                        out.push(if let Some(node_id) = lambda_node_id {
                            doc.annotate(node_id)
                        } else {
                            doc
                        });
                    }

                    Task::ExitParameterLet { name, var_id } => {
                        let value_doc = pop_doc(&mut out);
                        let type_annotation = if self.config.show_types {
                            self.resolve_type(var_id)
                                .map(|t| format!(": {}", t))
                                .unwrap_or_default()
                        } else {
                            String::new()
                        };
                        let doc = arena
                            .text("let ")
                            .append(arena.text(sanitize_identifier(name)))
                            .append(arena.text(type_annotation))
                            .append(arena.text(" ="))
                            .append(arena.softline())
                            .append(value_doc)
                            .group();
                        out.push(doc);
                    }

                    Task::ExitParametrizedScript {
                        param_count,
                        helper_count,
                    } => {
                        let mut helper_docs = Vec::with_capacity(helper_count);
                        for _ in 0..helper_count {
                            helper_docs.push(pop_doc(&mut out));
                        }
                        helper_docs.reverse();
                        let lambda_doc = pop_doc(&mut out);
                        let mut param_docs = Vec::with_capacity(param_count);
                        for _ in 0..param_count {
                            param_docs.push(pop_doc(&mut out));
                        }
                        param_docs.reverse();

                        let mut doc = arena.text("// Parameters").append(arena.hardline());
                        let params_section = param_docs.into_iter().enumerate().fold(
                            arena.nil(),
                            |acc, (i, param_doc)| {
                                if i == 0 {
                                    acc.append(param_doc)
                                } else {
                                    acc.append(arena.hardline()).append(param_doc)
                                }
                            },
                        );
                        doc = doc
                            .append(params_section)
                            .append(arena.hardline())
                            .append(arena.hardline())
                            .append(arena.text("// Main"))
                            .append(arena.hardline())
                            .append(lambda_doc);

                        if !helper_docs.is_empty() {
                            let helpers_section = helper_docs.into_iter().enumerate().fold(
                                arena.nil(),
                                |acc, (i, helper_doc)| {
                                    if i == 0 {
                                        acc.append(helper_doc)
                                    } else {
                                        acc.append(arena.hardline()).append(helper_doc)
                                    }
                                },
                            );
                            doc = doc
                                .append(arena.hardline())
                                .append(arena.hardline())
                                .append(arena.text("// Helpers"))
                                .append(arena.hardline())
                                .append(helpers_section);
                        }

                        out.push(doc.group());
                    }
                }
            }

            pop_doc(&mut out)
        })
    }

    /// Wrap a rendered doc in a `{ … }` block on its own lines. Used
    /// to make a statement-sequence value (`let`/`expect`/`seq` chain)
    /// legal in a single-expression position — a `let` value, a `when`
    /// subject, or a `record`/`collection` being projected.
    fn wrap_doc_in_block<'a>(
        &self,
        arena: &'a PrettyArena<'a>,
        inner: PrettyDoc<'a>,
    ) -> PrettyDoc<'a> {
        arena
            .text("{")
            .append(
                arena
                    .hardline()
                    .append(inner)
                    .nest(self.config.indent as isize),
            )
            .append(arena.hardline())
            .append(arena.text("}"))
    }

    /// Convert a pattern to a document.
    fn pattern_to_doc<'a>(
        &self,
        arena: &'a PrettyArena<'a>,
        pattern: &WhenPattern,
        node_ids: &HashMap<usize, PseudoNodeId>,
        church_notes: &crate::decompile::render_prep::ChurchLetComments,
    ) -> PrettyDoc<'a> {
        match pattern {
            WhenPattern::Constructor {
                type_hint,
                tag,
                fields,
                shape,
                ..
            } => {
                use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
                // idiomatic list patterns:
                //   `KnownConstructor::Nil` with no fields → `[]`
                //   `KnownConstructor::Cons` with [h, t] → `[h, ..t]`
                // Any other arity falls through to the generic
                // `Cons(h, t)` form, keeping `Nil`/`Cons` out of
                // pattern positions where surface expects list syntax.
                if let ConstructorShape::Known(kc) = shape {
                    match kc {
                        KnownConstructor::Nil if fields.is_empty() => {
                            return arena.text("[]");
                        }
                        KnownConstructor::Cons if fields.len() == 2 => {
                            let head_name = sanitize_identifier(fields[0].as_ref());
                            let tail_name = sanitize_identifier(fields[1].as_ref());
                            let tail_text = if tail_name == "_" {
                                "..".to_string()
                            } else {
                                format!("..{}", tail_name)
                            };
                            return arena
                                .text("[")
                                .append(arena.text(head_name))
                                .append(arena.text(", "))
                                .append(arena.text(tail_text))
                                .append(arena.text("]"));
                        }
                        _ => {}
                    }
                }
                let pretty_label = self.registry.resolve(*shape, type_hint.as_ref());
                let name_doc = match pretty_label.as_deref() {
                    Some(n) => arena.text(n.to_string()),
                    None => arena.text(format!("Constr<{}>", tag)),
                };

                // A constructor with more arity than the pattern binds
                // needs `_` padding to render as valid surface syntax:
                //   - `fields.is_empty()` with `expected_arity > 0` —
                //     a `Data.case` shape-test binds no fields though
                //     `Data.Constr` has arity 2; emit `Constr(_, _)`.
                //   - `fields.len() < expected_arity` — partial bind,
                //     pad the trailing slots with `_`.
                let expected_arity =
                    expected_pattern_arity(pretty_label.as_deref(), type_hint.as_ref(), *shape);
                if fields.is_empty() && expected_arity == 0 {
                    name_doc
                } else if fields.is_empty() {
                    let wildcards = arena.intersperse(
                        (0..expected_arity).map(|_| arena.text("_")),
                        arena.text(", "),
                    );
                    name_doc
                        .append(arena.text("("))
                        .append(wildcards)
                        .append(arena.text(")"))
                } else if fields.len() < expected_arity {
                    let missing = expected_arity - fields.len();
                    let parts: Vec<PrettyDoc<'a>> = fields
                        .iter()
                        .map(|f| arena.text(sanitize_identifier(f.as_ref())))
                        .chain((0..missing).map(|_| arena.text("_")))
                        .collect();
                    let fields_doc = arena.intersperse(parts, arena.text(", "));
                    name_doc
                        .append(arena.text("("))
                        .append(fields_doc)
                        .append(arena.text(")"))
                } else {
                    let fields_doc = arena.intersperse(
                        fields
                            .iter()
                            .map(|f| arena.text(sanitize_identifier(f.as_ref()))),
                        arena.text(", "),
                    );
                    name_doc
                        .append(arena.text("("))
                        .append(fields_doc)
                        .append(arena.text(")"))
                }
            }
            WhenPattern::List { elements, tail } => {
                let mut items: Vec<PrettyDoc<'a>> = elements
                    .iter()
                    .map(|e| arena.text(sanitize_identifier(e.as_ref())))
                    .collect();

                if let Some(t) = tail {
                    // `Binder { name: "_" }` is the ignore-tail sentinel
                    // minted by synthetic passes (`lift_list_fold_to_when`
                    // when the body indexes the subject instead of the
                    // bound tail). the surface prefers bare `..`; `.._` is a
                    // tail named `_` — valid, but noisy.
                    if t.as_str() == "_" {
                        items.push(arena.text(".."));
                    } else {
                        items.push(arena.text(format!("..{}", sanitize_identifier(t.as_ref()))));
                    }
                }

                arena
                    .text("[")
                    .append(arena.intersperse(items, arena.text(", ")))
                    .append(arena.text("]"))
            }
            WhenPattern::Tuple(fields) => {
                let docs = fields
                    .iter()
                    .map(|f| arena.text(sanitize_identifier(f.as_ref())));
                arena
                    .text("(")
                    .append(arena.intersperse(docs, arena.text(", ")))
                    .append(arena.text(")"))
            }
            WhenPattern::Pair(a, b) => arena
                .text("Pair(")
                .append(arena.text(sanitize_identifier(a.as_ref())))
                .append(arena.text(", "))
                .append(arena.text(sanitize_identifier(b.as_ref())))
                .append(arena.text(")")),
            WhenPattern::Wildcard => arena.text("_"),
            WhenPattern::Var(name) => arena.text(sanitize_identifier(name.as_ref())),
            WhenPattern::Literal(expr) => self.to_doc(arena, expr, node_ids, church_notes),
        }
    }

    /// Convert PseudoData to a document.
    fn data_to_doc<'a>(&self, arena: &'a PrettyArena<'a>, data: &PseudoData) -> PrettyDoc<'a> {
        enum Task<'a> {
            Enter(&'a PseudoData),
            Exit(&'a PseudoData),
        }

        let mut tasks = vec![Task::Enter(data)];
        let mut out: Vec<PrettyDoc<'a>> = Vec::new();

        while let Some(task) = tasks.pop() {
            match task {
                Task::Enter(node) => {
                    tasks.push(Task::Exit(node));
                    match node {
                        PseudoData::List(items) => {
                            for item in items.iter().rev() {
                                tasks.push(Task::Enter(item));
                            }
                        }
                        PseudoData::Map(pairs) => {
                            for (k, v) in pairs.iter().rev() {
                                tasks.push(Task::Enter(v));
                                tasks.push(Task::Enter(k));
                            }
                        }
                        PseudoData::Constr(_, fields) => {
                            for field in fields.iter().rev() {
                                tasks.push(Task::Enter(field));
                            }
                        }
                        PseudoData::Integer(_) | PseudoData::ByteString(_) => {}
                    }
                }
                Task::Exit(node) => {
                    let doc = match node {
                        PseudoData::Integer(n) => arena.text(n.to_string()),
                        PseudoData::ByteString(bytes) => arena.text(format_byte_array(bytes)),
                        PseudoData::List(items) => {
                            let mut docs = Vec::with_capacity(items.len());
                            for _ in 0..items.len() {
                                docs.push(pop_doc(&mut out));
                            }
                            docs.reverse();
                            arena
                                .text("[")
                                .append(arena.intersperse(docs, arena.text(", ")))
                                .append(arena.text("]"))
                        }
                        PseudoData::Map(pairs) => {
                            let mut docs = Vec::with_capacity(pairs.len());
                            for _ in 0..pairs.len() {
                                let value_doc = pop_doc(&mut out);
                                let key_doc = pop_doc(&mut out);
                                docs.push(key_doc.append(arena.text(": ")).append(value_doc));
                            }
                            docs.reverse();
                            arena
                                .text("{")
                                .append(arena.intersperse(docs, arena.text(", ")))
                                .append(arena.text("}"))
                        }
                        PseudoData::Constr(tag, fields) => {
                            let mut field_docs = Vec::with_capacity(fields.len());
                            for _ in 0..fields.len() {
                                field_docs.push(pop_doc(&mut out));
                            }
                            field_docs.reverse();
                            arena
                                .text(format!("Data.Constr({}, [", tag))
                                .append(arena.intersperse(field_docs, arena.text(", ")))
                                .append(arena.text("])"))
                        }
                    };
                    out.push(doc);
                }
            }
        }

        pop_doc(&mut out)
    }
}

impl Default for PrettyPrinter {
    fn default() -> Self {
        Self::new()
    }
}

impl PseudoExpr {
    /// Pretty print to a string with default settings.
    pub(crate) fn to_pretty(&self) -> String {
        PrettyPrinter::new().print(self)
    }

    /// Pretty print to a string and return stable pseudo-node spans.
    pub(crate) fn to_pretty_with_spans(&self) -> (String, Vec<(PseudoNodeId, SourceSpan)>) {
        PrettyPrinter::new().print_with_spans(self)
    }

    /// Pretty print with custom config and return stable pseudo-node spans.
    pub(crate) fn to_pretty_with_spans_and_config(
        &self,
        config: PrettyConfig,
    ) -> (String, Vec<(PseudoNodeId, SourceSpan)>) {
        PrettyPrinter::with_config(config).print_with_spans(self)
    }

    /// Pretty print with custom config.
    pub(crate) fn to_pretty_with_config(&self, config: PrettyConfig) -> String {
        PrettyPrinter::with_config(config).print(self)
    }

    /// Pretty print with custom config and a populated
    /// [`BlueprintHintRegistry`] for resolving user-ADT constructor
    /// names without consulting the inline `display_name` field.
    pub(crate) fn to_pretty_with_spans_config_and_registry(
        &self,
        config: PrettyConfig,
        registry: Rc<BlueprintHintRegistry>,
    ) -> (String, Vec<(PseudoNodeId, SourceSpan)>) {
        PrettyPrinter::with_config(config)
            .with_registry(registry)
            .print_with_spans(self)
    }

    /// Pretty print with the pipeline-produced [`FinalTypeTable`]
    /// as the source for `show_types` annotations.
    pub(crate) fn to_pretty_with_spans_config_registry_and_final_types(
        &self,
        config: PrettyConfig,
        registry: Rc<BlueprintHintRegistry>,
        final_types: Rc<FinalTypeTable>,
    ) -> (String, Vec<(PseudoNodeId, SourceSpan)>) {
        PrettyPrinter::with_config(config)
            .with_registry(registry)
            .with_final_types(final_types)
            .print_with_spans(self)
    }
}

#[cfg(test)]
mod tests;
