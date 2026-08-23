//! Surface applied compile-time params as a `const param_N = ...`
//! prefix above the validator wrap. Read-only: the body stays
//! β-reduced; this only re-attaches which inlined constants were
//! knobs.
//!
//! Input is `OuterStructure.applied_params` from `inspect_outer`.
//! `None` when there are no applied params or all are `NonConstant`.
//! Re-binding the body lambdas to named params (keeping the outer
//! Apply chain) is deferred.

use uplc::ast::Constant;

use crate::pseudo::ast::PseudoData;

use super::{AppliedKind, AppliedParam, OuterStructure};

/// Resolve the user-supplied `AppliedKind` against the actual
/// `applied_count` + the expected runtime arity into a concrete
/// `runtime_count`: the LAST N outer Apply nodes are runtime args,
/// the first `applied_count - N` are compile-time params.
///
/// `Auto` (default) classifies all applied as runtime when
/// `applied + lambda == runtime_arity` exactly, otherwise behaves
/// like `Compile`. `Compile` is the explicit no-auto override.
pub(crate) fn resolve_runtime_count(
    kind: AppliedKind,
    outer: &OuterStructure,
    runtime_arity: usize,
) -> usize {
    let applied = outer.applied_params.len();
    match kind {
        AppliedKind::Auto => {
            // Auto-classify ONLY on exact match
            // `applied + lambda == runtime_arity`: the entire outer
            // Apply chain is treated as pre-applied runtime args.
            // Any other ratio (under-apply, strict over-apply,
            // mismatch with the version/purpose runtime arity)
            // falls back to compile-time; override with `--applied-as`.
            //
            // `>=` is rejected here: it would mask
            // genuine over-apply / parameterized validators where
            // the user really does have compile-time apply on top
            // of pre-applied runtime args.
            if applied > 0 && applied + outer.lambda_chain_length == runtime_arity {
                applied
            } else {
                0
            }
        }
        AppliedKind::Compile => 0,
        AppliedKind::Runtime => runtime_arity.min(applied),
        AppliedKind::RuntimeCount(n) => n.min(applied),
    }
}

/// The `param_N` number a compile slot is labeled with, skipping the
/// compiled-in bindings that share the outer Apply spine. `None` for a
/// binding: it is not a parameter and never takes a number.
///
/// Every surface that names a param — the prefix block, the hoisted
/// `const` annotations — goes through this, so a script whose spine
/// carries a compiler binding gets ONE consistent numbering.
pub(crate) fn param_label_index(bindings: &[usize], index: usize) -> Option<usize> {
    if bindings.contains(&index) {
        return None;
    }
    Some(index - bindings.iter().filter(|b| **b < index).count())
}

/// Test-only: production formats through the `_with_skip` variant.
/// Format the applied params (when any are present) as a leading
/// comment block. Returns `None` when there are no applied params.
///
/// The output splits into up to two sections — compile-time params
/// first, runtime args second — based on the resolved
/// `runtime_count`.
///
/// `runtime_arity` is the calling-convention arity from
/// `runtime_arity_for(version, purpose)`. Used to compute the
/// split when `kind = Runtime`.
#[cfg(test)]
pub(crate) fn format_applied_params_prefix(
    outer: &OuterStructure,
    kind: AppliedKind,
    runtime_arity: usize,
) -> Option<String> {
    format_applied_params_prefix_with_skip(outer, kind, runtime_arity, &Default::default())
}

/// Same as [`format_applied_params_prefix`] but `skip_indices` is
/// a set of applied-param indices to omit from the output. Used
/// after `hoist_compile_param_lets` — hoisted params already have
/// a `// ↓ applied compile-time param_K` annotation on their const
/// decl, so listing them in the prefix would be redundant.
pub(crate) fn format_applied_params_prefix_with_skip(
    outer: &OuterStructure,
    kind: AppliedKind,
    runtime_arity: usize,
    skip_indices: &std::collections::HashSet<usize>,
) -> Option<String> {
    if outer.applied_params.is_empty() {
        return None;
    }
    let applied = outer.applied_params.len();
    let runtime_count = resolve_runtime_count(kind, outer, runtime_arity);
    let compile_count = applied - runtime_count;

    // Surface ALL compile-labeled applied slots, even when every
    // one is `NonConstant`. A previous suppression "no Constant ⇒
    // skip section" silently dropped pre-applied non-literal compile
    // params (think: a script pre-applied with another script's
    // reference) — leaving the reader without ANY signal that the
    // script had compile-time parameterisation.
    //
    // Compile slots that are not params at all: PlutusTx's hoisted
    // builtin let-chain shares the outer Apply spine with them. They
    // stay visible as a trailing note, but never as `param_N`.
    let binding_list: Vec<usize> = outer
        .compiler_binding_indices
        .iter()
        .copied()
        .filter(|i| *i < compile_count)
        .collect();
    let binding_summaries: Vec<String> = outer
        .compiler_binding_indices
        .iter()
        .filter(|i| **i < compile_count)
        .map(|i| match &outer.applied_params[*i] {
            AppliedParam::NonConstant { summary } if !summary.is_empty() => summary.clone(),
            _ => "<term>".to_string(),
        })
        .collect();

    // If `skip_indices` covers ALL the remaining compile slots, we can
    // omit the compile section entirely.
    let compile_emit_count = (0..compile_count)
        .filter(|i| !skip_indices.contains(i) && !binding_list.contains(i))
        .count();
    let emit_compile = compile_emit_count > 0;
    let emit_runtime = runtime_count > 0;
    if !emit_compile && !emit_runtime {
        if binding_summaries.len() == compile_count && compile_count > 0 {
            // Every compile slot is a compiled-in binding: report the
            // chain rather than silently dropping it, so "no params"
            // stays a stated fact instead of an absence.
            return Some(format!(
                "// Outer Apply chain — no compile-time params: all {} argument(s) are\n// compiled in, and an applied parameter is always `con data`: {}.\n\n",
                compile_count,
                binding_summaries.join(", ")
            ));
        }
        return None;
    }

    // Visual order matches the Apply-stack metaphor — runtime args
    // are applied LAST (outermost in the tree, "on top of" the
    // script), so they appear FIRST in the output. Compile params
    // are applied first (innermost), so they appear below.
    let mut out = String::new();
    if emit_runtime {
        out.push_str(
            "// Pre-applied runtime args (datum / redeemer / script_context) — applied last (outermost):\n",
        );
        for (rel, p) in outer.applied_params[compile_count..].iter().enumerate() {
            push_param_line(&mut out, rel, p, /* runtime = */ true);
        }
    }
    if emit_compile {
        if emit_runtime {
            // Blank-line separator between the two sections.
            out.push('\n');
        }
        out.push_str(
            "// Applied compile-time params (from outer Apply chain) — applied first (innermost):\n",
        );
        // `param_N` numbers the PARAMS, not the spine slots: a
        // compiled-in binding that happens to sit on the same Apply
        // chain would otherwise take a number and push every real param
        // one along.
        for (i, p) in outer.applied_params[..compile_count].iter().enumerate() {
            if skip_indices.contains(&i) {
                continue;
            }
            let Some(label) = param_label_index(&binding_list, i) else {
                continue;
            };
            push_param_line(&mut out, label, p, /* runtime = */ false);
        }
    }
    if emit_compile {
        // The body is beta-reduced, so a param has no binder to look up
        // — it reads as an inlined literal wherever it was used. Say so:
        // a list of params that appear nowhere as variables is exactly
        // what makes readers doubt the decompilation.
        out.push_str("// Substituted into the body below: a param reads as an inlined\n");
        out.push_str("// literal, not as a named variable.\n");
    }
    if !binding_summaries.is_empty() {
        out.push_str(&format!(
            "// The outer Apply chain also carries {} compiled-in argument(s), not\n",
            binding_summaries.len()
        ));
        out.push_str(&format!(
            "// parameters — an applied parameter is always `con data`: {}.\n",
            binding_summaries.join(", ")
        ));
    }
    out.push('\n');
    Some(out)
}

/// Collect distinguishing hex bytestrings from a `Constant` so we
/// can match against the RHS of hoisted module-level
/// `const X = ...` declarations. Bytestrings ≥ 4 bytes (8 hex
/// chars) are kept — shorter ones collide too often.
pub(crate) fn collect_distinguishing_hex(c: &Constant) -> Vec<String> {
    let mut out = Vec::new();
    match c {
        Constant::ByteString(b) => {
            if b.len() >= 4 {
                out.push(hex::encode(b));
            }
        }
        Constant::Data(d) => collect_hex_from_plutus_data(d, &mut out),
        _ => {}
    }
    out
}

fn collect_hex_from_plutus_data(d: &uplc::PlutusData, out: &mut Vec<String>) {
    use uplc::PlutusData;
    match d {
        PlutusData::BoundedBytes(b) => {
            let bytes: &[u8] = b.as_ref();
            if bytes.len() >= 4 {
                out.push(hex::encode(bytes));
            }
        }
        PlutusData::Constr(c) => {
            for f in c.fields.iter() {
                collect_hex_from_plutus_data(f, out);
            }
        }
        PlutusData::Map(pairs) => {
            for (k, v) in pairs.iter() {
                collect_hex_from_plutus_data(k, out);
                collect_hex_from_plutus_data(v, out);
            }
        }
        PlutusData::Array(items) => {
            for i in items.iter() {
                collect_hex_from_plutus_data(i, out);
            }
        }
        PlutusData::BigInt(_) => {}
    }
}

/// Annotate hoisted module-level `const X = ...` decls with
/// `// ↓ <label>` comments when the const's RHS
/// contains hex bytestrings that match applied params from
/// `outer.applied_params`.
///
/// `compile_count` controls how each applied param is labeled —
/// indices `[0, compile_count)` use `param_K` (compile-time
/// param), indices `[compile_count, applied)` use `runtime_arg_K`
/// (rebased from 0 within the runtime range). This mirrors the
/// labeling used in `format_applied_params_prefix`.
///
/// Returns the set of matched applied-param indices so callers
/// can drop them from the prefix block (the const decl's `// ↓
/// extracted from ...` annotation already documents the param).
pub(crate) fn annotate_hoisted_consts_with_param_origin(
    rendered: &str,
    applied: &[AppliedParam],
    compile_count: usize,
    bindings: &[usize],
) -> (String, std::collections::HashSet<usize>) {
    // Build (index, label, hex-set) tuples for EVERY applied param
    // with a distinguishing bytestring — both compile and runtime
    // ranges contribute, each labeled per its classification.
    let param_entries: Vec<(usize, String, Vec<String>)> = applied
        .iter()
        .enumerate()
        .filter_map(|(i, p)| match p {
            AppliedParam::Constant(c) => {
                let h = collect_distinguishing_hex(c);
                if h.is_empty() {
                    None
                } else {
                    let label = if i < compile_count {
                        format!("param_{}", param_label_index(bindings, i)?)
                    } else {
                        let rel = i - compile_count;
                        format!("runtime_arg_{rel}")
                    };
                    Some((i, label, h))
                }
            }
            AppliedParam::NonConstant { .. } => None,
        })
        .collect();
    let mut matched_indices: std::collections::HashSet<usize> = std::collections::HashSet::new();
    if param_entries.is_empty() {
        return (rendered.to_string(), matched_indices);
    }

    let lines: Vec<&str> = rendered.lines().collect();
    let mut out: Vec<String> = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        if line.starts_with("const ") {
            // Determine the end of this const block (continuation
            // lines until next top-level keyword or EOF).
            let mut j = i + 1;
            while j < lines.len() {
                let next = lines[j];
                if next.starts_with("const ")
                    || next.starts_with("fn ")
                    || next.starts_with("rec fn ")
                    || next.starts_with("pub ")
                    || next.starts_with("validator ")
                {
                    break;
                }
                j += 1;
            }
            // Materialize block text for substring search.
            let block_text = lines[i..j].join("\n");
            let matched: Vec<&str> = param_entries
                .iter()
                .filter(|(_, _, hexes)| hexes.iter().any(|h| block_text.contains(h.as_str())))
                .map(|(idx, label, _)| {
                    matched_indices.insert(*idx);
                    label.as_str()
                })
                .collect();
            if !matched.is_empty() {
                out.push(format!("// ↓ extracted from {}", matched.join(" / ")));
            }
            for line in &lines[i..j] {
                out.push((*line).to_string());
            }
            i = j;
        } else {
            out.push(line.to_string());
            i += 1;
        }
    }
    let mut result = out.join("\n");
    if rendered.ends_with('\n') {
        result.push('\n');
    }
    (result, matched_indices)
}

/// Hoist `let NAME: T =
/// <RHS>` lines inside the validator block whose RHS contains a
/// known compile-time param hex bytestring, up to module-level
/// `const NAME: T = RHS` declarations above the validator. Each
/// hoisted const is annotated with the matched `param_K` for
/// traceability. Duplicate occurrences across arms are removed.
///
/// Returns `(rendered_with_hoists, hoisted_param_indices)`. The
/// caller uses the indices to drop those entries from the
/// "Applied compile-time params" prefix block — the const decl
/// is now self-documenting.
pub(crate) fn hoist_compile_param_lets(
    rendered: &str,
    applied: &[AppliedParam],
    compile_count: usize,
    bindings: &[usize],
) -> (String, std::collections::HashSet<usize>) {
    // Collect (compile-param-index, hex-set) pairs.
    let param_hexes: Vec<(usize, Vec<String>)> = applied
        .iter()
        .enumerate()
        .take(compile_count)
        .filter_map(|(i, p)| match p {
            AppliedParam::Constant(c) => {
                let h = collect_distinguishing_hex(c);
                if h.is_empty() { None } else { Some((i, h)) }
            }
            AppliedParam::NonConstant { .. } => None,
        })
        .collect();
    if param_hexes.is_empty() {
        return (rendered.to_string(), std::collections::HashSet::new());
    }

    let lines: Vec<&str> = rendered.lines().collect();
    // `hoisted_decls[i]` is `(annotation_comment, const_decl_line)`.
    let mut hoisted_decls: Vec<(String, String)> = Vec::new();
    let mut hoisted_names: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut hoisted_indices: std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut new_lines: Vec<String> = Vec::with_capacity(lines.len());
    let mut inside_validator = false;
    for line in &lines {
        if line.starts_with("validator ") || line.starts_with("pub fn ") {
            inside_validator = true;
            new_lines.push(line.to_string());
            continue;
        }
        if inside_validator && let Some((indent, name, type_part, rhs)) = parse_let_line(line) {
            // Find which compile-param's hex matches.
            let matched: Option<usize> = param_hexes
                .iter()
                .find(|(_, hexes)| hexes.iter().any(|h| rhs.contains(h.as_str())))
                .map(|(idx, _)| *idx);
            if let Some(idx) = matched {
                if hoisted_names.insert(name.to_string()) {
                    let type_str = if type_part.is_empty() {
                        String::new()
                    } else {
                        type_part.to_string()
                    };
                    let label = param_label_index(bindings, idx).unwrap_or(idx);
                    hoisted_decls.push((
                        format!("// ↑ applied compile-time param_{label}"),
                        format!("const {name}{type_str} = {rhs}"),
                    ));
                    hoisted_indices.insert(idx);
                } else {
                    // Same NAME was already hoisted — record
                    // its index too (this duplicate confirms
                    // the param is captured).
                    hoisted_indices.insert(idx);
                }
                // Drop the line — variable is now module-level.
                let _ = indent;
                continue;
            }
        }
        new_lines.push(line.to_string());
    }
    if hoisted_decls.is_empty() {
        return (rendered.to_string(), hoisted_indices);
    }
    // Insert hoisted decls just before the `validator ` / `pub fn `
    // line. Format: `<const decl>\n<annotation comment>\n` so the
    // comment lives directly UNDER the const (matching the
    // `↓ extracted from ...` convention reversed:
    // `↑` because here we annotate the line ABOVE).
    //
    // Actually for readability put the annotation ABOVE the const:
    // `// ↓ applied compile-time param_K\nconst NAME = ...`
    let mut out: Vec<String> = Vec::with_capacity(new_lines.len() + hoisted_decls.len() * 2 + 2);
    let mut inserted = false;
    for line in new_lines {
        if !inserted && (line.starts_with("validator ") || line.starts_with("pub fn ")) {
            for (comment, decl) in &hoisted_decls {
                let annotation = comment.replace("↑ applied", "↓ applied");
                out.push(annotation);
                out.push(decl.clone());
            }
            out.push(String::new()); // blank separator
            inserted = true;
        }
        out.push(line);
    }
    let mut result = out.join("\n");
    if rendered.ends_with('\n') {
        result.push('\n');
    }
    (result, hoisted_indices)
}

/// Parse a `<indent>let NAME(: TYPE)? = <RHS>` line. Returns
/// `(indent, name, type_part, rhs)` where `type_part` includes the
/// leading `: TYPE` or is empty if absent.
fn parse_let_line(line: &str) -> Option<(&str, &str, &str, &str)> {
    let indent_end = line.find(|c: char| c != ' ' && c != '\t')?;
    let (indent, body) = line.split_at(indent_end);
    let after_let = body.strip_prefix("let ")?;
    let eq_idx = after_let.find(" = ")?;
    let head = &after_let[..eq_idx];
    let rhs = &after_let[eq_idx + 3..];
    // Split head on `:` to separate NAME from TYPE.
    let (name, type_part) = if let Some(colon_idx) = head.find(':') {
        let name = head[..colon_idx].trim();
        let type_part = &head[colon_idx..];
        (name, type_part)
    } else {
        (head.trim(), "")
    };
    if name.is_empty() {
        return None;
    }
    // Reject names that contain non-ident chars (e.g. tuple destructuring).
    if !name.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return None;
    }
    Some((indent, name, type_part, rhs))
}

fn push_param_line(out: &mut String, index: usize, p: &AppliedParam, runtime: bool) {
    let ident_prefix = if runtime { "runtime_arg" } else { "param" };
    match p {
        AppliedParam::Constant(value) => match render_constant(value) {
            RenderForm::ConstDecl { ty, value } => {
                if runtime {
                    out.push_str(&format!("// {ident_prefix}_{index}: {ty} = {value}\n"));
                } else {
                    out.push_str(&format!(
                        "// const {ident_prefix}_{index}: {ty} = {value}\n"
                    ));
                }
            }
            RenderForm::Data {
                structural,
                cbor_hex,
            } => {
                // Decoded structural literal first (human-readable),
                // then the canonical CBOR for an exact round-trip.
                // Both are `//` comments and deliberately avoid the
                // `const X: Data = ...` decl shape the P6.3 audit
                // forbids (and the body's `Data.Constr(` artifact).
                out.push_str(&format!(
                    "// {ident_prefix}_{index} (Plutus Data, decoded): {structural}\n"
                ));
                out.push_str(&format!(
                    "// {ident_prefix}_{index} (Plutus Data, CBOR): {cbor_hex}\n"
                ));
            }
            RenderForm::Opaque { kind } => {
                out.push_str(&format!("// {ident_prefix}_{index}: <opaque {kind}>\n"));
            }
        },
        AppliedParam::NonConstant { summary } => {
            out.push_str(&format!(
                "// {ident_prefix}_{index}: <non-constant: {summary}>\n"
            ));
        }
    }
}

/// How a `Constant` should appear in the surface output.
#[derive(Debug, PartialEq)]
enum RenderForm {
    /// A clean source-compatible declaration.
    ConstDecl { ty: &'static str, value: String },
    /// A decoded Plutus `Data` compile-time param — e.g. a DEX/AMM
    /// pool config (asset classes, pool NFT, LP token, fee knobs)
    /// baked into a parameterized validator. `structural` is a
    /// single-line, non-surface literal — `Constr(tag, [..])`, `[..]`
    /// (list), `{k: v}` (map), integers, and bytestrings (`@"text"`
    /// for printable, `#"hex"` otherwise) — so the reader sees the
    /// FULL value instead of an opaque stub. `cbor_hex` is the
    /// canonical CBOR encoding of that value, so a consumer can
    /// round-trip the `Data` without re-deriving it. Canonical, not
    /// verbatim: it reproduces the applied bytes themselves only where
    /// those were already canonical. Both render as `//`
    /// comments, so this is informational, never compilable surface
    /// syntax (matching the param prefix's readability-first default).
    Data {
        structural: String,
        cbor_hex: String,
    },
    /// Shapes with no concise representation at all (BLS12-381
    /// elements) — emit as a tagged opaque comment.
    Opaque { kind: String },
}

impl RenderForm {
    /// The bare value text for embedding inside a larger literal
    /// (a `ProtoList` element or `ProtoPair` side). For a nested
    /// `Data` the structural literal is used; the top-level CBOR
    /// round-trip line is only emitted for the whole param.
    fn into_inline_value(self) -> String {
        match self {
            RenderForm::ConstDecl { value, .. } => value,
            RenderForm::Data { structural, .. } => structural,
            RenderForm::Opaque { kind } => format!("<{kind}>"),
        }
    }
}

/// Format a UPLC `Constant`. Plain primitives produce a
/// `RenderForm::ConstDecl` with source-compatible syntax.
/// Embedded `Data` and BLS12-381 elements have no concise
/// surface form and produce `RenderForm::Opaque`.
///
/// Every `RenderForm::ConstDecl` is emitted as a `//` comment
/// (not an actual `const` decl) so the
/// prefix is purely informational — it shouldn't introduce
/// declarations that conflict with body-inlined values or trip the
/// audit guards (e.g. P6.3's `: Data =` pattern).
fn render_constant(c: &Constant) -> RenderForm {
    match c {
        Constant::Integer(n) => RenderForm::ConstDecl {
            ty: "Int",
            value: n.to_string(),
        },
        Constant::ByteString(b) => RenderForm::ConstDecl {
            ty: "ByteArray",
            value: format!("#\"{}\"", hex::encode(b)),
        },
        Constant::String(s) => RenderForm::ConstDecl {
            ty: "String",
            value: format!("@\"{}\"", escape_surface_string(s)),
        },
        Constant::Bool(b) => RenderForm::ConstDecl {
            ty: "Bool",
            value: if *b {
                "True".to_string()
            } else {
                "False".to_string()
            },
        },
        Constant::Unit => RenderForm::ConstDecl {
            ty: "Void",
            value: "Void".to_string(),
        },
        Constant::ProtoList(_, items) => {
            let parts: Vec<String> = items
                .iter()
                .map(|i| render_constant(i).into_inline_value())
                .collect();
            RenderForm::ConstDecl {
                ty: "List<_>",
                value: format!("[{}]", parts.join(", ")),
            }
        }
        Constant::ProtoPair(_, _, a, b) => {
            let av = render_constant(a).into_inline_value();
            let bv = render_constant(b).into_inline_value();
            RenderForm::ConstDecl {
                ty: "Pair<_, _>",
                value: format!("Pair({av}, {bv})"),
            }
        }
        Constant::Data(d) => {
            // Decode the Plutus Data into a structural literal so the
            // reader sees the actual baked-in value (DEX pool config,
            // asset classes, NFT policy, fee knobs, ...) rather than
            // an opaque stub — the whole point of a Data compile
            // param is that it CARRIES the config. Also emit the
            // canonical CBOR encoding so a consumer can round-trip the
            // value without re-deriving it from the body. A param that
            // arrived non-canonically — map pairs out of key order,
            // tag 102 where a compact constructor tag exists — encodes
            // to different bytes for the same value.
            RenderForm::Data {
                structural: render_plutus_data_inline(d),
                cbor_hex: hex::encode(uplc::plutus_data_to_bytes(d)),
            }
        }
        _ => RenderForm::Opaque {
            kind: "BLS12-381 element".to_string(),
        },
    }
}

/// Render a decoded Plutus `Data` value as a single-line structural
/// literal: `Constr(tag, [..])` (constructor), `[..]` (list),
/// `{k: v}` (map), integers, and bytestrings (`@"text"` / `#"hex"`).
///
/// This is deliberately NON-surface pseudo (bare `Constr(..)`, not
/// the body renderer's `Data.Constr(..)` — keeping the param comment
/// free of any `Data` token and of `Data.Constr(` artifacts that the
/// MIR pipeline guards against). It favors showing the COMPLETE value
/// over source validity so the reader can recover what a
/// parameterized validator baked in. Logical constructor tags
/// (CBOR alt-tags 121→0, 1280→7, ...) are normalized by
/// [`convert_plutus_data`](crate::decompile::basic::convert_plutus_data).
///
/// The accompanying `(Plutus Data, CBOR)` line is the canonical,
/// lossless form; this structural view is a readability aid. The rare
/// general-form constructor (CBOR tag 102, which is how an index ≥128
/// is written) shows its LOGICAL index here like any other, because
/// [`constructor_index`](crate::decompile::basic::constructor_index)
/// reads that index out of the node's `any_constructor` field rather
/// than off the escape tag.
fn render_plutus_data_inline(d: &uplc::PlutusData) -> String {
    let mut out = String::new();
    push_pseudo_data_inline(&mut out, &crate::decompile::basic::convert_plutus_data(d));
    out
}

fn push_pseudo_data_inline(out: &mut String, d: &PseudoData) {
    match d {
        PseudoData::Integer(n) => out.push_str(&n.to_string()),
        PseudoData::ByteString(b) => out.push_str(&format_data_bytes(b)),
        PseudoData::List(items) => {
            out.push('[');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                push_pseudo_data_inline(out, item);
            }
            out.push(']');
        }
        PseudoData::Map(pairs) => {
            out.push('{');
            for (i, (k, v)) in pairs.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                push_pseudo_data_inline(out, k);
                out.push_str(": ");
                push_pseudo_data_inline(out, v);
            }
            out.push('}');
        }
        PseudoData::Constr(tag, fields) => {
            out.push_str(&format!("Constr({tag}, ["));
            for (i, f) in fields.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                push_pseudo_data_inline(out, f);
            }
            out.push_str("])");
        }
    }
}

/// Format a Plutus `Data` bytestring leaf the same way the body Data
/// renderer does: `@"text"` when every byte is printable ASCII (so an
/// asset name like `@"USDA"` reads naturally), otherwise `#"<hex>"`
/// (policy IDs, hashes). The CBOR line carries the same leaf either
/// way, so this choice is presentation only.
fn format_data_bytes(bytes: &[u8]) -> String {
    if !bytes.is_empty()
        && bytes.iter().all(|&b| (0x20..=0x7E).contains(&b))
        && let Ok(s) = std::str::from_utf8(bytes)
    {
        format!("@\"{}\"", escape_surface_string(s))
    } else {
        format!("#\"{}\"", hex::encode(bytes))
    }
}

fn escape_surface_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests;
