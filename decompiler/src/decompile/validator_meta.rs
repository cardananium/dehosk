//! Validator-block metadata for emitting
//! `validator NAME { spend(...) {...} mint(...) {...} else(_) { fail } }`
//! syntax instead of the bare `fn decompiled(...)` form.
//!
//! Carried by [`crate::decompile::DecompileOptions::validator_meta`] when
//! blueprint information is available (`dehosk blueprint <plutus.json>`);
//! `None` falls back to `fn decompiled(args) { body }` /
//! `validator decompiled { else(_) { body } }`.

use serde::{Deserialize, Serialize};

/// Validator-block metadata: name + entry-point purposes.
///
/// Validators sharing one compiled image (`multi.redeem.spend` and
/// `multi.redeem.mint`) collapse into one `ValidatorMeta` with
/// several `entries`. The renderer repeats the body under each
/// entry; `prune_purpose_dispatch` keeps only that purpose's arm.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValidatorMeta {
    /// Validator block name — an legal identifier (no `.`, no
    /// keyword collision). From a blueprint title, the segment before
    /// the purpose suffix: `<package>.<module>.<title>.<purpose>` →
    /// `<title>`.
    pub name: String,

    /// Entry points, in render order. The renderer emits one
    /// `<purpose>(params) { body }` arm per entry, plus a trailing
    /// `else(_) { fail }` when no `Else` entry is present and at least
    /// one other entry is.
    pub entries: Vec<ValidatorEntry>,
}

/// One entry point inside a [`ValidatorMeta`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValidatorEntry {
    pub purpose: ValidatorPurpose,
    /// Parameter names from the blueprint redeemer/datum schema, in
    /// declaration order. Empty `params` for `Else` (renders `_`).
    pub params: Vec<String>,
}

/// Cardano validator purposes per CIP-0035 / V3 schema.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ValidatorPurpose {
    Spend,
    Mint,
    Withdraw,
    /// `certificate(...)` — `ScriptInfo::Certifying`. Blueprint titles
    /// still use the `.publish` suffix; both spellings parse.
    Certificate,
    Vote,
    /// `propose(action) { ... }` — V3-only governance purpose
    /// (`ScriptInfo::Proposing`, Constr tag 5). V1/V2 have none.
    Propose,
    /// `else(_) { fail }` — the universal fallback purpose. Declared as
    /// a real entry (a blueprint `.else` title on the same hash) it
    /// renders `else(_) { body }`; with no `else` entry the renderer
    /// synthesises a trailing `else(_) { fail }`.
    Else,
}

impl ValidatorPurpose {
    /// Every purpose, once — the one list, so the renderer that prints a
    /// handler keyword and the readers that recognise one cannot go stale
    /// against each other (the debugger reads the keywords through it).
    /// `all_is_exhaustive` names every variant in a `match` with no `_` arm,
    /// so adding one without adding it here fails the build.
    pub(crate) const ALL: [ValidatorPurpose; 7] = [
        Self::Spend,
        Self::Mint,
        Self::Withdraw,
        Self::Certificate,
        Self::Vote,
        Self::Propose,
        Self::Else,
    ];

    /// surface-surface keyword for this purpose, contextual only at the
    /// handler-DECLARATION position — as ordinary binders/field names these
    /// words are legal identifiers, so `sanitize_identifier`
    /// (pseudo/pretty/mod.rs) deliberately does NOT escape them.
    pub(crate) const fn keyword(self) -> &'static str {
        match self {
            Self::Spend => "spend",
            Self::Mint => "mint",
            Self::Withdraw => "withdraw",
            Self::Certificate => "certificate",
            Self::Vote => "vote",
            Self::Propose => "propose",
            Self::Else => "else",
        }
    }

    /// Parse from a blueprint title's trailing segment (e.g.
    /// "hello_world.hello_world.spend" → `Some(Spend)`).
    pub(crate) fn from_title_suffix(suffix: &str) -> Option<Self> {
        match suffix {
            "spend" => Some(Self::Spend),
            "mint" => Some(Self::Mint),
            "withdraw" => Some(Self::Withdraw),
            "certificate" | "publish" => Some(Self::Certificate),
            "vote" => Some(Self::Vote),
            "propose" => Some(Self::Propose),
            "else" => Some(Self::Else),
            _ => None,
        }
    }
}

impl ValidatorMeta {
    /// Fallback stub for the no-blueprint case: a single-entry
    /// `else(_) { body }` block named `decompiled`, keeping the
    /// legal surface shape when the real purpose is unknown.
    pub(crate) fn fallback() -> Self {
        // Empty `params` lets `render_validator_block` pick
        // `entry_args` (when the original lambda bound something like
        // `script_context`) or a literal `_`.
        Self {
            name: "decompiled".to_string(),
            entries: vec![ValidatorEntry {
                purpose: ValidatorPurpose::Else,
                params: Vec::new(),
            }],
        }
    }

    /// True iff this meta contains an `else` entry.
    pub(crate) fn has_else(&self) -> bool {
        self.entries
            .iter()
            .any(|e| matches!(e.purpose, ValidatorPurpose::Else))
    }

    /// Build a [`ValidatorMeta`] from one hash group of blueprint
    /// validators (from `Blueprint::validators_by_hash`). The name is
    /// the second-to-last `.` segment of the first title
    /// (`multi.redeem.spend` → `redeem`); each purpose is parsed from
    /// the trailing segment, skipping titles whose suffix names no
    /// known purpose. `None` when the group is empty or yields none.
    pub fn from_blueprint_group<I, S>(titles_and_params: I) -> Option<Self>
    where
        I: IntoIterator<Item = (S, Vec<String>)>,
        S: AsRef<str>,
    {
        let collected: Vec<(String, Vec<String>)> = titles_and_params
            .into_iter()
            .map(|(t, p)| (t.as_ref().to_string(), p))
            .collect();
        if collected.is_empty() {
            return None;
        }
        let name = derive_validator_name(&collected.first()?.0)?;
        let entries: Vec<ValidatorEntry> = collected
            .iter()
            .filter_map(|(title, params)| {
                let suffix = title.rsplit('.').next()?;
                let purpose = ValidatorPurpose::from_title_suffix(suffix)?;
                // An `Else` entry's blueprint params are placeholders
                // (`_redeemer`, `p0`, …): the else arm binds no typed
                // datum/redeemer. Drop them so `render_validator_block` emits
                // `else(_)` or `else(<entry_args>)`.
                let params = if purpose == ValidatorPurpose::Else {
                    Vec::new()
                } else {
                    params.clone()
                };
                Some(ValidatorEntry { purpose, params })
            })
            .collect();
        if entries.is_empty() {
            return None;
        }
        Some(Self { name, entries })
    }
}

/// Render the entry-lambda body (no `fn decompiled` wrap) as
/// `validator NAME { <purpose>(params) { body } … }`.
/// `entry_args` fills entries whose blueprint `params` are empty.
pub(crate) fn render_validator_block(
    meta: &ValidatorMeta,
    rendered_body: &str,
    entry_args: &str,
    indent: usize,
) -> String {
    render_validator_block_with_bodies(meta, rendered_body, entry_args, indent, None)
}

/// `render_validator_block` with optional PRE-RENDERED per-purpose bodies
/// (built from per-purpose ASTs with handler-local dead-code elimination).
/// An entry with a supplied body uses it verbatim; the rest fall back to
/// the text-level `prune_purpose_dispatch` or the full shared body.
pub(crate) fn render_validator_block_with_bodies(
    meta: &ValidatorMeta,
    rendered_body: &str,
    entry_args: &str,
    indent: usize,
    purpose_bodies: Option<&[(ValidatorPurpose, String)]>,
) -> String {
    let one = " ".repeat(indent);
    let two = " ".repeat(indent * 2);
    let mut out = String::new();
    out.push_str("validator ");
    out.push_str(&meta.name);
    out.push_str(" {\n");

    // Prune the shared body to a per-purpose arm only when more
    // than one non-`Else` entry renders it; a single-entry
    // validator keeps the body unchanged.
    let multi_entry = meta
        .entries
        .iter()
        .filter(|e| e.purpose != ValidatorPurpose::Else)
        .count()
        > 1;

    for entry in &meta.entries {
        // Param binding: explicit entry params win; otherwise `entry_args`
        // (the original `fn decompiled(...)` parameter list) so the body's
        // references stay bound. Collapse to a literal `_` only for an
        // `Else` entry whose args were empty or a single underscore.
        let params = if !entry.params.is_empty() {
            entry.params.join(", ")
        } else if entry.purpose == ValidatorPurpose::Else
            && (entry_args.is_empty() || entry_args == "_")
        {
            "_".to_string()
        } else {
            entry_args.to_string()
        };
        out.push_str(&one);
        out.push_str(entry.purpose.keyword());
        out.push('(');
        out.push_str(&params);
        out.push_str(") {\n");

        // Per-entry body priority: a pre-rendered per-purpose AST body
        // (dispatch arm selected, handler-local DCE applied), then the
        // text-level dispatch prune, then the full shared body.
        let ast_body: Option<&str> = purpose_bodies.and_then(|bodies| {
            bodies
                .iter()
                .find(|(p, _)| *p == entry.purpose)
                .map(|(_, b)| b.as_str())
        });
        let pruned = if ast_body.is_none() && multi_entry {
            prune_purpose_dispatch(rendered_body, entry.purpose)
        } else {
            None
        };
        let body_for_entry: &str = ast_body.or(pruned.as_deref()).unwrap_or(rendered_body);

        for line in body_for_entry.lines() {
            if line.is_empty() {
                out.push('\n');
            } else {
                out.push_str(&two);
                out.push_str(line);
                out.push('\n');
            }
        }
        out.push_str(&one);
        out.push_str("}\n");
    }

    // Trailing `else(_) { fail }` fallback if no `Else` entry exists
    // *and* the validator has at least one non-Else entry.
    if !meta.has_else()
        && meta
            .entries
            .iter()
            .any(|e| !matches!(e.purpose, ValidatorPurpose::Else))
    {
        out.push_str(&one);
        out.push_str("else(_) {\n");
        out.push_str(&two);
        out.push_str("fail\n");
        out.push_str(&one);
        out.push_str("}\n");
    }

    out.push('}');
    out
}

/// If the validator body's outermost expression (after leading
/// let/expect) is a script-purpose `when`, return that purpose's arm
/// or `fail`. Detection is by arm constructor names, not the
/// subject — `script_context.purpose` / `script_info` / a renamed
/// binder all work; `Spending`/`Minting`/… are unambiguous.
///
/// Every non-wildcard arm must be one of `{Spending, Minting,
/// Rewarding, Certifying, Voting, Proposing}`, and at least two must
/// be present — otherwise this is an ordinary constructor match.
/// Nothing but whitespace may follow the matched `}` (bar an expect
/// message and trailing `Void`). `Else` returns `None`. Unrecognised
/// shape → `None` and the renderer emits the full body.
fn prune_purpose_dispatch(body: &str, purpose: ValidatorPurpose) -> Option<String> {
    // Else has no specific arm — leave unchanged.
    let purpose_constructor = match purpose {
        ValidatorPurpose::Spend => "Spending",
        ValidatorPurpose::Mint => "Minting",
        ValidatorPurpose::Withdraw => "Rewarding",
        ValidatorPurpose::Certificate => "Certifying",
        ValidatorPurpose::Vote => "Voting",
        ValidatorPurpose::Propose => "Proposing",
        ValidatorPurpose::Else => return None,
    };
    const PURPOSE_NAMES: &[&str] = &[
        "Spending",
        "Minting",
        "Rewarding",
        "Certifying",
        "Voting",
        "Proposing",
    ];

    // The simplifier commonly emits the dispatch behind a let-chain:
    //
    // ```
    // let purpose = script_context.purpose
    // [expect[!]] when purpose is { Spending -> ...; Minting -> ...; }
    // ```
    //
    // Split the leading bracket-balanced statements off so they
    // survive on every per-purpose arm, then prune the trailing When.
    let (leading_prefix, when_part) = split_leading_statements_before_when(body)?;

    let trimmed = when_part.trim_start();
    // Accept `when ` bare or behind `expect ` / `expect! ` (the
    // simplifier emits both). The prefix is dropped: the pruned body
    // is the matched arm itself, not a When needing an `expect`.
    let (when_kw_offset, had_expect_prefix) = if let Some(rest) = trimmed.strip_prefix("expect! ") {
        if rest.starts_with("when ") {
            (8_usize, true)
        } else {
            return None;
        }
    } else if let Some(rest) = trimmed.strip_prefix("expect ") {
        if rest.starts_with("when ") {
            (7_usize, true)
        } else {
            return None;
        }
    } else if trimmed.starts_with("when ") {
        (0_usize, false)
    } else {
        return None;
    };
    let when_view = &trimmed[when_kw_offset..];

    // The When block's opening `{` must sit on the header line.
    let mut open_brace_idx: Option<usize> = None;
    for (i, c) in when_view.char_indices() {
        if c == '{' {
            open_brace_idx = Some(i);
            break;
        }
        if c == '\n' {
            return None;
        }
    }
    let open_brace = open_brace_idx?;
    // Sanity: the header before the brace must contain ` is `.
    if !when_view[..open_brace].contains(" is ") {
        return None;
    }
    // The dispatch subject (e.g. `script_context.script_info`) is the
    // header text between the leading `when ` and the last ` is `; it
    // restores the per-purpose arm binders that pruning would drop.
    // Malformed headers fail closed to `None` — no restoration.
    let dispatch_subject: Option<String> = when_view[..open_brace]
        .strip_prefix("when ")
        .and_then(|h| h.rfind(" is ").map(|idx| h[..idx].trim().to_string()))
        .filter(|s| !s.is_empty());
    // Bracket-balance to find the matching closing brace.
    let close_brace = match_close_brace(&when_view[open_brace..])?;
    let arms_text = &when_view[open_brace + 1..open_brace + close_brace];

    // Anything after the matched `}` must be whitespace, or the body
    // has trailing statements that pruning would discard. The one
    // tolerated exception is the `, @"msg"` suffix the simplifier
    // appends to an `expect when`, and only for that form: a bare
    // `when` is an expression and carries no error message.
    let mut after = when_view[open_brace + close_brace + 1..].trim();
    // The renderer prints an expect-chain's final `Void` on its own line
    // after the dispatch instead of eliding it; that `Void` is the chain's
    // implicit result, so drop a standalone trailing one.
    if had_expect_prefix {
        if after == "Void" {
            after = "";
        } else if let Some(rest) = after.strip_suffix("\nVoid") {
            after = rest.trim_end();
        }
    }
    if !after.is_empty() && !(had_expect_prefix && is_expect_message_suffix(after)) {
        return None;
    }

    let arms = parse_when_arms(arms_text)?;
    // Filter out wildcard arms; require ≥2 purpose-constructor arms.
    let purpose_arms: Vec<&Arm> = arms
        .iter()
        .filter(|a| PURPOSE_NAMES.contains(&a.constructor.as_str()))
        .collect();
    if purpose_arms.len() < 2 {
        return None;
    }
    // ALL non-wildcard arms must be purpose constructors.
    for arm in &arms {
        if arm.constructor != "_" && !PURPOSE_NAMES.contains(&arm.constructor.as_str()) {
            return None;
        }
    }

    // Find matching arm. Wildcard `_` matches if no specific purpose-arm
    // matched. If no match found, emit `fail` (this purpose is dead).
    let arm_body = if let Some(arm) = arms.iter().find(|a| a.constructor == purpose_constructor) {
        let body = dedent_arm_body(&arm.body);
        // Restore the binders pruning dropped: a split handler runs only for
        // its own purpose, so an `expect` destructure of the dispatch subject
        // rebinds datum/policy_id/… as the original arm did, matching the
        // single-purpose path's `expect Spending(...) = <subject>`. Gated on
        // a named binder, so all-wildcard arms (V1/V2 style) emit nothing.
        match (&dispatch_subject, binders_to_restore(&arm.binders)) {
            (Some(subject), Some(binders)) => {
                format!("expect {purpose_constructor}({binders}) = {subject}\n{body}")
            }
            _ => body,
        }
    } else if let Some(wildcard) = arms.iter().find(|a| a.constructor == "_") {
        dedent_arm_body(&wildcard.body)
    } else {
        "fail".to_string()
    };

    if leading_prefix.is_empty() {
        Some(arm_body)
    } else {
        // Re-attach the leading let-chain to the pruned arm body.
        let mut out = String::with_capacity(leading_prefix.len() + arm_body.len() + 1);
        out.push_str(leading_prefix);
        if !leading_prefix.ends_with('\n') {
            out.push('\n');
        }
        out.push_str(&arm_body);
        Some(out)
    }
}

/// Split a body into `(leading_prefix, rest_starting_at_the_When)`.
/// The prefix is the bracket-balanced top-level statements (let
/// bindings, `expect ...`) that precede the dispatch When.
///
/// With no dispatch When anywhere, returns `(body, "")`; the empty
/// rest fails the caller's `when ` check and it bails.
fn split_leading_statements_before_when(body: &str) -> Option<(&str, &str)> {
    let bytes = body.as_bytes();
    let mut depth_paren = 0_i32;
    let mut depth_brace = 0_i32;
    let mut depth_bracket = 0_i32;
    let mut i = 0_usize;
    while i < bytes.len() {
        let c = bytes[i];
        // Skip string literals so braces inside them are not counted.
        // BOTH spellings: `@"…"` is a `String` (trace text) and `"…"` is
        // a printable `ByteArray`, and an asset name really can contain
        // a brace — `let marker = "{"` used to desync this walk, which
        // then never saw the dispatch `when` at depth zero.
        if c == b'"' || (c == b'@' && bytes.get(i + 1) == Some(&b'"')) {
            i += if c == b'@' { 2 } else { 1 };
            while i < bytes.len() {
                let sc = bytes[i];
                i += 1;
                if sc == b'\\' && i < bytes.len() {
                    i += 1;
                } else if sc == b'"' {
                    break;
                }
            }
            continue;
        }
        match c {
            b'(' => depth_paren += 1,
            b')' => depth_paren -= 1,
            b'{' => depth_brace += 1,
            b'}' => depth_brace -= 1,
            b'[' => depth_bracket += 1,
            b']' => depth_bracket -= 1,
            b'\n'
                // At a top-level line boundary, check whether
                // the next line opens the dispatch When.
                if depth_paren == 0 && depth_brace == 0 && depth_bracket == 0 => {
                    let line_start = i + 1;
                    if line_starts_with_when_dispatch(&body[line_start..]) {
                        return Some((&body[..line_start], &body[line_start..]));
                    }
                }
            _ => {}
        }
        i += 1;
    }
    // No boundary matched: the body may itself start with a When
    // (no leading let-chain); otherwise let the caller bail.
    if line_starts_with_when_dispatch(body) {
        Some(("", body))
    } else {
        Some((body, ""))
    }
}

/// Recognise the trailing suffix `, @"<string>"` that the simplifier
/// appends to an `expect when` dispatch. The string may contain
/// escapes (`\"`, `\\`, `\n`, …) and must terminate before any
/// trailing non-whitespace.
fn is_expect_message_suffix(s: &str) -> bool {
    let s = s.trim_start();
    let Some(rest) = s.strip_prefix(',') else {
        return false;
    };
    let rest = rest.trim_start();
    let Some(rest) = rest.strip_prefix("@\"") else {
        return false;
    };
    // Walk the string literal until the closing quote, honouring
    // `\` escapes. Anything after the closing `"` must be whitespace.
    let bytes = rest.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if c == b'\\' && i + 1 < bytes.len() {
            i += 2;
            continue;
        }
        if c == b'"' {
            return rest[i + 1..].trim().is_empty();
        }
        i += 1;
    }
    false
}

fn line_starts_with_when_dispatch(text: &str) -> bool {
    let trimmed = text.trim_start_matches([' ', '\t']);
    if trimmed.starts_with("when ") {
        return true;
    }
    if let Some(rest) = trimmed.strip_prefix("expect ") {
        return rest.starts_with("when ");
    }
    if let Some(rest) = trimmed.strip_prefix("expect! ") {
        return rest.starts_with("when ");
    }
    false
}

/// One parsed `when` arm.
#[derive(Debug)]
struct Arm {
    /// Constructor name (e.g. "Spending", "Minting") or "_" for
    /// wildcard.
    constructor: String,
    /// Raw pattern binders between the constructor's parens
    /// (e.g. `"output_reference, datum"`); empty when the arm has no
    /// parens. Used to restore purpose-field bindings when a
    /// multi-purpose dispatch is pruned per-handler.
    binders: String,
    /// Arm body string (everything after `->`, possibly multi-line).
    body: String,
}

/// The binder list to restore via an `expect` destructure, or `None` when
/// there is nothing to bind (empty, or all `_`). A non-`_` binder is what
/// proves text-pruning would drop a real binding; an all-wildcard
/// dispatch restores nothing.
fn binders_to_restore(binders: &str) -> Option<String> {
    let trimmed = binders.trim();
    if trimmed.is_empty() {
        return None;
    }
    let has_named = trimmed
        .split(',')
        .map(str::trim)
        .any(|b| !b.is_empty() && b != "_");
    has_named.then(|| trimmed.to_string())
}

/// Parse the inside-the-braces text of a `when` block into arms:
/// `<constructor>(<binders>) -> <body>`, `<constructor> -> <body>`
/// or `_ -> <body>`. Multi-line bodies run greedily to the next arm
/// header at the same indent. `None` on parse failure.
fn parse_when_arms(text: &str) -> Option<Vec<Arm>> {
    let lines: Vec<&str> = text.lines().collect();
    let mut arms: Vec<Arm> = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].trim_start();
        if line.is_empty() {
            i += 1;
            continue;
        }
        // Arm header: a capitalised identifier or `_`, then an arrow.
        // The renderer emits it inline as ` -> <body>` or at end of line
        // with the body below (V3 multi-purpose dispatch); accept both.
        let (arrow_idx, arrow_len) = if let Some(i) = line.find(" -> ") {
            (i, 4)
        } else if line.ends_with(" ->") {
            (line.len() - 3, 3)
        } else {
            return None;
        };
        let header = &line[..arrow_idx];
        let body_first_line = if arrow_idx + arrow_len <= line.len() {
            &line[arrow_idx + arrow_len..]
        } else {
            ""
        };
        // Constructor name is the header up to `(`, binders the paren
        // content; the header is one line, so `rfind(')')` finds the
        // matching close.
        let (constructor, binders): (String, String) = if let Some(paren) = header.find('(') {
            let inner = match header.rfind(')') {
                Some(close) if close > paren => header[paren + 1..close].trim().to_string(),
                _ => String::new(),
            };
            (header[..paren].to_string(), inner)
        } else {
            (header.trim().to_string(), String::new())
        };
        if !is_valid_arm_constructor(&constructor) {
            return None;
        }

        // Collect body — current line's rest + any following lines until
        // the next arm header (same indent as this arm) or end.
        let arm_indent = lines[i].len() - lines[i].trim_start().len();
        let mut body_lines = Vec::new();
        if !body_first_line.is_empty() {
            body_lines.push(body_first_line.to_string());
        }
        i += 1;
        while i < lines.len() {
            let next = lines[i];
            // Empty line continues the current arm body.
            if next.trim().is_empty() {
                body_lines.push(String::new());
                i += 1;
                continue;
            }
            let next_indent = next.len() - next.trim_start().len();
            if next_indent <= arm_indent {
                // Could be a new arm header — arrow inline or at
                // end of line.
                let nt = next.trim_start();
                let has_arrow = nt.contains(" -> ") || nt.ends_with(" ->");
                if has_arrow
                    && (nt.starts_with('_')
                        || nt.chars().next().is_some_and(|c| c.is_ascii_uppercase()))
                {
                    break;
                }
            }
            body_lines.push(next.to_string());
            i += 1;
        }
        arms.push(Arm {
            constructor,
            binders,
            body: body_lines.join("\n"),
        });
    }
    Some(arms)
}

/// Validate an arm constructor name. Either `_` (wildcard) or a
/// Capitalised identifier (constructor naming).
fn is_valid_arm_constructor(s: &str) -> bool {
    if s == "_" {
        return true;
    }
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_uppercase() => chars.all(|c| c.is_alphanumeric() || c == '_'),
        _ => false,
    }
}

/// Index of the `}` matching the `{` at position 0 of `s`, or
/// `None` if unbalanced. Skips surface `"..."` / `@"..."` literals
/// so braces inside trace / fail / `expect` messages don't
/// desync the depth counter, mirroring the brace-counter in
/// `split_validator_entry_block`.
fn match_close_brace(s: &str) -> Option<usize> {
    assert!(s.starts_with('{'));
    let bytes = s.as_bytes();
    let mut depth = 0_isize;
    let mut in_string = false;
    let mut prev_backslash = false;
    for (i, &b) in bytes.iter().enumerate() {
        if in_string {
            match b {
                b'\\' if !prev_backslash => prev_backslash = true,
                b'"' if !prev_backslash => {
                    in_string = false;
                    prev_backslash = false;
                }
                _ => prev_backslash = false,
            }
            continue;
        }
        match b {
            b'"' => in_string = true,
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Dedent an arm body by the minimum leading-whitespace count
/// across non-empty lines, keeping internal indentation relative.
fn dedent_arm_body(body: &str) -> String {
    let lines: Vec<&str> = body.lines().collect();
    let min_indent = lines
        .iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start().len())
        .min()
        .unwrap_or(0);
    lines
        .iter()
        .map(|l| {
            if l.len() >= min_indent {
                &l[min_indent..]
            } else {
                *l
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Split the first `fn decompiled(...) { ... }` block in `rendered`
/// into `prefix` (text before it), `args` (the parameter list minus
/// parens), `body` (between the opening `{` and its matching `}`),
/// and `suffix` (text after it, e.g. helper functions).
///
/// `None` when no such block is found — the renderer didn't produce
/// the expected shape, so callers fall through to the unwrapped
/// output.
pub(crate) fn split_validator_entry_block(rendered: &str) -> Option<EntryBlock<'_>> {
    let prefix_end = rendered.find("fn decompiled(")?;
    let after_fn = &rendered[prefix_end + "fn decompiled(".len()..];
    let args_end_rel = after_fn.find(')')?;
    let args = &after_fn[..args_end_rel];
    // After `)`: optional whitespace, then `{`.
    let after_args = &after_fn[args_end_rel + 1..];
    let brace_open_rel = after_args.find('{')?;
    let body_start_abs =
        prefix_end + "fn decompiled(".len() + args_end_rel + 1 + brace_open_rel + 1;

    // Brace-count to the matching `}`, skipping `"..."` and `@"..."`
    // string contents so braces inside them don't desync the depth.
    let mut depth = 1usize;
    let mut in_string = false;
    let mut prev_backslash = false;
    let bytes = rendered.as_bytes();
    let mut idx = body_start_abs;
    while idx < bytes.len() {
        let b = bytes[idx];
        if in_string {
            match b {
                b'\\' if !prev_backslash => prev_backslash = true,
                b'"' if !prev_backslash => in_string = false,
                _ => prev_backslash = false,
            }
        } else {
            match b {
                b'"' => in_string = true,
                b'{' => depth += 1,
                b'}' => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                _ => {}
            }
        }
        idx += 1;
    }
    if depth != 0 {
        return None;
    }
    let body_end_abs = idx;
    let body_raw = &rendered[body_start_abs..body_end_abs];
    let body = body_raw.trim_matches('\n');
    let prefix = &rendered[..prefix_end];
    let suffix_start = body_end_abs + 1; // past the closing `}`
    let suffix = if suffix_start < rendered.len() {
        rendered[suffix_start..].trim_start_matches('\n')
    } else {
        ""
    };
    Some(EntryBlock {
        prefix,
        args,
        body,
        suffix,
    })
}

/// Split result for `split_validator_entry_block`.
pub(crate) struct EntryBlock<'a> {
    pub prefix: &'a str,
    pub args: &'a str,
    pub body: &'a str,
    pub suffix: &'a str,
}

/// Scan a rendered body for the script-purpose dispatch shape and
/// return the purposes it dispatches on, in body order. Same gates
/// as `prune_purpose_dispatch`: ≥2 purpose arms, all non-wildcard
/// arms drawn from the known purpose set.
///
/// Empty when there is no such dispatch — that is how
/// `wrap_render_with_flat_validator` decides whether to emit its
/// `// Inferred purposes:` header.
pub(crate) fn infer_purposes_from_body(body: &str) -> Vec<ValidatorPurpose> {
    const PURPOSE_NAMES: &[&str] = &[
        "Spending",
        "Minting",
        "Rewarding",
        "Certifying",
        "Voting",
        "Proposing",
    ];

    let trimmed = body.trim_start();
    if !trimmed.starts_with("when ") {
        return Vec::new();
    }
    // Find the opening `{`.
    let mut open_brace: Option<usize> = None;
    for (i, c) in trimmed.char_indices() {
        if c == '{' {
            open_brace = Some(i);
            break;
        }
        if c == '\n' {
            return Vec::new();
        }
    }
    let Some(open_brace) = open_brace else {
        return Vec::new();
    };
    if !trimmed[..open_brace].contains(" is ") {
        return Vec::new();
    }
    let Some(close_brace) = match_close_brace(&trimmed[open_brace..]) else {
        return Vec::new();
    };
    let arms_text = &trimmed[open_brace + 1..open_brace + close_brace];
    let after = trimmed[open_brace + close_brace + 1..].trim();
    if !after.is_empty() {
        return Vec::new();
    }
    let Some(arms) = parse_when_arms(arms_text) else {
        return Vec::new();
    };
    // Collect purpose arms in body order.
    let mut purposes: Vec<ValidatorPurpose> = Vec::new();
    for arm in &arms {
        if arm.constructor == "_" {
            continue;
        }
        if !PURPOSE_NAMES.contains(&arm.constructor.as_str()) {
            // Mixed in non-purpose constructor — bail.
            return Vec::new();
        }
        let purpose = match arm.constructor.as_str() {
            "Spending" => ValidatorPurpose::Spend,
            "Minting" => ValidatorPurpose::Mint,
            "Rewarding" => ValidatorPurpose::Withdraw,
            "Certifying" => ValidatorPurpose::Certificate,
            "Voting" => ValidatorPurpose::Vote,
            "Proposing" => ValidatorPurpose::Propose,
            _ => unreachable!(),
        };
        if !purposes.contains(&purpose) {
            purposes.push(purpose);
        }
    }
    // Require ≥2 distinct purposes: one purpose arm plus a wildcard
    // could be a regular constructor When over a non-purpose union.
    if purposes.len() < 2 {
        return Vec::new();
    }
    purposes
}

/// Wrap as a flat `validator <name>(<args>) { <body> }` — no purpose
/// arms. Used when there is no blueprint: the purpose-arm form
/// cannot be reconstructed. An optional `// Inferred purposes:`
/// header names purposes found in an explicit dispatch.
///
/// Not valid surface syntax (a real validator needs purpose arms); the flat
/// form is honest about the unknown purpose.
pub(crate) fn wrap_render_with_flat_validator(rendered: &str, validator_name: &str) -> String {
    wrap_render_with_flat_validator_inner(rendered, validator_name, None)
}

/// `wrap_render_with_flat_validator` with the purposes supplied by
/// the caller (from AST-level `validator_shape::detect_dispatch`),
/// skipping the string-parsing `infer_purposes_from_body`.
pub(crate) fn wrap_render_with_flat_validator_using_purposes(
    rendered: &str,
    validator_name: &str,
    purposes: &[ValidatorPurpose],
) -> String {
    wrap_render_with_flat_validator_inner(rendered, validator_name, Some(purposes))
}

fn wrap_render_with_flat_validator_inner(
    rendered: &str,
    validator_name: &str,
    ast_purposes: Option<&[ValidatorPurpose]>,
) -> String {
    let Some(entry) = split_validator_entry_block(rendered) else {
        return rewrite_expect_bang_calls(&merge_when_arms_with_or_pattern(
            &promote_module_level_lets_to_const(rendered),
        ));
    };
    let body = dedent_block(entry.body);
    let purposes_owned: Vec<ValidatorPurpose>;
    let purposes: &[ValidatorPurpose] = match ast_purposes {
        Some(p) => p,
        None => {
            purposes_owned = infer_purposes_from_body(&body);
            &purposes_owned
        }
    };
    // Hoist module-level `const` decls above the validator
    // wrap so constants sit at the top of the file.
    let (hoisted_consts, helpers_suffix) = if entry.suffix.is_empty() {
        (String::new(), String::new())
    } else {
        let promoted = promote_module_level_lets_to_const(entry.suffix);
        hoist_module_level_consts(&promoted)
    };

    let mut out = String::new();
    out.push_str(entry.prefix);
    if !hoisted_consts.is_empty() {
        out.push_str(&hoisted_consts);
        out.push('\n');
    }
    if !purposes.is_empty() {
        let names: Vec<&str> = purposes.iter().map(|p| p.keyword()).collect();
        out.push_str(&format!("// Inferred purposes: {}\n", names.join(", ")));
    }
    out.push_str("validator ");
    out.push_str(validator_name);
    out.push('(');
    if entry.args.is_empty() {
        out.push('_');
    } else {
        out.push_str(entry.args);
    }
    out.push_str(") {\n");
    for line in body.lines() {
        if line.is_empty() {
            out.push('\n');
        } else {
            out.push_str("  ");
            out.push_str(line);
            out.push('\n');
        }
    }
    out.push('}');
    if !helpers_suffix.is_empty() {
        out.push('\n');
        out.push_str(&helpers_suffix);
    }
    rewrite_expect_bang_calls(&merge_when_arms_with_or_pattern(&out))
}

/// Top-level wrapper: turn the renderer's output into the final
/// `validator NAME { ... }` block. With no `fn decompiled(...)`
/// shape to wrap, only the text-level fixes are applied.
pub(crate) fn wrap_render_with_validator_block(rendered: &str, meta: &ValidatorMeta) -> String {
    wrap_render_with_validator_block_with_bodies(rendered, meta, None)
}

/// `wrap_render_with_validator_block` with optional per-purpose AST bodies.
pub(crate) fn wrap_render_with_validator_block_with_bodies(
    rendered: &str,
    meta: &ValidatorMeta,
    purpose_bodies: Option<&[(ValidatorPurpose, String)]>,
) -> String {
    let Some(entry) = split_validator_entry_block(rendered) else {
        // Even without the wrap, the text-level fixes apply.
        return rewrite_expect_bang_calls(&merge_when_arms_with_or_pattern(
            &promote_module_level_lets_to_const(rendered),
        ));
    };
    // Trim per-line de-indent if the body was indented inside the fn.
    let body = dedent_block(entry.body);
    let block = render_validator_block_with_bodies(meta, &body, entry.args, 2, purpose_bodies);
    // Hoist module-level `const` decls above the validator
    // block so constants sit at the top of the file.
    let (hoisted_consts, helpers_suffix) = if entry.suffix.is_empty() {
        (String::new(), String::new())
    } else {
        let promoted = promote_module_level_lets_to_const(entry.suffix);
        hoist_module_level_consts(&promoted)
    };
    let mut out = String::new();
    out.push_str(entry.prefix);
    if !hoisted_consts.is_empty() {
        out.push_str(&hoisted_consts);
        out.push('\n');
    }
    out.push_str(&block);
    if !helpers_suffix.is_empty() {
        out.push('\n');
        out.push_str(&helpers_suffix);
    }
    rewrite_expect_bang_calls(&merge_when_arms_with_or_pattern(&out))
}

/// `Apply(Var("expect!"), [arg])` prints as `expect!(arg)`, which is
/// not surface syntax (`expect` is a statement). Rewrite `expect!(`
/// to `expect (` — a valid parenthesized statement.
///
/// Skip when the parens have a top-level comma: `expect (cond, body)`
/// would parse as `expect <tuple>`. Do not rewrite inside `@"..."`
/// literals. `expect!.fst` is untouched (`!` is followed by `.`).
pub(crate) fn rewrite_expect_bang_calls(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut i = 0;
    while i < bytes.len() {
        // Copy `@"..."` string literals through verbatim: anything
        // inside, `expect!(` included, is pinned text.
        if i + 1 < bytes.len() && bytes[i] == b'@' && bytes[i + 1] == b'"' {
            out.push('@');
            out.push('"');
            i += 2;
            while i < bytes.len() {
                let c = bytes[i];
                out.push(c as char);
                i += 1;
                if c == b'\\' && i < bytes.len() {
                    out.push(bytes[i] as char);
                    i += 1;
                } else if c == b'"' {
                    break;
                }
            }
            continue;
        }
        // Match `expect!(` (8 chars) at the current position.
        if bytes[i..].starts_with(b"expect!(") {
            // Find matching `)` by paren depth. A top-level `,` marks
            // a multi-arg call, which would rewrite to `expect <tuple>`.
            let open_idx = i + 8; // first char after `(`
            let mut depth = 1_usize;
            let mut saw_top_comma = false;
            let mut close_idx: Option<usize> = None;
            let mut k = open_idx;
            // Defensive: skip string literals inside the parens.
            while k < bytes.len() {
                let c = bytes[k];
                if c == b'@' && k + 1 < bytes.len() && bytes[k + 1] == b'"' {
                    k += 2;
                    while k < bytes.len() {
                        let sc = bytes[k];
                        k += 1;
                        if sc == b'\\' && k < bytes.len() {
                            k += 1;
                        } else if sc == b'"' {
                            break;
                        }
                    }
                    continue;
                }
                if c == b'(' {
                    depth += 1;
                } else if c == b')' {
                    depth -= 1;
                    if depth == 0 {
                        close_idx = Some(k);
                        break;
                    }
                } else if c == b',' && depth == 1 {
                    saw_top_comma = true;
                }
                k += 1;
            }
            if let Some(close) = close_idx
                && !saw_top_comma
            {
                // Safe rewrite: `expect!(<expr>)` → `expect (<expr>)`.
                out.push_str("expect (");
                out.push_str(&text[open_idx..close]);
                out.push(')');
                i = close + 1;
                continue;
            }
            // Unbalanced or multi-arg: emit the original `expect!(`
            // unchanged so the marker stays visible downstream.
            out.push_str("expect!(");
            i += 8;
            continue;
        }
        out.push(bytes[i] as char);
        i += 1;
    }
    out
}

/// Merge adjacent `when` arms with identical single-line bodies into
/// one `|`-pattern arm: `Constr<0> -> X; Constr<1> -> X` collapses to
/// `Constr<0> | Constr<1> -> X`. Safe only for tag-only patterns (no
/// field binders), hence the restriction to the literal `Constr<N>`
/// shape the renderer emits for blueprint-unresolved tags; adjacent
/// same-indent same-body runs are rewritten in place. Multi-line
/// bodies (ending in `{`, or continuing on the next line) are out of
/// reach for a line-at-a-time pass and left alone.
pub(crate) fn merge_when_arms_with_or_pattern(text: &str) -> String {
    let lines: Vec<&str> = text.lines().collect();
    let mut out: Vec<String> = Vec::with_capacity(lines.len());
    let mut i = 0;
    while i < lines.len() {
        let Some((indent, tag, body)) = parse_constr_arm_line(lines[i]) else {
            out.push(lines[i].to_string());
            i += 1;
            continue;
        };
        // Try to extend the run while indent + body match exactly.
        let mut tags: Vec<usize> = vec![tag];
        let mut j = i + 1;
        while j < lines.len() {
            let Some((next_indent, next_tag, next_body)) = parse_constr_arm_line(lines[j]) else {
                break;
            };
            if next_indent != indent || next_body != body {
                break;
            }
            tags.push(next_tag);
            j += 1;
        }
        if tags.len() >= 2 {
            // Emit the merged arm. Pattern order preserved.
            let patterns: Vec<String> = tags.iter().map(|t| format!("Constr<{}>", t)).collect();
            out.push(format!("{}{} -> {}", indent, patterns.join(" | "), body));
            i = j;
        } else {
            out.push(lines[i].to_string());
            i += 1;
        }
    }
    let mut result = out.join("\n");
    if text.ends_with('\n') {
        result.push('\n');
    }
    result
}

/// Parse `<indent>Constr<N> -> <body>` where `<body>` is a single-line
/// expression: non-empty and not ending in a token that continues onto
/// the next line. Returns `(indent, tag, body)` on match.
fn parse_constr_arm_line(line: &str) -> Option<(&str, usize, &str)> {
    // Split into leading indent + rest.
    let trim_start = line.len() - line.trim_start_matches(' ').len();
    let indent = &line[..trim_start];
    let rest = &line[trim_start..];
    // Match `Constr<` prefix.
    let after_constr = rest.strip_prefix("Constr<")?;
    // Find the closing `>` of the tag.
    let close = after_constr.find('>')?;
    let tag_str = &after_constr[..close];
    let after_tag = &after_constr[close + 1..];
    // Tag must parse as a non-negative integer.
    let tag: usize = tag_str.parse().ok()?;
    // After the tag must come ` -> ` exactly: a `Constr<0>(payload)`
    // pattern binds a field, and Or-patterns can't merge bindings.
    let body = after_tag.strip_prefix(" -> ")?;
    // Body must be non-empty and complete on this line. `Constr<N> ->
    // foo(` / `-> [` / `-> a +` continue on the next line, and
    // merging them would splice a tag pattern onto an unrelated
    // continuation, so a body ending in a continuation token is
    // rejected. So is a body already containing `|`: a second merge
    // over an Or-pattern would be ambiguous (this pass runs once, so
    // it cannot arise).
    let trimmed_body = body.trim_end();
    if trimmed_body.is_empty() {
        return None;
    }
    // Trailing tokens that mean the body continues on the next line.
    // Bare `<` / `>` are deliberately absent: a `Constr<2>` body ends
    // in `>` as the tag bracket, so including them would flag every
    // such arm as a continuation. `<=` / `>=` stay. A relational
    // expression that really wraps after a bare `<` / `>` is fine to
    // merge — the continuation attaches to the expression, not to the
    // pattern.
    const CONTINUATION_SUFFIXES: &[&str] = &[
        "{", "(", "[", ",", "+", "-", "*", "/", "%", "&&", "||", "==", "!=", "<=", ">=", "=", "<>",
        "..", "::", "->",
    ];
    for suffix in CONTINUATION_SUFFIXES {
        if trimmed_body.ends_with(suffix) {
            return None;
        }
    }
    // A body containing `|` would merge into `A | B -> X | Y`, where the
    // body's `|` collides with the pattern separator. Bail.
    if trimmed_body.contains(" | ") {
        return None;
    }
    Some((indent, tag, trimmed_body))
}

/// Split mixed top-level text into two strings: the `const`
/// declarations, and everything else (fn / rec fn / validator).
/// Callers run it after `promote_module_level_lets_to_const` to
/// hoist the constants above the validator wrap; otherwise they
/// trail the end of the file.
///
/// A `const` block spans from a `const ` line to the next line
/// starting with a top-level keyword (`const`/`fn`/`rec fn`/
/// `pub`/`validator`) or EOF; indented or blank continuation
/// lines belong to the const.
pub(crate) fn hoist_module_level_consts(text: &str) -> (String, String) {
    let lines: Vec<&str> = text.lines().collect();
    let mut consts: Vec<String> = Vec::new();
    let mut others: Vec<String> = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        if line.starts_with("const ") {
            let mut block: Vec<String> = vec![line.to_string()];
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
                block.push(next.to_string());
                j += 1;
            }
            // Trim trailing blank continuation lines.
            while block.last().is_some_and(|l| l.trim().is_empty()) {
                block.pop();
            }
            consts.extend(block);
            i = j;
        } else {
            others.push(line.to_string());
            i += 1;
        }
    }
    let consts_str = if consts.is_empty() {
        String::new()
    } else {
        let mut s = consts.join("\n");
        s.push('\n');
        s
    };
    let others_str = if others.is_empty() {
        String::new()
    } else {
        others.join("\n")
    };
    (consts_str, others_str)
}

/// Rewrite column-0 (module scope) `let X = ...` lines to `const`.
/// Indented `let` inside `validator` / `fn` bodies stays.
pub(crate) fn promote_module_level_lets_to_const(text: &str) -> String {
    let mut lines = Vec::new();
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("let ") {
            // Column 0: `let X = ...` → `const X = ...`.
            let mut converted = String::with_capacity(line.len() + 2);
            converted.push_str("const ");
            converted.push_str(rest);
            lines.push(converted);
        } else {
            lines.push(line.to_string());
        }
    }
    let mut result = lines.join("\n");
    if text.ends_with('\n') {
        result.push('\n');
    }
    result
}

/// Strip a single common leading-indent prefix from every non-empty
/// line in `s`. Mirrors what the renderer does inside `fn { ... }`
/// bodies (typically 2-space indent).
fn dedent_block(s: &str) -> String {
    let mut common = usize::MAX;
    for line in s.lines() {
        if line.trim().is_empty() {
            continue;
        }
        let n = line.chars().take_while(|c| *c == ' ').count();
        common = common.min(n);
    }
    if common == 0 || common == usize::MAX {
        return s.to_string();
    }
    s.lines()
        .map(|line| {
            if line.len() < common {
                line
            } else {
                &line[common..]
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Return the second-to-last segment of a blueprint title
/// (`<module>.<validator>.<purpose>`) as the validator name.
fn derive_validator_name(title: &str) -> Option<String> {
    let mut segs: Vec<&str> = title.split('.').collect();
    if segs.len() < 2 {
        // Title doesn't have a purpose suffix; treat the whole thing
        // as the name.
        return Some(title.to_string());
    }
    // Drop the trailing purpose segment.
    segs.pop();
    // The last remaining segment is the validator name.
    segs.last().map(|s| s.to_string())
}

#[cfg(test)]
mod tests;
