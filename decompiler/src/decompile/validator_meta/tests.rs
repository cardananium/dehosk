use super::*;

#[test]
fn fallback_is_else_only() {
    let m = ValidatorMeta::fallback();
    assert_eq!(m.name, "decompiled");
    assert_eq!(m.entries.len(), 1);
    assert_eq!(m.entries[0].purpose, ValidatorPurpose::Else);
    assert!(
        m.entries[0].params.is_empty(),
        "fallback Else entry has no explicit params; renderer chooses based on entry_args"
    );
    assert!(m.has_else());
}

#[test]
fn keyword_maps_to_rendered_surface() {
    assert_eq!(ValidatorPurpose::Spend.keyword(), "spend");
    assert_eq!(ValidatorPurpose::Mint.keyword(), "mint");
    assert_eq!(ValidatorPurpose::Withdraw.keyword(), "withdraw");
    assert_eq!(ValidatorPurpose::Certificate.keyword(), "certificate");
    assert_eq!(ValidatorPurpose::Vote.keyword(), "vote");
    assert_eq!(ValidatorPurpose::Propose.keyword(), "propose");
    assert_eq!(ValidatorPurpose::Else.keyword(), "else");
}

/// `ALL` is a hand-written list, so the compiler is made to check it: the
/// `match` below has no wildcard arm, and every variant must both appear
/// there and be found in `ALL`. Adding a purpose without extending `ALL`
/// fails this test; adding one without extending the `match` fails the
/// BUILD. Without both, a new purpose would print a handler that
/// `fn_blocks`' wrap guard does not recognise, and the guard would go quiet
/// on exactly the text it exists to refuse.
#[test]
fn all_is_exhaustive() {
    fn present(p: ValidatorPurpose) -> bool {
        ValidatorPurpose::ALL.contains(&p)
    }
    for p in ValidatorPurpose::ALL {
        // No `_` arm: the compiler will not let this go stale.
        let named = match p {
            ValidatorPurpose::Spend => present(ValidatorPurpose::Spend),
            ValidatorPurpose::Mint => present(ValidatorPurpose::Mint),
            ValidatorPurpose::Withdraw => present(ValidatorPurpose::Withdraw),
            ValidatorPurpose::Certificate => present(ValidatorPurpose::Certificate),
            ValidatorPurpose::Vote => present(ValidatorPurpose::Vote),
            ValidatorPurpose::Propose => present(ValidatorPurpose::Propose),
            ValidatorPurpose::Else => present(ValidatorPurpose::Else),
        };
        assert!(named, "{p:?} missing from ValidatorPurpose::ALL");
    }
    // A duplicate would satisfy `contains` while hiding a missing variant.
    let mut keywords: Vec<&str> = ValidatorPurpose::ALL.iter().map(|p| p.keyword()).collect();
    keywords.sort_unstable();
    let distinct = keywords.len();
    keywords.dedup();
    assert_eq!(keywords.len(), distinct, "ALL repeats a purpose");
}

#[test]
fn from_title_suffix_round_trip() {
    for p in [
        ValidatorPurpose::Spend,
        ValidatorPurpose::Mint,
        ValidatorPurpose::Withdraw,
        ValidatorPurpose::Certificate,
        ValidatorPurpose::Vote,
        ValidatorPurpose::Propose,
        ValidatorPurpose::Else,
    ] {
        assert_eq!(ValidatorPurpose::from_title_suffix(p.keyword()), Some(p));
    }
    assert_eq!(ValidatorPurpose::from_title_suffix("not_a_purpose"), None);
    assert_eq!(ValidatorPurpose::from_title_suffix(""), None);
    // Aiken blueprint titles still use `.publish`.
    assert_eq!(
        ValidatorPurpose::from_title_suffix("publish"),
        Some(ValidatorPurpose::Certificate)
    );
}

#[test]
fn from_blueprint_group_picks_name_from_middle_segment() {
    let meta = ValidatorMeta::from_blueprint_group(vec![
        ("multi.redeem.spend", vec!["d".into(), "r".into()]),
        ("multi.redeem.mint", vec!["r".into()]),
        ("multi.redeem.else", vec!["_".into()]),
    ])
    .unwrap();
    assert_eq!(meta.name, "redeem");
    assert_eq!(meta.entries.len(), 3);
    assert_eq!(meta.entries[0].purpose, ValidatorPurpose::Spend);
    assert_eq!(meta.entries[1].purpose, ValidatorPurpose::Mint);
    assert_eq!(meta.entries[2].purpose, ValidatorPurpose::Else);
    // Else entries discard their blueprint-supplied params
    // (the renderer picks `_` or entry_args).
    assert!(meta.entries[2].params.is_empty());
    assert!(meta.has_else());
}

#[test]
fn from_blueprint_group_handles_doubled_module_name() {
    // `hello_world.hello_world.spend` → name `hello_world`.
    let meta = ValidatorMeta::from_blueprint_group(vec![
        (
            "hello_world.hello_world.spend",
            vec!["d".into(), "r".into()],
        ),
        ("hello_world.hello_world.else", vec!["_".into()]),
    ])
    .unwrap();
    assert_eq!(meta.name, "hello_world");
    assert_eq!(meta.entries.len(), 2);
}

#[test]
fn from_blueprint_group_skips_unknown_purpose_suffix() {
    let meta = ValidatorMeta::from_blueprint_group(vec![
        ("mod.foo.spend", vec!["d".into()]),
        ("mod.foo.weirdsuffix", vec!["x".into()]),
        ("mod.foo.else", vec!["_".into()]),
    ])
    .unwrap();
    assert_eq!(meta.entries.len(), 2);
    assert_eq!(meta.entries[0].purpose, ValidatorPurpose::Spend);
    assert_eq!(meta.entries[1].purpose, ValidatorPurpose::Else);
}

#[test]
fn from_blueprint_group_returns_none_for_empty_input() {
    let empty: Vec<(&str, Vec<String>)> = vec![];
    assert!(ValidatorMeta::from_blueprint_group(empty).is_none());
}

#[test]
fn split_entry_block_extracts_single_validator() {
    let rendered = "fn decompiled(script_context) {\n  let x = 1\n  x\n}\n";
    let block = split_validator_entry_block(rendered).unwrap();
    assert_eq!(block.prefix, "");
    assert_eq!(block.args, "script_context");
    assert_eq!(block.body, "  let x = 1\n  x");
    assert_eq!(block.suffix, "");
}

#[test]
fn split_entry_block_separates_helpers_into_suffix() {
    let rendered = "fn decompiled(ctx) {\n  body\n}\nfn helper(x) {\n  x\n}\n";
    let block = split_validator_entry_block(rendered).unwrap();
    assert_eq!(block.args, "ctx");
    assert_eq!(block.body, "  body");
    assert_eq!(block.suffix, "fn helper(x) {\n  x\n}\n");
}

#[test]
fn split_entry_block_handles_nested_braces_in_body() {
    let rendered = "fn decompiled(ctx) {\n  when ctx is {\n    Foo -> 1\n    _ -> 0\n  }\n}\n";
    let block = split_validator_entry_block(rendered).unwrap();
    assert!(block.body.contains("when ctx is"));
    assert!(block.body.contains("_ -> 0"));
}

#[test]
fn split_entry_block_handles_brace_in_string_literal() {
    // A `@"..."` literal can contain `{` / `}` that the brace
    // counter must not treat as braces.
    let rendered = "fn decompiled(ctx) {\n  let s = @\"hello {world}\"\n  s\n}\n";
    let block = split_validator_entry_block(rendered).unwrap();
    assert!(block.body.contains("hello {world}"));
    assert!(block.body.contains("let s"));
    // The body must end before the *outer* `}` of the fn, not before
    // the `}` inside the string.
    assert!(block.suffix.is_empty());
}

#[test]
fn split_entry_block_handles_escaped_quote_in_string() {
    // `@"say \"hi\""` — neither the inner `\"` nor braces inside it
    // may confuse the string-state machine.
    let rendered = "fn decompiled(ctx) {\n  let s = @\"say \\\"{hi}\\\"\"\n  s\n}\n";
    let block = split_validator_entry_block(rendered).unwrap();
    assert!(block.body.contains("say"));
    assert!(block.suffix.is_empty());
}

#[test]
fn render_validator_block_else_with_non_underscore_args_binds_them() {
    // An Else entry with no explicit params binds non-trivial
    // `entry_args` rather than collapsing to `_` — otherwise the body
    // loses its `script_context` reference.
    let meta = ValidatorMeta::fallback();
    let out = render_validator_block(&meta, "script_context.tx_info", "script_context", 2);
    assert!(
        out.contains("else(script_context)"),
        "else arm should bind `script_context`, got:\n{out}"
    );
}

#[test]
fn render_validator_block_else_with_underscore_args_keeps_underscore() {
    // When `entry_args` is the literal `_`, the Else arm stays as
    // `else(_)` (nothing to bind).
    let meta = ValidatorMeta::fallback();
    let out = render_validator_block(&meta, "True", "_", 2);
    assert!(out.contains("else(_)"));
}

#[test]
fn split_entry_block_returns_none_when_marker_missing() {
    let rendered = "fn anonymous() {\n  body\n}\n";
    assert!(split_validator_entry_block(rendered).is_none());
}

#[test]
fn render_validator_block_single_else_entry() {
    let meta = ValidatorMeta::fallback();
    let body = "let x = 1\nx";
    let out = render_validator_block(&meta, body, "_", 2);
    assert!(out.contains("validator decompiled {"));
    assert!(out.contains("else(_) {"));
    assert!(out.contains("    let x = 1"));
    assert!(out.contains("    x"));
}

/// When the body is a script-purpose dispatch,
/// each entry's rendered body is pruned to its matching arm.
#[test]
fn p2_2_prunes_purpose_dispatch_per_entry() {
    let meta = ValidatorMeta::from_blueprint_group(vec![
        (
            "multi.redeem.spend",
            vec!["datum".into(), "redeemer".into()],
        ),
        ("multi.redeem.mint", vec!["redeemer".into()]),
    ])
    .unwrap();
    // Body is a top-level When dispatching on script_purpose.
    let body = "when script_context.purpose is {\n  Spending(_) -> spend_body\n  Minting(_) -> mint_body\n}";
    let out = render_validator_block(&meta, body, "ctx", 2);
    // Spend entry's body should contain spend_body and NOT mint_body.
    assert!(
        out.contains("spend(datum, redeemer) {\n    spend_body\n"),
        "Spend entry must have pruned spend_body: {out}"
    );
    // Mint entry's body should contain mint_body and NOT spend_body.
    let mint_section_start = out
        .find("mint(redeemer) {")
        .expect("mint entry must be present");
    let mint_section = &out[mint_section_start..];
    assert!(
        mint_section.contains("mint_body"),
        "Mint entry must have mint_body: {mint_section}"
    );
    assert!(
        !mint_section[..mint_section.find("else(").unwrap_or(mint_section.len())]
            .contains("spend_body"),
        "Mint entry must NOT contain spend_body before else: {mint_section}"
    );
    // When dispatch fully pruned — no `when script_context.purpose is`
    // surfaces in the output.
    assert!(
        !out.contains("when script_context.purpose is"),
        "dispatch When must be pruned: {out}"
    );
}

/// When no arm matches the entry's purpose, emit `fail`.
#[test]
fn p2_2_emits_fail_when_purpose_arm_missing() {
    // Validator declares spend+mint, but the dispatch only handles
    // Minting+Rewarding — Spend should get `fail`.
    let meta = ValidatorMeta::from_blueprint_group(vec![
        ("p.v.spend", vec!["d".into(), "r".into()]),
        ("p.v.mint", vec!["r".into()]),
    ])
    .unwrap();
    let body = "when script_info is {\n  Minting(_) -> mint_body\n  Rewarding(_) -> rew_body\n}";
    let out = render_validator_block(&meta, body, "ctx", 2);
    let spend_start = out.find("spend(d, r) {").unwrap();
    let mint_start = out.find("mint(r) {").unwrap();
    let spend_section = &out[spend_start..mint_start];
    assert!(
        spend_section.contains("fail"),
        "Spend entry must contain `fail` (no matching arm in dispatch): {spend_section}"
    );
    let mint_section = &out[mint_start..];
    assert!(
        mint_section.contains("mint_body"),
        "Mint entry must have mint_body: {mint_section}"
    );
}

/// When the body is NOT a recognised dispatch shape (e.g. a
/// regular Constructor When over a non-purpose type, or a
/// non-When body), prune is a no-op — body unchanged per entry.
#[test]
fn p2_2_leaves_unchanged_when_body_is_not_a_purpose_dispatch() {
    let meta = ValidatorMeta::from_blueprint_group(vec![
        ("p.v.spend", vec!["d".into(), "r".into()]),
        ("p.v.mint", vec!["r".into()]),
    ])
    .unwrap();
    // Body is a regular When but over a non-purpose subject.
    let body = "when option is {\n  Some(x) -> handle(x)\n  None -> default\n}";
    let out = render_validator_block(&meta, body, "ctx", 2);
    // Both entries should have the full body (unchanged).
    let spend_section = &out[out.find("spend(").unwrap()..out.find("mint(").unwrap()];
    assert!(spend_section.contains("Some(x) -> handle(x)"));
    assert!(spend_section.contains("None -> default"));
}

/// Single-entry validators don't trigger pruning (no
/// dispatch to prune against).
#[test]
fn p2_2_skips_single_entry_validators() {
    let meta =
        ValidatorMeta::from_blueprint_group(vec![("p.v.spend", vec!["d".into(), "r".into()])])
            .unwrap();
    let body = "when script_context.purpose is {\n  Spending(_) -> spend_body\n  Minting(_) -> mint_body\n}";
    let out = render_validator_block(&meta, body, "ctx", 2);
    // Spend entry should have the FULL body (no pruning for single-entry).
    assert!(out.contains("when script_context.purpose is"));
    assert!(out.contains("Spending(_) -> spend_body"));
    assert!(out.contains("Minting(_) -> mint_body"));
}

/// Wildcard fallback: an entry whose purpose has no explicit arm
/// uses the dispatch's `_ -> body`.
#[test]
fn p2_2_falls_through_to_wildcard_arm() {
    let meta = ValidatorMeta::from_blueprint_group(vec![
        ("p.v.spend", vec!["d".into(), "r".into()]),
        ("p.v.mint", vec!["r".into()]),
    ])
    .unwrap();
    // Spending is explicit, Minting falls through to `_`.
    let body = "when p is {\n  Spending(_) -> spend_body\n  _ -> default_body\n}";
    let out = render_validator_block(&meta, body, "ctx", 2);
    let mint_start = out.find("mint(r) {").unwrap();
    let else_start = out.find("else(").unwrap();
    let mint_section = &out[mint_start..else_start];
    assert!(
        mint_section.contains("default_body"),
        "Mint entry must use the wildcard arm body: {mint_section}"
    );
}

/// Only fires when ≥2 purpose arms are present. A single
/// purpose arm + wildcard isn't enough to confirm it's a dispatch.
#[test]
fn p2_2_requires_at_least_two_purpose_arms() {
    let meta = ValidatorMeta::from_blueprint_group(vec![
        ("p.v.spend", vec!["d".into(), "r".into()]),
        ("p.v.mint", vec!["r".into()]),
    ])
    .unwrap();
    // Only ONE purpose arm — refuse the prune.
    let body = "when p is {\n  Spending(_) -> spend_body\n  _ -> default_body\n}";
    let out = render_validator_block(&meta, body, "ctx", 2);
    // Spend entry should still have the full When (not just spend_body).
    let spend_start = out.find("spend(d, r) {").unwrap();
    let mint_start = out.find("mint(r) {").unwrap();
    let spend_section = &out[spend_start..mint_start];
    assert!(
        spend_section.contains("when p is"),
        "single-purpose-arm dispatch must not be pruned: {spend_section}"
    );
}

/// Refuse when the body has trailing statements after the
/// When (discarding them would be unsafe).
#[test]
fn p2_2_refuses_when_body_has_trailing_statements() {
    let meta = ValidatorMeta::from_blueprint_group(vec![
        ("p.v.spend", vec!["d".into(), "r".into()]),
        ("p.v.mint", vec!["r".into()]),
    ])
    .unwrap();
    let body =
        "when p is {\n  Spending(_) -> spend_body\n  Minting(_) -> mint_body\n}\n\ntrace @\"end\"";
    let out = render_validator_block(&meta, body, "ctx", 2);
    // Body has `trace` after the when — must NOT prune.
    let spend_section = &out[out.find("spend(").unwrap()..out.find("mint(").unwrap()];
    assert!(
        spend_section.contains("when p is"),
        "body with trailing statements must not be pruned: {spend_section}"
    );
}

/// Refuse when an arm is a non-purpose Constructor pattern.
/// E.g. if the dispatch mixes `Spending(_) -> ...; Some(_) -> ...`,
/// it's not actually a script-purpose dispatch.
#[test]
fn p2_2_refuses_when_arm_is_not_a_known_purpose() {
    let meta = ValidatorMeta::from_blueprint_group(vec![
        ("p.v.spend", vec!["d".into(), "r".into()]),
        ("p.v.mint", vec!["r".into()]),
    ])
    .unwrap();
    let body = "when p is {\n  Spending(_) -> spend_body\n  Minting(_) -> mint_body\n  Some(_) -> other_body\n}";
    let out = render_validator_block(&meta, body, "ctx", 2);
    let spend_section = &out[out.find("spend(").unwrap()..out.find("mint(").unwrap()];
    assert!(
        spend_section.contains("when p is"),
        "dispatch with non-purpose arm must not be pruned: {spend_section}"
    );
}

#[test]
fn render_validator_block_multi_purpose_synthesizes_else_when_missing() {
    // `multi.redeem.spend` + `.mint` (no else entry) → trailing
    // `else(_) { fail }` is auto-emitted.
    let meta = ValidatorMeta::from_blueprint_group(vec![
        (
            "multi.redeem.spend",
            vec!["datum".into(), "redeemer".into()],
        ),
        ("multi.redeem.mint", vec!["redeemer".into()]),
    ])
    .unwrap();
    let out = render_validator_block(&meta, "body", "ctx", 2);
    assert!(out.contains("validator redeem {"));
    assert!(out.contains("spend(datum, redeemer) {"));
    assert!(out.contains("mint(redeemer) {"));
    assert!(out.contains("else(_) {"));
    assert!(out.contains("fail"));
}

/// When body contains `when X is { Spending(...) -> ...;
/// Minting(...) -> ...; }`, `infer_purposes_from_body` returns
/// `[Spend, Mint]` (in body-order).
#[test]
fn infer_purposes_from_body_detects_dispatch() {
    let body = "when script_context.purpose is {\n  Spending(_) -> a\n  Minting(_) -> b\n}";
    let purposes = infer_purposes_from_body(body);
    assert_eq!(
        purposes,
        vec![ValidatorPurpose::Spend, ValidatorPurpose::Mint]
    );
}

/// ≥2 purpose arms required. A single arm doesn't trigger
/// inference (could be a regular Constructor When).
#[test]
fn infer_purposes_from_body_skips_single_purpose() {
    let body = "when X is {\n  Spending(_) -> a\n  _ -> fail\n}";
    let purposes = infer_purposes_from_body(body);
    assert!(purposes.is_empty());
}

/// Bodies that aren't a top-level When return empty.
#[test]
fn infer_purposes_from_body_ignores_non_when_bodies() {
    let body = "let x = 1\nlet y = 2\nx + y";
    assert!(infer_purposes_from_body(body).is_empty());
}

/// A When whose arms aren't pure purpose-constructors is NOT a
/// script-purpose dispatch.
#[test]
fn infer_purposes_from_body_refuses_mixed_arms() {
    let body = "when X is {\n  Spending(_) -> a\n  Some(_) -> b\n}";
    assert!(infer_purposes_from_body(body).is_empty());
}

/// The simplifier can emit a dispatch body as `let purpose =
/// script_context.purpose` followed by `when purpose is { ... }`.
/// The leading lets are preserved and only the trailing When is
/// pruned to the matching arm.
#[test]
fn prune_purpose_dispatch_handles_let_chain_before_when() {
    let body =
        "let purpose = ctx.purpose\nwhen purpose is {\n  Spending(_) -> a\n  Minting(_) -> b\n}";
    let pruned = prune_purpose_dispatch(body, ValidatorPurpose::Spend)
        .expect("expected pruning to succeed on let-chain dispatch");
    assert!(
        pruned.contains("let purpose = ctx.purpose"),
        "leading let-chain should be preserved: {pruned}"
    );
    assert!(
        pruned.contains('a') && !pruned.contains("Spending(_)"),
        "should keep the Spending arm body, drop the dispatch: {pruned}"
    );
    assert!(
        !pruned.contains("Minting(_)"),
        "Minting arm should be pruned out: {pruned}"
    );
}

/// The simplifier sometimes wraps that shape as `expect! when
/// ...`; the `expect!` prefix is stripped with the dispatch.
#[test]
fn prune_purpose_dispatch_handles_expect_bang_when_after_let_chain() {
    let body = "let purpose = ctx.purpose\nexpect! when purpose is {\n  Spending(_) -> a\n  Minting(_) -> b\n}";
    let pruned = prune_purpose_dispatch(body, ValidatorPurpose::Mint)
        .expect("expected pruning to succeed on let-chain + expect! when dispatch");
    assert!(
        pruned.contains("let purpose = ctx.purpose"),
        "leading let-chain should be preserved: {pruned}"
    );
    assert!(
        !pruned.contains("expect!"),
        "`expect!` prefix should be dropped along with the dispatch: {pruned}"
    );
    assert!(
        pruned.contains('b') && !pruned.contains("Minting(_)"),
        "should keep the Minting arm body: {pruned}"
    );
}

/// A V3 multi-purpose dispatch whose arms carry NAMED binders
/// (`Spending(output_reference, datum)`, `Minting(policy_id)`) must
/// restore them with an `expect <Ctor>(<binders>) = <subject>` at the
/// handler top, or the pruned body references them as free variables.
#[test]
fn prune_purpose_dispatch_restores_named_purpose_binders() {
    let body = "let tx_info = script_context.tx_info\nwhen script_context.script_info is {\n  Spending(output_reference, datum) ->\n    when datum is {\n      Foo -> a\n    }\n  Minting(policy_id) ->\n    use(policy_id)\n}";
    let spend =
        prune_purpose_dispatch(body, ValidatorPurpose::Spend).expect("spend prune should succeed");
    assert!(
        spend.contains("expect Spending(output_reference, datum) = script_context.script_info"),
        "spend handler must restore the dropped purpose binders: {spend}"
    );
    assert!(
        spend.contains("when datum is"),
        "spend arm body kept: {spend}"
    );
    assert!(
        spend.contains("let tx_info = script_context.tx_info"),
        "leading let-chain preserved before the expect: {spend}"
    );
    let mint =
        prune_purpose_dispatch(body, ValidatorPurpose::Mint).expect("mint prune should succeed");
    assert!(
        mint.contains("expect Minting(policy_id) = script_context.script_info"),
        "mint handler must restore the policy_id binder: {mint}"
    );
}

/// All-wildcard binders carry nothing to restore: no `expect` is
/// emitted and the body is the pruned arm verbatim. Guards the
/// V1/V2-style `.purpose` dispatch.
#[test]
fn prune_purpose_dispatch_skips_expect_for_wildcard_binders() {
    let body = "when script_context.script_info is {\n  Spending(_) -> a\n  Minting(_) -> b\n}";
    let spend =
        prune_purpose_dispatch(body, ValidatorPurpose::Spend).expect("spend prune should succeed");
    assert!(
        !spend.contains("expect"),
        "all-wildcard binders must not emit an expect: {spend}"
    );
    assert_eq!(spend.trim(), "a");
}

/// Neither the wildcard-fallback arm nor the synthetic `fail`
/// branch binds purpose fields, so neither restores binders.
#[test]
fn prune_purpose_dispatch_fallback_and_fail_get_no_expect() {
    // Named binders present, but the queried purpose has no arm and no
    // wildcard -> `fail`, with no spurious `expect`.
    let no_match = "when script_context.script_info is {\n  Spending(output_reference, datum) -> a\n  Minting(policy_id) -> b\n}";
    let withdraw = prune_purpose_dispatch(no_match, ValidatorPurpose::Withdraw)
        .expect("prune should still succeed (>=2 purpose arms)");
    assert_eq!(
        withdraw.trim(),
        "fail",
        "missing purpose -> fail: {withdraw}"
    );
    assert!(
        !withdraw.contains("expect"),
        "fail branch gets no expect: {withdraw}"
    );

    // A wildcard fallback is used verbatim, with no expect injected.
    let with_wildcard = "when script_context.script_info is {\n  Spending(output_reference, datum) -> a\n  Minting(policy_id) -> b\n  _ -> c\n}";
    let withdraw2 = prune_purpose_dispatch(with_wildcard, ValidatorPurpose::Withdraw)
        .expect("prune should succeed with wildcard fallback");
    assert_eq!(
        withdraw2.trim(),
        "c",
        "wildcard fallback body used: {withdraw2}"
    );
    assert!(
        !withdraw2.contains("expect"),
        "wildcard fallback gets no expect: {withdraw2}"
    );
}

/// The simplifier emits `expect when X is { … }, @"msg"` for a
/// V3 multi-purpose dispatch wrapped in an expect statement;
/// the trailing `, @"msg"` must not block the prune.
#[test]
fn prune_purpose_dispatch_tolerates_expect_message_suffix() {
    let body = "expect when ctx.script_info is {\n  Spending(_) -> a\n  Minting(_) -> b\n}, @\"Validator returned false\"";
    let pruned = prune_purpose_dispatch(body, ValidatorPurpose::Spend)
        .expect("expected pruning to succeed with a trailing expect message");
    assert!(pruned.contains('a'), "expected matched arm body: {pruned}");
    assert!(
        !pruned.contains("Minting(_)"),
        "non-matching arm should be pruned: {pruned}"
    );
}

/// The trailing message may contain escaped quotes / characters
/// and the parser must walk through them without bailing.
#[test]
fn prune_purpose_dispatch_handles_escaped_quotes_in_expect_message() {
    let body = "expect when ctx.script_info is {\n  Spending(_) -> a\n  Minting(_) -> b\n}, @\"msg with \\\"nested\\\" escapes\"";
    let pruned = prune_purpose_dispatch(body, ValidatorPurpose::Mint)
        .expect("expected pruning to succeed with escaped quotes in suffix");
    assert!(pruned.contains('b'), "expected matched arm body: {pruned}");
}

/// Content after `}, @"msg"` means the dispatch isn't the whole
/// body — pruning must bail.
#[test]
fn prune_purpose_dispatch_rejects_trailing_statement_after_expect_message() {
    let body = "expect when ctx.script_info is {\n  Spending(_) -> a\n  Minting(_) -> b\n}, @\"msg\"\nlet trailing = 1";
    assert!(
        prune_purpose_dispatch(body, ValidatorPurpose::Spend).is_none(),
        "trailing statement after expect message should disable pruning"
    );
}

/// Only an `expect` / `expect!`-wrapped dispatch carries an
/// error-message arg, so a bare `when X is { … }, @"msg"` must
/// not prune.
#[test]
fn prune_purpose_dispatch_rejects_bare_when_with_trailing_message() {
    let body = "when ctx.script_info is {\n  Spending(_) -> a\n  Minting(_) -> b\n}, @\"msg\"";
    assert!(
        prune_purpose_dispatch(body, ValidatorPurpose::Spend).is_none(),
        "bare when with trailing message should disable pruning"
    );
}

/// `{` / `}` inside a `@"..."` message
/// must not truncate the arm body.
#[test]
fn prune_purpose_dispatch_handles_brace_in_string_literal_in_arm() {
    let body = "when ctx.purpose is {\n  Spending(_) -> fail @\"{}braces inside{string\"\n  Minting(_) -> b\n}";
    let pruned = prune_purpose_dispatch(body, ValidatorPurpose::Spend)
        .expect("expected pruning to succeed even with `{`/`}` inside string literal");
    assert!(
        pruned.contains("{}braces inside{string"),
        "string-literal contents should survive intact: {pruned}"
    );
}

/// `wrap_render_with_flat_validator` emits the flat
/// `validator NAME(args) { body }` form (no `else` arm) and
/// prepends a `// Inferred purposes:` comment when the body
/// contains a multi-purpose dispatch.
#[test]
fn wrap_render_with_flat_validator_emits_inferred_comment() {
    let rendered = "fn decompiled(ctx) {\n  when ctx.purpose is {\n    Spending(_) -> a\n    Minting(_) -> b\n  }\n}";
    let out = wrap_render_with_flat_validator(rendered, "decompiled");
    assert!(
        out.contains("// Inferred purposes: spend, mint"),
        "expected inferred-purposes comment: {out}"
    );
    assert!(
        out.contains("validator decompiled(ctx) {"),
        "flat header: {out}"
    );
    // No `else(...)` arm — flat form.
    assert!(
        !out.contains("else("),
        "flat form should have no `else(`: {out}"
    );
}

/// Single-purpose body: flat form, no comment.
#[test]
fn wrap_render_with_flat_validator_omits_comment_when_single_purpose() {
    let rendered = "fn decompiled(ctx) {\n  expect Spending(_) = ctx.purpose\n  True\n}";
    let out = wrap_render_with_flat_validator(rendered, "decompiled");
    assert!(
        !out.contains("// Inferred purposes:"),
        "no comment for single-purpose body: {out}"
    );
    assert!(out.contains("validator decompiled(ctx) {"));
}

#[test]
fn render_validator_block_with_explicit_else_does_not_double_emit() {
    let meta = ValidatorMeta::from_blueprint_group(vec![
        ("m.v.spend", vec!["d".into(), "r".into()]),
        ("m.v.else", vec!["_".into()]),
    ])
    .unwrap();
    let out = render_validator_block(&meta, "True", "ctx", 2);
    let n_else = out.matches("else(").count();
    assert_eq!(
        n_else, 1,
        "should have exactly one `else(` arm, got:\n{out}"
    );
}

#[test]
fn wrap_render_full_roundtrip() {
    // The fallback Else arm keeps the original lambda's args so body
    // references stay bound: `else(script_context)`.
    let rendered = "fn decompiled(script_context) {\n  True\n}\n";
    let meta = ValidatorMeta::fallback();
    let out = wrap_render_with_validator_block(rendered, &meta);
    assert!(out.contains("validator decompiled {"));
    assert!(
        out.contains("else(script_context) {"),
        "expected Else arm to bind `script_context`, got:\n{out}"
    );
    assert!(out.contains("    True"));
    assert!(!out.contains("fn decompiled("));
}

#[test]
fn wrap_render_preserves_helpers() {
    let rendered = "fn decompiled(ctx) {\n  call_helper(ctx)\n}\nfn helper(x) {\n  x\n}\n";
    let meta = ValidatorMeta::fallback();
    let out = wrap_render_with_validator_block(rendered, &meta);
    assert!(out.contains("validator decompiled {"));
    assert!(out.contains("fn helper(x) {"));
}

#[test]
fn p5_4_promotes_module_level_let_to_const() {
    // Column-0 `let X = ...` → `const X = ...`.
    let text =
        "let z8 = Constr<0>\nlet choose_fst = Constr<0>\nfn helper(x) {\n  let y = x\n  y\n}\n";
    let out = promote_module_level_lets_to_const(text);
    assert!(out.contains("const z8 = Constr<0>"));
    assert!(out.contains("const choose_fst = Constr<0>"));
    // Indented `let` inside fn body MUST stay `let`.
    assert!(out.contains("  let y = x"));
    // No leftover `let z8`/`let choose_fst` at column 0.
    assert!(!out.contains("\nlet z8 ") && !out.starts_with("let z8 "));
    assert!(!out.contains("\nlet choose_fst ") && !out.starts_with("let choose_fst "));
}

#[test]
fn p5_4_preserves_indented_let() {
    let text = "  let x = 1\n    let y = 2\nlet z = 3\n";
    let out = promote_module_level_lets_to_const(text);
    assert!(out.contains("  let x = 1"));
    assert!(out.contains("    let y = 2"));
    assert!(out.contains("const z = 3"));
    // No `const` for indented lets.
    assert!(!out.contains("  const "));
}

#[test]
fn p5_4_preserves_trailing_newline() {
    let text = "let a = 1\n";
    let out = promote_module_level_lets_to_const(text);
    assert_eq!(out, "const a = 1\n");
}

#[test]
fn p5_4_handles_multiline_let_value() {
    // `let z8 = ` on its own line, value continues indented.
    // Only the `let` line should change — continuation stays as-is.
    let text = "let z8 =\n  when fix is {\n    _ -> 0\n  }\nfn other() { 0 }\n";
    let out = promote_module_level_lets_to_const(text);
    assert!(out.starts_with("const z8 =\n"));
    assert!(out.contains("  when fix is {"));
    assert!(out.contains("fn other()"));
}

#[test]
fn wrap_render_passthrough_when_no_marker() {
    let rendered = "fn anonymous() {\n  body\n}\n";
    let meta = ValidatorMeta::fallback();
    let out = wrap_render_with_validator_block(rendered, &meta);
    assert_eq!(
        out, rendered,
        "no marker found — must return input unchanged"
    );
}

#[test]
fn from_blueprint_group_returns_none_when_no_known_purposes() {
    let meta = ValidatorMeta::from_blueprint_group(vec![
        ("mod.foo.unknown1", vec![]),
        ("mod.foo.unknown2", vec![]),
    ]);
    assert!(meta.is_none());
}

#[test]
fn has_else_detects_else_entry() {
    let with_else = ValidatorMeta {
        name: "x".into(),
        entries: vec![
            ValidatorEntry {
                purpose: ValidatorPurpose::Spend,
                params: vec!["d".into(), "r".into()],
            },
            ValidatorEntry {
                purpose: ValidatorPurpose::Else,
                params: vec!["_".into()],
            },
        ],
    };
    assert!(with_else.has_else());
    let no_else = ValidatorMeta {
        name: "x".into(),
        entries: vec![ValidatorEntry {
            purpose: ValidatorPurpose::Spend,
            params: vec!["d".into(), "r".into()],
        }],
    };
    assert!(!no_else.has_else());
}

/// Adjacent `Constr<N> -> X` arms with an identical single-line
/// body collapse to `Constr<0> | Constr<1> | … -> X`; a differing
/// body or indent breaks the run.
#[test]
fn p5_2_merges_adjacent_constr_arms_with_same_body() {
    let input = "when x_165 is {\n  Constr<0> -> Constr<2>\n  Constr<1> -> Constr<2>\n  Constr<2> -> Constr<2>\n  Constr<3> -> Constr<2>\n  Constr<4> -> Constr<1>(x_165)\n}";
    let got = merge_when_arms_with_or_pattern(input);
    assert!(
        got.contains("Constr<0> | Constr<1> | Constr<2> | Constr<3> -> Constr<2>"),
        "expected 4-way merge, got:\n{got}"
    );
    assert!(
        got.contains("Constr<4> -> Constr<1>(x_165)"),
        "non-merge arm (body differs) must survive untouched: {got}"
    );
    assert!(
        !got.contains("\n  Constr<0> -> Constr<2>\n  Constr<1>"),
        "merged arms must collapse, individual Constr<0>/Constr<1> lines must vanish: {got}"
    );
}

/// Only the literal tag-only `Constr<N>` shape merges. surface
/// Or-patterns require identical binders across alternatives, and
/// `Constr<0>(payload)` would bind `payload` in some branches and
/// not others, so patterns with field bindings are left alone.
#[test]
fn p5_2_does_not_merge_patterns_that_bind_fields() {
    let input = "when x is {\n  Constr<0>(payload) -> payload\n  Constr<1>(payload) -> payload\n  _ -> fail\n}";
    let got = merge_when_arms_with_or_pattern(input);
    assert_eq!(
        got, input,
        "patterns with field binders must not be merged; got:\n{got}"
    );
}

/// Multi-line bodies — `->` followed by `{`, or a continuation on
/// the next line — can't merge: this post-process works one line
/// at a time.
#[test]
fn p5_2_does_not_merge_multiline_bodies() {
    let input = "when x is {\n  Constr<0> ->\n    long\n  Constr<1> ->\n    long\n  _ -> fail\n}";
    let got = merge_when_arms_with_or_pattern(input);
    // The arm line ends at `->` with nothing after it, so
    // `parse_constr_arm_line` never matches and both arms survive.
    assert!(
        got.contains("Constr<0> ->\n    long"),
        "multi-line Constr<0> body must survive: {got}"
    );
    assert!(
        got.contains("Constr<1> ->\n    long"),
        "multi-line Constr<1> body must survive: {got}"
    );
}

/// Arms at different indents — two separate `when` blocks
/// juxtaposed in the output — must not merge.
#[test]
fn p5_2_does_not_merge_across_indent_levels() {
    let input = "  Constr<0> -> X\nConstr<1> -> X\n";
    let got = merge_when_arms_with_or_pattern(input);
    assert_eq!(
        got, input,
        "different indents must break the run; got:\n{got}"
    );
}

/// A body ending in `(`, `[`, `,`, or a binary operator continues
/// on the next line, and that continuation belongs to one arm —
/// merging would attach it to the wrong pattern.
#[test]
fn p5_2_does_not_merge_bodies_opening_continuations() {
    for trailing in [
        "foo(", // function call continues
        "[",    // list continues
        "a,",   // tuple/list element continues
        "a +",  // operator continuation
        "a &&", // logical continuation
        "a ==", // comparison continuation
        "a =",  // record/let continuation
        "a ..", // range continuation
    ] {
        let input = format!(
            "  Constr<0> -> {trailing}\n    inner_a\n  Constr<1> -> {trailing}\n    inner_b\n  _ -> fail\n"
        );
        let got = merge_when_arms_with_or_pattern(&input);
        assert_eq!(
            got, input,
            "body ending in continuation `{trailing}` must NOT merge — \
             the next-line continuation belongs to one specific arm. \
             Got:\n{got}\nInput was:\n{input}"
        );
    }
}

/// A body already containing ` | ` would make the merged output
/// ambiguous (`A | B -> X | Y` mis-reads as a 4-way pattern), so
/// the pass bails.
#[test]
fn p5_2_does_not_merge_when_body_contains_or_separator() {
    let input = "  Constr<0> -> X | Y\n  Constr<1> -> X | Y\n";
    let got = merge_when_arms_with_or_pattern(input);
    assert_eq!(
        got, input,
        "bodies containing ` | ` (an already-Or'd pattern or value) \
         must NOT merge; got:\n{got}"
    );
}

/// A body ending in `->` is a lambda-arrow continuation (or a
/// function-type fragment); `CONTINUATION_SUFFIXES` rejects it.
#[test]
fn p5_2_does_not_merge_bodies_ending_with_arrow() {
    let input = "  Constr<0> -> fn(x) ->\n    x + 1\n  Constr<1> -> fn(x) ->\n    x + 1\n";
    let got = merge_when_arms_with_or_pattern(input);
    assert_eq!(
        got, input,
        "body ending with ` -> ` indicates lambda continuation; must \
         NOT merge. Got:\n{got}"
    );
}

/// `expect!(<expr>)` → `expect (<expr>)`, the valid surface syntax
/// `expect <parenthesized expr>` statement form.
#[test]
fn p1_1_ext_rewrites_expect_bang_call_form_to_statement_form() {
    let input = "        expect!(x_116(c1, e1))\n";
    let got = rewrite_expect_bang_calls(input);
    assert_eq!(got, "        expect (x_116(c1, e1))\n", "got:\n{got}");
}

/// Field access on the synthetic helper (`expect!.fst`) is left
/// alone: `expect.fst` is keyword.field, which the surface rejects.
#[test]
fn p1_1_ext_leaves_expect_bang_field_access_alone() {
    let input = "        _ -> expect!.fst\n";
    let got = rewrite_expect_bang_calls(input);
    assert_eq!(
        got, input,
        "expect!.fst (field access) must survive untouched; got:\n{got}"
    );
}

/// Multi-line `expect!( … )` also rewrites: `expect!(` opens the
/// call regardless of how the body wraps, and the resulting
/// `expect (` is valid because the `(` closes on a later line.
#[test]
fn p1_1_ext_rewrites_multiline_expect_bang_call() {
    let input = "        expect!(\n          long(\n            x\n          )\n        )\n";
    let got = rewrite_expect_bang_calls(input);
    assert!(
        got.starts_with("        expect (\n"),
        "multi-line call form should rewrite the opening; got:\n{got}"
    );
    assert!(
        !got.contains("expect!("),
        "no `expect!(` should remain: {got}"
    );
}

/// The synth helper can carry multiple args: rewriting
/// `expect!(cond, body, then_fn)` would give `expect <tuple>`,
/// and `expect` wants Bool, so multi-arg outer calls are left
/// untouched.
#[test]
fn p1_1_ext_leaves_multi_arg_expect_bang_alone() {
    let input = "        expect!(h2 == 0, Constr<0>(j2, k2), fn(x, y) { x })\n";
    let got = rewrite_expect_bang_calls(input);
    assert_eq!(
        got, input,
        "outer `expect!(cond, body, ...)` with top-level commas must \
         NOT rewrite — would produce semantically wrong `expect \
         <tuple>`. Got:\n{got}"
    );
}

/// `expect!(` inside a `@"..."` trace/fail
/// message is pinned text, not code.
#[test]
fn p1_1_ext_does_not_clobber_expect_bang_inside_string_literal() {
    let input = "      trace @\"expect!(foo)\" {\n        body\n      }\n";
    let got = rewrite_expect_bang_calls(input);
    assert_eq!(
        got, input,
        "expect!( inside `@\"...\"` literal must be preserved verbatim. \
         Got:\n{got}"
    );
}

/// A single-arg call with inner-call commas still rewrites:
/// the inner args sit below the top paren depth, so they
/// aren't top-level commas.
#[test]
fn p1_1_ext_inner_call_commas_do_not_block_rewrite() {
    let input = "        expect!(x_116(c1, e1))\n";
    let got = rewrite_expect_bang_calls(input);
    assert_eq!(
        got, "        expect (x_116(c1, e1))\n",
        "inner-call commas are at depth>1 and must not block the \
         outer single-arg rewrite. Got:\n{got}"
    );
}
