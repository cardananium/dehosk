use crate::decompile::naming::render_improve_variable_names;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

// Every render-prep pass, one module each, alphabetically. This is the
// chain's table of contents — `prepare_for_render` below runs them in a
// deliberate ORDER, which the list here does not and should not encode.
pub(crate) mod alpha_uniquify;
mod beta_reduce_lambda_apply;
mod bind_cardano_sum_when_payload;
mod bind_list_cons_head_tail;
mod bool_witness;
mod cardano_type_env;
mod church_bool_in_list_fold;
mod church_pair_collapse;
mod clarify_rec_self_value_use;
mod clarify_recfn_tail_return;
mod collapse_bool_identity_when;
mod collapse_dead_fail_chain;
mod collapse_empty_when;
mod collapse_identity_option_when;
mod collapse_identity_self_receiver;
mod collapse_over_applied_fail;
mod collapse_script_context_when;
mod collapse_trace_fail_let;
mod complete_church_nil_to_empty_list;
mod const_fold_church_bytestring;
mod copy_propagate_var_aliases;
mod cse_alpha_equivalent_lambda_helpers;
mod cse_church_cons_helpers;
mod cse_church_list_map_helpers;
mod cse_inline_y_comb;
mod cse_y_comb_consts;
pub(crate) mod ctx;
mod curry_split_partial_helpers;
mod decode_church_list_fold_partial;
mod decode_church_pair_application;
mod decode_church_to_native;
mod decode_safe_pair_pack;
mod drop_dead_fail_labels;
mod drop_dead_pure_lets;
mod drop_unreferenced_helper_fns;
mod eta_reduce_lambda_forwarder;
mod eta_reduce_pair_aliases;
mod expect_field_access;
mod expect_three_arg_conditional;
mod expect_when_bool;
mod extract_repeated_subexpr;
mod extractor_prefix;
mod field_kind_inference;
mod fix_option_false_to_none;
mod flag_orphan_fix;
mod flatten_recfn_unused_self;
mod fold_arith_identity;
mod fold_const_recfn_alias;
mod fold_data_eq_roundtrip;
mod fold_force_on_lambda_var;
mod fold_identity_pair_map;
mod fold_if_to_logical;
mod fold_un_data_scalar_const;
mod fold_when_option_to_is_some;
mod hoist_church_bool_selectors;
mod hoist_church_pair_pack;
mod hoist_entry_param_chain_calls;
mod hoist_pure_multi_arg_calls;
mod inline_always_fail_helpers;
mod inline_constructor_helpers;
mod inline_cps_identity_helpers;
mod inline_expect_subject;
mod inline_identity_helper;
mod inline_identity_param;
mod inline_pack_call_use_sites;
mod inline_pair_identity_arg;
mod inline_partial_binop;
mod inline_pattern_field_access;
mod interproc_provenance;
mod let_disambiguation;
mod lift_let_through_expect;
mod lift_list_fold_to_when;
mod list_element_provenance;
mod lower_constr_field_sugar;
mod name_cardano_sum_arms;
mod name_cardano_sum_values;
mod name_context_field_peel;
mod normalize_church_false_arm_to_native;
mod normalize_tuple_field_ordinals;
mod pass_order;
mod pattern_dedup;
pub(crate) mod prelude_downgrade;
mod profile;
mod purity;
mod rebind_pattern_field_slices;
mod recfn_self_ref_probe;
mod recover_church_booleans;
mod recover_church_list_literal;
mod recover_constr_cons_spread;
mod recover_if_from_bool_option_when;
mod recover_inverse_cip_nil_as_true;
mod recover_inverted_church_or;
mod recover_ordering_comparator;
mod recover_recursive_list_builder;
mod recover_scott_list_builder;
mod reduce_applied_church_pair_pack;
mod relabel_bool_none_to_false;
mod relabel_option_consumer_args;
mod relabel_option_producer_leaves;
mod relabel_stub_consumer_args;
pub(crate) mod relabel_stub_producer_leaves;
mod rename_church_list_helper_binders;
mod rename_church_n_pack_helpers;
mod rename_hygiene;
mod rename_let_to_cardano_field;
mod rename_module_shadowing_let;
mod rename_semantic_helpers;
mod rename_synthetic_field_let_binders;
mod rename_tx_info_binders;
mod rename_unused_lambda_params;
mod replace_inline_pack_with_pack_n;
mod resolve_pack_ordinal_projection;
mod resolve_scott_eliminator;
mod resolve_tx_info_field_indices;
mod rewrite_native_list_map;
mod saturate_dead_param_knot;
mod schema_param_provenance;
pub(crate) mod scope_recurse;
mod slice_chain;
mod split_over_applied_helper_calls;
mod strip_all_traces;
mod strip_force_under_member_access;
mod strip_plutustx_trace_pairs;
mod strip_stray_thunk_wrappers;
mod strip_void_apply_on_constr;
mod strip_void_apply_on_noncallable_result;
pub(crate) mod stub_adt;
mod underscore_lambda;
mod undo_if_on_function_condition;
mod undo_pair_when_on_lambda_subject;
mod unfold_y_comb_apply;
mod unfold_y_comb_helper_apply;
mod unfold_y_comb_through_let_pair_when;
mod unify_constructor_arity;
mod unname_discarded_check;

/// `when` subjects the context schema types as a Cardano SUM, measured
/// on a prepared tree.
///
/// `merge_isomorphic_stub_adts` keeps these classes out of the pool. The
/// ABI already names their constructors, and a stub identity can only
/// take that away: the merge pools such a class with unrelated
/// same-tag-set classes, `unify_constructor_pattern_arity` then pads its
/// arms to the pool's widest, and the ABI arity check (rightly) refuses
/// an arm padded past what the schema declares. That is what left a V3
/// `when script_info is { … }` rendering `Unknown_S_6_1(_, _, _)`
/// instead of `Spending(output_reference, datum)`.
///
/// Returns raw `VarId`s; the merge canonicalises them through the same
/// alias analysis that keys the classes, since a subject reached by an
/// alias hop (`let y = x; when y is …`) is filed under `x`.
///
/// Identifying these by HINT instead does not work: by the time a
/// prepared tree exists the naming pass has already replaced the stub
/// hint on exactly these arms with the Cardano one (`"script_info"`), so
/// the stub hint the merge groups by is no longer there to match.
pub(crate) fn cardano_sum_scrutinees(
    prepared: &crate::pseudo::ast::PseudoExpr,
    ctx: &RenderCtx,
) -> std::collections::HashSet<crate::pseudo::var_id::VarId> {
    use crate::pseudo::ast::PseudoExpr;
    use crate::pseudo::fold::ExprVisitor;

    let version = ctx.version_or_v2();
    // The same env the naming pass consults, built the same way.
    let mut env = cardano_type_env::build_cardano_type_env(prepared, ctx);
    env.fill_gaps(name_context_field_peel::infer_context_types(prepared, ctx));

    struct Collect<'a> {
        env: &'a cardano_type_env::CardanoTypeEnv,
        version: crate::decompile::ScriptVersion,
        found: std::collections::HashSet<crate::pseudo::var_id::VarId>,
    }
    impl ExprVisitor for Collect<'_> {
        fn visit_when(
            &mut self,
            subject: &PseudoExpr,
            _subject_name: Option<&crate::pseudo::ast::Binder>,
            _clauses: &[crate::pseudo::ast::WhenClause],
        ) {
            if let PseudoExpr::Var { id: Some(vid), .. } = subject
                && name_cardano_sum_arms::when_subject_cardano_sum(subject, self.version, self.env)
                    .is_some()
            {
                self.found.insert(*vid);
            }
        }
    }
    let mut c = Collect {
        env: &env,
        version,
        found: std::collections::HashSet::new(),
    };
    c.walk(prepared);
    c.found
}
pub(crate) use drop_dead_pure_lets::drop_dead_pure_lets_unchecked;

use self::church_pair_collapse::collapse_church_pair_eliminator_ast;
pub(crate) use self::ctx::RenderCtx;
pub(crate) use self::decode_church_to_native::ChurchLetComments;
use self::drop_dead_fail_labels::drop_dead_fail_labels;
use self::expect_field_access::rewrite_expect_field_access;
use self::expect_three_arg_conditional::rewrite_expect_three_arg_conditional;
use self::expect_when_bool::rewrite_expect_when_bool;
#[cfg(test)]
pub(crate) use self::extractor_prefix::debug_prefix_bare_extractor_lets_with_field_name;
use self::extractor_prefix::prefix_bare_extractor_lets_with_field_name;
use self::inline_expect_subject::inline_expect_subjects;
pub(crate) use self::let_disambiguation::disambiguate_shadowed_pattern_binders;
#[cfg(test)]
pub(crate) use self::let_disambiguation::{
    debug_disambiguate_shadowed_lets, debug_expr_contains_var_name,
};
use self::let_disambiguation::{disambiguate_shadowed_lets, pattern_binds_name};
use self::lift_let_through_expect::lift_let_through_expect;
#[cfg(test)]
pub(crate) use self::pattern_dedup::debug_deduplicate_constr_pattern_binders;
use self::pattern_dedup::deduplicate_constr_pattern_binders;
use self::slice_chain::inline_slice_chain_aliases;
use self::strip_stray_thunk_wrappers::strip_stray_thunk_wrappers;
#[cfg(test)]
pub(crate) use self::underscore_lambda::debug_repair_underscore_lambda_params_with_dangling_uses;
use self::underscore_lambda::repair_underscore_lambda_params_with_dangling_uses;

/// Prepare `expr` for rendering. The overwhelming majority of callers
/// want only the tree; the pretty-printer needs the church-decode notes
/// too, and takes [`prepare_for_render_with_notes`].
pub(crate) fn prepare_for_render(expr: &PseudoExpr, ctx: &RenderCtx) -> PseudoExpr {
    prepare_for_render_with_notes(expr, ctx).expr
}

/// What one `prepare_for_render` produced: the tree, the church-decode's
/// per-binding tags, and what each of its ~140 steps cost.
pub(crate) struct Prepared {
    /// The prepared tree.
    pub(crate) expr: PseudoExpr,
    /// The church-decode's `VarId → tag` notes, valid only for `expr` —
    /// every prepare re-mints binder ids.
    pub(crate) church_notes: ChurchLetComments,
    /// Per-step timings, for `--emit prep-profile`.
    pub(crate) profile: profile::PrepProfile,
}

/// [`prepare_for_render`] plus the church-decode's per-binding tags,
/// which the printer renders as trailing `// <tag>` comments. They come
/// back BESIDE the prepared tree because their `VarId` keys only match
/// that tree — this function re-mints binder ids on every call.
pub(crate) fn prepare_for_render_with_notes(expr: &PseudoExpr, ctx: &RenderCtx) -> Prepared {
    let mut church_notes = ChurchLetComments::default();
    let mut prep = profile::PrepRun::new();
    // Church-bool polarity was detected once on the seed in the pipeline —
    // simplify has folded the producer signals, so it cannot be
    // re-detected here; the inverse-CIP recoverers below read it off
    // `ctx`.
    //
    // Alpha-uniquify duplicate binder VarIds arriving in the pipeline
    // output before any id-keyed prepare pass can conflate them. Pure
    // id surgery — display names untouched.
    let ids_deduped = prep.step("uniquify_duplicate_binders", || {
        alpha_uniquify::uniquify_duplicate_binders(expr.clone())
    });
    let renamed = prep.step("render_improve_variable_names", || {
        render_improve_variable_names(ids_deduped)
    });
    let dedup = prep.step("deduplicate_constr_pattern_binders", || {
        deduplicate_constr_pattern_binders(renamed)
    });
    let prefixed = prep.step("prefix_bare_extractor_lets_with_field_name", || {
        prefix_bare_extractor_lets_with_field_name(dedup)
    });
    let inlined = prep.step("inline_slice_chain_aliases", || {
        inline_slice_chain_aliases(prefixed)
    });
    let lambda_repaired = prep.step("repair_underscore_lambda_params_with_dangling_uses", || {
        repair_underscore_lambda_params_with_dangling_uses(inlined)
    });
    let disambiguated = prep.step("disambiguate_shadowed_lets", || {
        disambiguate_shadowed_lets(&lambda_repaired)
    });
    // `disambiguate_shadowed_lets` only renames let/lambda/recfn
    // binders; `when`-pattern binders relabeled to literal `head`/`tail`
    // by `display/rewrite` can still collide across nested cons clauses,
    // making e.g. a parallel two-list `rec_fn(v1_tail, v2_tail)` render
    // as the ambiguous `rec_fn(tail, tail)`. Suffix the inner colliding
    // pattern binders (rewiring uses by VarId).
    let disambiguated = prep.step("disambiguate_shadowed_pattern_binders", || {
        disambiguate_shadowed_pattern_binders(disambiguated)
    });
    // Collapse `let X = fail @"L<line>;<col>"` chains whose binders
    // are never referenced — these are dead source-map labels that
    // shadow the entire single-letter alphabet at validator entry.
    let labels_dropped = prep.step("drop_dead_fail_labels", || {
        drop_dead_fail_labels(disambiguated)
    });
    // Strip stray `Apply(non-callable, [])` wrappers — the trailing
    // `}()` after a `when`/`if`/`trace`/`let` block from
    // force/delay cancellation that didn't collapse upstream.
    let zero_apply_stripped = prep.step("strip_stray_thunk_wrappers", || {
        strip_stray_thunk_wrappers(labels_dropped)
    });
    // Inline `let X = e; expect P = X; body` →
    // `expect P = e; body` when X is consumed exactly as the
    // expect-when's subject. Reduces `_result` rebinding noise.
    let inlined_subjects = prep.step("inline_expect_subjects", || {
        inline_expect_subjects(zero_apply_stripped)
    });
    // Detect the Bool-shaped When inside an
    // `Apply(expect!, [When, tail])` chain and rewrite to a
    // pattern-expect When `{P -> tail, _ -> fail}` that
    // `extract_expect_pattern` recognises and renders as legal
    // `expect P = X; tail`.
    let expect_when_bool_rewritten = prep.step("rewrite_expect_when_bool", || {
        rewrite_expect_when_bool(inlined_subjects)
    });
    // Lift `let X = v` out of `expect !(let X = v in body)` chains so
    // the rendered output reads `let X = v; expect !body; …`. The bare
    // `expect !let X = v` form is invalid surface syntax.
    let let_lifted = prep.step("lift_let_through_expect", || {
        lift_let_through_expect(expect_when_bool_rewritten)
    });
    // Detect church-Bool eliminator shape — `args[2]` is NON-String
    // AND `args[0]` is structurally Bool (BinOp comparison/logical,
    // `Bool` literal, or `Not(structurally_bool)` excluding `Not(Let)`)
    // rewrite to `If { c, t, e }`. The 3-arg fail-message sugar
    // form is preserved (args[2] is String).
    //
    // Placement: AFTER the let-lift pass, which first lifts any
    // `Let` out of `Not(Let ...)` in args[0]; this pass then sees
    // `Not(body)` and can fire when body is structurally Bool.
    let three_arg_rewritten = prep.step("rewrite_expect_three_arg_conditional", || {
        rewrite_expect_three_arg_conditional(let_lifted)
    });
    // Rewrite `FieldAccess { record: Var{name:"expect!", id:None}, .. }`
    // to `fail`. The simplifier's synthetic assertion sentinel leaks
    // into expression position with a `.fst|.snd` selector; the bare
    // helper has no surface syntax, so collapse to `fail` (its sole
    // UPLC semantic).
    let expect_field_rewritten = prep.step("rewrite_expect_field_access", || {
        rewrite_expect_field_access(three_arg_rewritten)
    });
    // Collapse `Force(Lambda(x, x(a, b))).fst|snd` church-pair eliminator
    // shape to `a` / `b` with a purity guard on the discarded side.
    let church_pair_collapsed = prep.step("collapse_church_pair_eliminator_ast", || {
        collapse_church_pair_eliminator_ast(expect_field_rewritten)
    });
    // Undo the `when <Lambda/RecFn> is { Pair(a, b) -> body }` collapse
    // the simplifier produces for Y-combinator / Church-encoded function
    // subjects: the When shape is meaningless on a function, so revert to
    // the Apply form `subject(λa b. body)`.
    let church_pair_collapsed = prep.step("undo_pair_when_on_lambda_subject", || {
        undo_pair_when_on_lambda_subject::undo_pair_when_on_lambda_subject(church_pair_collapsed)
    });
    // Same shape, indirected through a `let`: the subject is a
    // `Var` whose binding is a canonical Y-combinator literal.
    // Rewrites `when Var is { Pair(a, b) → body }` to the unfolded
    // fixpoint `rec fn a(b) { body }`, the Scott-data-as-fn
    // misuse that `undo_pair_when_on_lambda_subject` handles only
    // for INLINE subjects.
    let church_pair_collapsed = prep.step("unfold_y_comb_through_let_pair_when", || {
        unfold_y_comb_through_let_pair_when::unfold_y_comb_through_let_pair_when(
            church_pair_collapsed,
        )
    });
    // Collapse `when X is { True -> True; False -> False; _ -> fail }`
    // (Bool-identity) to just `X`.
    let church_pair_collapsed = prep.step("collapse_bool_identity_when", || {
        collapse_bool_identity_when::collapse_bool_identity_when(church_pair_collapsed)
    });
    // Rename synthetic `field_N(_M)?` let binders to `tx_info` /
    // `redeemer` / `script_info` when the let value is a known V3
    // ScriptContext field access.
    let church_pair_collapsed = prep.step("rename_synthetic_field_let_binders", || {
        rename_synthetic_field_let_binders::rename_synthetic_field_let_binders(
            church_pair_collapsed,
        )
    });
    // Fold `Force(...Force(Var(c)))` to `Var(c)` when c is bound to
    // a Lambda/RecFn. Done BEFORE `inline_identity_helper` so the
    // identity-call inliner sees the plain `c(arg)` shape rather
    // than `c()(arg)` (which it doesn't recognise).
    let church_pair_collapsed = prep.step("fold_force_on_lambda_var", || {
        fold_force_on_lambda_var::fold_force_on_lambda_var(church_pair_collapsed)
    });
    // Strip redundant `Force(Var(p))` / `Apply{Var(p), []}` wrapper under
    // FieldAccess / IndexAccess, where `p` is a pattern binder (When clauses),
    // a Lambda param, or a RecFn param. Handles church-pair access through an
    // alias (`payload().snd`) that the Let-bound-only
    // `fold_force_on_lambda_var` cannot see.
    let church_pair_collapsed = prep.step("strip_force_under_member_access", || {
        strip_force_under_member_access::strip_force_under_member_access(church_pair_collapsed)
    });
    // Inline + drop identity helpers (`fn c(x) { x }`) — every
    // `c(arg)` callsite becomes `arg` and the let disappears. PlutusTx
    // sometimes emits these as `force`/`delay` residue that survived
    // simplification.
    let identity_helpers_inlined = prep.step("inline_identity_helpers", || {
        inline_identity_helper::inline_identity_helpers(church_pair_collapsed)
    });
    // Inline fully-applied CPS-identity helpers
    // `fn h(args..., k) { k(args...) }` at each call site where
    // args.len() == params.len() (no partial app). Partial
    // applications stay (church-pair-pack idiom).
    let identity_helpers_inlined = prep.step("inline_cps_identity_helpers", || {
        inline_cps_identity_helpers::inline_cps_identity_helpers(identity_helpers_inlined)
    });
    // Strips the `trace("entering X", fn(_) { trace("exiting X", body,
    // _) }, _)` instrumentation that PlutusTx-compiled scripts wrap
    // around every call site. Off by default: those traces name the
    // original Haskell functions, so hiding them costs the reader more
    // than it saves.
    let plutustx_trace_stripped = if ctx.strip_plutustx_traces() {
        strip_plutustx_trace_pairs::strip_plutustx_trace_pairs(identity_helpers_inlined)
    } else {
        identity_helpers_inlined
    };
    // Strip ALL trace expressions, including user-facing surface
    // `trace @"msg"`. Default no-op; semantically log-dropping.
    let all_traces_stripped = prep.step("strip_all_traces", || {
        strip_all_traces::strip_all_traces(plutustx_trace_stripped, ctx)
    });
    // Collapse `let __N = fail in fail` chains that PlutusTx emits at
    // every `error "msg"` source site: the binder is never referenced
    // and the trailing `fail` is dead. Runs before the unused-param
    // rename so that pass sees a smaller tree.
    let fail_chains_collapsed = prep.step("collapse_dead_fail_chain", || {
        collapse_dead_fail_chain::collapse_dead_fail_chain(all_traces_stripped)
    });
    // Rename lambda params never referenced in their body to `_`.
    // PlutusTx-compiled scripts carry hundreds of `fn(__N) { … }`
    // lambdas whose param is a `traceIfFalse` unit-thunk arg.
    let unused_params_renamed = prep.step("rename_unused_lambda_params", || {
        rename_unused_lambda_params::rename_unused_lambda_params(fail_chains_collapsed)
    });
    // Backstop for orphan `Var("fix")` references — see
    // `flag_orphan_fix.rs` for the underlying pass-strip bug.
    let fix_flagged = prep.step("flag_orphan_fix", || {
        flag_orphan_fix::flag_orphan_fix(unused_params_renamed)
    });
    // Inside an emitted `validator decompiled { … }` block, collapse
    // the redundant `when script_context is { K -> body }` wrapper
    // (ScriptContext is single-variant — the match is a tautology).
    // Gated tightly: only fires when the enclosing block is the
    // wrap-time `decompiled` sentinel AND the when has exactly one
    // empty-fields clause AND no guard.
    let sc_when_collapsed = prep.step("collapse_script_context_when", || {
        collapse_script_context_when::collapse_script_context_when(fix_flagged)
    });
    // Dedupe structurally-identical Y-comb defining Lambdas at
    // top-level into one canonical binding + redirected refs.
    let y_comb_deduped = prep.step("cse_y_comb_consts", || {
        cse_y_comb_consts::cse_y_comb_consts(sc_when_collapsed)
    });
    // Recover Church-encoded list literals (nested `cons(head, cons(head,
    // ... nil))` chains) as `PseudoExpr::List`. Render-only inverse of the
    // compiler lowering: the value stays a Church-encoded function,
    // but the reader sees `[a, b, c, ...]`.
    //
    // Runs AFTER cse_y_comb_consts and BEFORE unfold_y_comb_applications —
    // the chain only takes its final Apply-call-site shape once the passes
    // that synthesize and rename those sites have run.
    let y_comb_deduped = prep.step("recover_church_list_literals", || {
        recover_church_list_literal::recover_church_list_literals(y_comb_deduped)
    });
    // Unfold Y-combinator INSTANTIATIONS: collapse
    //   `(fn(v) { rec fn self(x) { v(self, x) } })(driver)`
    // into `rec fn self(x) { driver(self, x) }`, dropping two layers of
    // wrapping where the Y-comb construction is inlined at each use site.
    // Only fires when `driver` is a pure value.
    let y_comb_unfolded = prep.step("unfold_y_comb_applications", || {
        unfold_y_comb_apply::unfold_y_comb_applications(y_comb_deduped)
    });
    // Same unfold, keyed on a HOISTED half-Z helper: the half-Z lambda
    // is named (`fn rec_fn_2(v) { rec fn s(x) { v(s, x) } }`) and
    // instantiated per recursion (`rec_fn_2(fn(self, arg) { … })`). The
    // inline pass above can't see through the `Var(rec_fn_2)` head; this
    // one resolves it by VarId. Once every call site unfolds, the dead
    // helper Let is swept by the `drop_dead_pure_lets` re-runs below.
    let y_comb_unfolded = prep.step("unfold_y_comb_helper_applications", || {
        unfold_y_comb_helper_apply::unfold_y_comb_helper_applications(y_comb_unfolded)
    });
    // Witness-gated producer-side Option relabel: a fn whose result is
    // matched downstream with native Some/None gets its raw Option-shaped
    // return leaves named (incl. the CSE-alias None hop). Runs after the
    // half-Z unfold so the producer bodies are direct rec fns.
    let y_comb_unfolded = prep.step("relabel_option_producer_leaves", || {
        relabel_option_producer_leaves::relabel_option_producer_leaves(y_comb_unfolded)
    });
    // The argument-position dual of `relabel_option_producer_leaves`: a fn
    // whose PARAMETER is matched with native Some/None (a nullary None
    // witness proving Option over Result) gets its CALL-SITE arguments at
    // that position named — `Ok(x)`/raw `Constr<0>(x)` → `Some(x)`, nullary
    // raw `Constr<1>` → `None`. Same witness gate, and the same dependence
    // on the half-Z unfold having exposed direct fn bodies.
    let y_comb_unfolded = prep.step("relabel_option_consumer_args", || {
        relabel_option_consumer_args::relabel_option_consumer_args(y_comb_unfolded)
    });
    // Consumer-witness relabel of a re-constructed extraction payload back
    // to its native ctor: a raw `Constr{Unknown, tag, [Var(b)]}` where `b`
    // was extracted via `expect K(b)` (Ok/Error/Some) relabels to `K(b)`
    // ONLY when it PROVABLY flows to a call argument (directly or as a Pair
    // component) whose consuming fn destructures that position with K's
    // SAME ADT family — the extraction alone does not prove the label.
    // Display-only (same tag/arity).
    let y_comb_unfolded = prep.step("relabel_stub_consumer_args", || {
        relabel_stub_consumer_args::relabel_stub_consumer_args(y_comb_unfolded)
    });
    // Curry-split church-pair-pack helpers whose call sites all use
    // the SAME partial arity K < full param count, so the rendered
    // signature matches the calls — a 4-param helper called with 2
    // args otherwise looks like a syntax error.
    let curry_split = prep.step("curry_split_partial_helpers", || {
        curry_split_partial_helpers::curry_split_partial_helpers(y_comb_unfolded)
    });
    // CSE structurally-identical Church-Cons helper definitions
    // (post-curry-split shape `fn(a, b) { fn(_, k) { k(a, b) } }`).
    // Renames the canonical one to `church_cons` and redirects all
    // references.
    let curry_split = prep.step("cse_church_cons_helpers", || {
        cse_church_cons_helpers::cse_church_cons_helpers(curry_split)
    });
    // Rename `helper_N` Church-N-pack constructors (arity ≥ 3) to
    // `pack_N` where N is the ARITY, not the helper ordinal:
    // `helper_20` of arity 10 becomes `pack_10`.
    let curry_split = prep.step("rename_church_n_pack_helpers", || {
        rename_church_n_pack_helpers::rename_church_n_pack_helpers(curry_split)
    });
    // Rewrite `True`/`False` literals into explicit Church-encoded
    // Lambdas in a `Nil`/`Cons` match arm whose sibling arm returns
    // a Church-pair-pack value: the two arms share a UPLC encoding
    // but have inconsistent types. Runs AFTER curry_split, so
    // the Cons-arm helper application is already function-valued.
    let church_bool_rewritten = prep.step("rewrite_church_bool_in_list_fold", || {
        church_bool_in_list_fold::rewrite_church_bool_in_list_fold(curry_split)
    });
    // Inline `subject.fields.head` / `subject.fields[N]` to the
    // corresponding When-pattern binder when the access shadows
    // an existing pattern binding: `Unknown_S_10_0(tx_info,
    // purpose) -> let head = script_context.fields.head` becomes
    // `let head = tx_info`, which a later pass drops as a dead
    // alias when the two differ only by name.
    let field_access_inlined = prep.step("inline_pattern_field_access", || {
        inline_pattern_field_access::inline_pattern_field_access(church_bool_rewritten)
    });
    // ^ clones binder-bearing inlined values to every reference site —
    // re-uniquify the duplicates it mints.
    let field_access_inlined = prep.step("uniquify_duplicate_binders", || {
        alpha_uniquify::uniquify_duplicate_binders(field_access_inlined)
    });
    // `inline_pattern_field_access` grows each stub-constructor pattern
    // independently to cover its clause body's `subject.fields[N]`
    // reads, so one constructor can end up destructured at several
    // arities. Pad every site of a given `(type_hint, tag)` up to the
    // max so the constructor has one uniform arity (the surface requires it);
    // the declaration arity is reconciled from the padded AST in
    // `stub_adt::reconcile_declared_arities`.
    let field_access_inlined = prep.step("unify_constructor_pattern_arity", || {
        unify_constructor_arity::unify_constructor_pattern_arity(field_access_inlined)
    });
    // Rebind positional `subj.fields[k..].head` /
    // `subj.fields[k]` re-derivations, inside a clause whose Constructor
    // pattern binds `subj = Var(id)`, to the pattern binder `f_k` that already
    // names that raw field — dropping the now-dead slice `let`s. A pure
    // alias-collapse (binder is that raw field, same representation), resolving
    // the field index through let-alias offset accumulation
    // (`let w = subj.fields[j..]; w[i..].head` -> index `j + i`). Fail-closed on
    // any unresolved offset. Runs AFTER `unify_constructor_arity` mints +
    // arity-unifies the `field_N` binders this pass targets.
    let field_access_inlined = prep.step("rebind_pattern_field_slices", || {
        rebind_pattern_field_slices::rebind_pattern_field_slices(field_access_inlined)
    });
    // Strip `(Void)` from `Apply { function: Var(zero_arg_constr),
    // args: [Unit] }` — the force-thunked-constant idiom. After this
    // pass, references to a zero-arity Constr-bound const read as
    // direct value access (`c1` not `c1(Void)`).
    let void_apply_stripped = prep.step("strip_void_apply_on_constr", || {
        strip_void_apply_on_constr::strip_void_apply_on_constr(field_access_inlined)
    });
    // Hoist repeated Church-encoded Bool selector Lambdas (`fn(t, _) { t }`
    // / `fn(_, f) { f }`) to top-level named consts (`church_true` /
    // `church_false`). Only fires when ≥ 2 occurrences exist, since
    // a const declaration for a single use is just noise.
    let selectors_hoisted = prep.step("hoist_church_bool_selectors", || {
        hoist_church_bool_selectors::hoist_church_bool_selectors(void_apply_stripped)
    });
    // Reduce Church-pair-packs that are built and immediately consumed
    // — `(fn(x) { x(a, b) })(consumer)` → `consumer(a, b)`. Runs BEFORE
    // `hoist_church_pair_pack`: once lifted, the round-trip becomes
    // `pair_pack(a, b)(consumer)`, whose callee is a helper call that
    // `beta_reduce` can no longer simplify.
    let round_trips_reduced = prep.step("reduce_applied_church_pair_pack", || {
        reduce_applied_church_pair_pack::reduce_applied_church_pair_pack(selectors_hoisted)
    });
    // Hoist inline 2-arg Church-pair-pack constructors `fn(x) { x(a, b) }`
    // to a named helper `pair_pack(a, b)` when ≥ 2 occurrences exist —
    // the Church-encoded UPLC equivalent of `Pair(a, b)` construction.
    let pair_packs_hoisted = prep.step("hoist_church_pair_pack", || {
        hoist_church_pair_pack::hoist_church_pair_pack(round_trips_reduced)
    });
    // Rename `when tx_info is { Unknown_S_X_Y(field_0, items, ...) }`
    // pattern binders to the canonical V1/V2/V3 TxInfo field
    // names (inputs, outputs, fee, mint, …). Arity disambiguates
    // version (10 = V1, 12 = V2, 16 = V3).
    let tx_info_renamed = prep.step("rename_tx_info_binders", || {
        rename_tx_info_binders::rename_tx_info_binders(pair_packs_hoisted)
    });
    // Relabel positional `tx_info.fields[N]` accessors to the schema-named
    // TxInfo field (`tx_info.inputs`, …) — the let-form companion to
    // `rename_tx_info_binders` (which handles the `when tx_info is { … }`
    // destructure form). Version-gated via the `RenderCtx`; a no-op when no
    // version is active (tests / version-less debug bundles).
    let tx_info_renamed = prep.step("resolve_tx_info_field_indices", || {
        resolve_tx_info_field_indices::resolve_tx_info_field_indices(tx_info_renamed, ctx)
    });
    // Schema-param provenance BRIDGE: propagate a NAMED TxInfo list field's
    // ELEMENT type to a helper-fn param that is provably fed only that
    // element type at EVERY call site, renaming the param to the element's
    // Cardano name. `tx_info.certificates : List<DCert>` → a helper param
    // named `certificate`, so the `when <param> is { … }` dispatch resolves
    // to `SumTypeId::Certificate` in the following `name_cardano_sum_arms`
    // pass, which needs the subject name already in place. Fail-closed
    // (enumerable call set + per-slot Conflict join); inert otherwise.
    let tx_info_renamed = prep.step("schema_param_provenance", || {
        schema_param_provenance::schema_param_provenance(tx_info_renamed, ctx)
    });
    // Bind the ABI payload of a `when <cardano-sum> is { Constr<tag> -> … }`
    // whose arms are nullary but re-project `<subject>.fields[i]` by hand
    // (`Constr<5> -> script_info.fields[1]` ⇒ `Constr<5>(field_0, field_1) ->
    // field_1`). Runs BEFORE `name_cardano_sum_arms` so the arity-correct
    // arms become nameable. Attaches no name itself; fail-closed (bails
    // unless every arm is a nullary ctor of trusted ABI arity with no
    // out-of-range field projection).
    //
    // This call gets an empty type-env, so it reshapes only whens whose
    // subject resolves by reserved Cardano name (`script_context.script_info`
    // → ScriptInfo, …). The type-based call after the CSE (below) takes the
    // subjects that are bare binders no name shape recognizes, e.g. the
    // `let w = <…>.fields[2]` that `extract_repeated_subexpr` mints.
    let tx_info_renamed = prep.step("bind_cardano_sum_when_payload", || {
        bind_cardano_sum_when_payload::bind_cardano_sum_when_payload(
            tx_info_renamed,
            &cardano_type_env::CardanoTypeEnv::default(),
            ctx,
        )
    });
    // Type-directed naming of sum-typed `when` arms, now that the Cardano
    // subject binders are named: stamps the constructor name + renames the
    // per-constructor payload binders for any `when <subject> is { … }`
    // whose subject resolves through the context schema to a known sum
    // type (`bound_type` → IntervalBoundType ⇒ Finite/NegativeInfinity/
    // PositiveInfinity; `purpose` → Minting(policy_id)/…). The universal,
    // late counterpart to the early `cardano_context_naming` pass, which
    // misses subjects that were still `field_N` when it ran. Arity-gated
    // against the ABI schema; inert otherwise.
    let tx_info_renamed = prep.step("name_cardano_sum_arms", || {
        name_cardano_sum_arms::name_cardano_sum_arms(
            tx_info_renamed,
            &cardano_type_env::CardanoTypeEnv::default(),
            ctx,
        )
    });
    // Lift the 4-arg CPS-identity shape
    //   `List.fold(xs, nil, fn(_) { cons }, fn(x) { x })`
    // to `when xs is { [] -> nil; [_, ..] -> cons }`. The MID
    // `try_recognize_choose_list` pass requires exactly 3 args, so the
    // CPS-style 4-arg form (Plutus church-list builders) leaks through
    // to render-time. Restoring the `when` shape makes the
    // church-list rec-fn helpers readable.
    let list_fold_lifted = prep.step("lift_list_fold_to_when", || {
        lift_list_fold_to_when::lift_list_fold_to_when(tx_info_renamed)
    });
    // CSE alpha-equivalent church-list-map rec-fn helpers in the same
    // local let chain; all refs share one canonical binding.
    let helpers_cse = prep.step("cse_church_list_map_helpers", || {
        cse_church_list_map_helpers::cse_church_list_map_helpers(list_fold_lifted)
    });
    // Display-only rename: church-list-map rec-fns get readable
    // names `step(xs)` instead of synthesized `self_fn_N(v_X_Y)`.
    let helpers_renamed = prep.step("rename_church_list_helper_binders", || {
        rename_church_list_helper_binders::rename_church_list_helper_binders(helpers_cse)
    });
    // Const-fold `s5(o5([byte_literal_list]))` where:
    //   o5 :: bytes → church-list of singleton-bytestrings
    //   s5 :: church-list-of-bytestrings → concatenated bytestring
    // Replaces the whole call with the resulting `#"<hex>"` literal.
    // Strict structural match on both helper definitions; no-op on any
    // other shape. Runs BEFORE `promote_validator_entry_first` so the
    // env walker sees the helpers in their lexical scope.
    let bytestring_folded = prep.step("const_fold_church_bytestring", || {
        const_fold_church_bytestring::const_fold_church_bytestring(helpers_renamed)
    });
    // Collapse `let X = trace @"msg": pure_val; fail` → `fail @"msg"`.
    // V1 scripts emit this at every "shouldn't happen" site; the surface
    // surface form is far shorter.
    let trace_fail_collapsed = prep.step("collapse_trace_fail_let", || {
        collapse_trace_fail_let::collapse_trace_fail_let(bytestring_folded)
    });
    // Drop pure-valued let-bindings whose binder is unreferenced.
    // Particularly catches the `let List_partial_*: List<Data> =
    // snd_N[K..]` synthetic shadows that the simplifier leaves
    // around when the body re-derives the slice inline rather than
    // through the binder. Gated on the `decompiled` marker to avoid
    // cascade-dropping the entire chain on validator-less scripts.
    let dead_pure_dropped = prep.step("drop_dead_pure_lets", || {
        drop_dead_pure_lets::drop_dead_pure_lets(trace_fail_collapsed)
    });
    // Fold surviving arithmetic/boolean identities: `x + 0`/`x - 0`/`x * 1` → x,
    // `a && a` (same pure Var) → a.
    let arith_folded = prep.step("fold_arith_identity", || {
        fold_arith_identity::fold_arith_identity(dead_pure_dropped)
    });
    // Drop redundant `list_data(a) == list_data(b)` round-trips → `a == b`.
    let arith_folded = prep.step("fold_data_eq_roundtrip", || {
        fold_data_eq_roundtrip::fold_data_eq_roundtrip(arith_folded)
    });
    // Const-fold `un_b_data(#"ab")` → `#"ab"` / `un_i_data(42)` → `42` (a scalar
    // `un_*_data` unwrap applied to a matching `Data` literal — the
    // compile-time-applied/extracted-param double-unwrap).
    let arith_folded = prep.step("fold_un_data_scalar_const", || {
        fold_un_data_scalar_const::fold_un_data_scalar_const(arith_folded)
    });
    // Fold a boolean `if` with a Bool-literal branch into a logical op —
    // `if c { body } else { False }` → `c && body`, `if c { True } else { body }`
    // → `c || body` (exact short-circuit equivalences; the both-literal identity
    // cases are left to boolean_cleanup).
    let arith_folded = prep.step("fold_if_to_logical", || {
        fold_if_to_logical::fold_if_to_logical(arith_folded)
    });
    // Inline partially-applied binop builtins: `let P = Int.lt(a); … P(b) …`
    // → `… a < b …` (drops the invalid dotted `Int.lt_partial` binding).
    let arith_folded = prep.step("inline_partial_binop", || {
        inline_partial_binop::inline_partial_binop(arith_folded)
    });
    // Route inline `fn(x){x(args)}` church-pack literals through the
    // top-level `pack_N` helper when arities match.
    let inline_pack_routed = prep.step("replace_inline_pack_with_pack_n", || {
        replace_inline_pack_with_pack_n::replace_inline_pack_with_pack_n(arith_folded)
    });
    // Replace inline Y-comb literals (`fn(v) { rec fn self(x) { v(self,
    // x) } }`) with refs to top-level `y_combinator` const when one
    // exists.
    let yc_cse = prep.step("cse_inline_y_comb", || {
        cse_inline_y_comb::cse_inline_y_comb(inline_pack_routed)
    });
    // Collapse identity `when X is { Some(p) -> Some(p); None -> None }` → `X`
    // (and both-`None` → `None`) before the is_some/is_none fold.
    let yc_cse = prep.step("collapse_identity_option_when", || {
        collapse_identity_option_when::collapse_identity_option_when(yc_cse)
    });
    // Fold `when X is { Some(_) -> True; None -> False }` → `option.is_some(X)`.
    let opt_check_folded = prep.step("fold_when_option_to_is_some", || {
        fold_when_option_to_is_some::fold_when_option_to_is_some(yc_cse)
    });
    // Hoist `f(entry_param)` calls that appear ≥3 times in entry body.
    let param_chain_hoisted = prep.step("hoist_entry_param_chain_calls", || {
        hoist_entry_param_chain_calls::hoist_entry_param_chain_calls(opt_check_folded)
    });
    // ^ clones a shared representative per scope — re-uniquify BEFORE the
    // sister hoist below, whose analysis a transiently duplicated tree
    // would mislead.
    let param_chain_hoisted = prep.step("uniquify_duplicate_binders", || {
        alpha_uniquify::uniquify_duplicate_binders(param_chain_hoisted)
    });
    // Hoist multi-arg pure-arg calls appearing ≥3 times in entry body.
    let multi_arg_hoisted = prep.step("hoist_pure_multi_arg_calls", || {
        hoist_pure_multi_arg_calls::hoist_pure_multi_arg_calls(param_chain_hoisted)
    });
    // ^ same shared-representative cloning — re-uniquify.
    let multi_arg_hoisted = prep.step("uniquify_duplicate_binders", || {
        alpha_uniquify::uniquify_duplicate_binders(multi_arg_hoisted)
    });
    // Optional church→native rewrite, gated on `RenderCtx::decode_church`,
    // which the pipeline builds from
    // `DecompileOptions::decode_church_to_native`; no-op by default.
    let church_decoded = prep.step("decode_church_to_native", || {
        decode_church_to_native::decode_church_to_native(multi_arg_hoisted, ctx, &mut church_notes)
    });
    let church_decoded = prep.step("rewrite_native_list_map", || {
        rewrite_native_list_map::rewrite_native_list_map(church_decoded)
    });
    // Now that `list.map` (and friends) are emitted as `module.fn` qualifiers,
    // rename any `const`/`let` whose name shadows a stdlib module used as such a
    // qualifier in its scope (e.g. `const list` vs `list.map` → `const list_2`),
    // so the qualifier resolves to the module, not the value binding.
    let church_decoded = prep.step("rename_module_shadowing_lets", || {
        rename_module_shadowing_let::rename_module_shadowing_lets(church_decoded)
    });
    // Collapse an identity `list.map(xs, fn(e){ Pair(e.fst, e.snd) })` → `xs`.
    let church_decoded = prep.step("fold_identity_pair_map", || {
        fold_identity_pair_map::fold_identity_pair_map(church_decoded)
    });
    // Inline `pair_val.<slot>(arg)` to `arg` when the pair's `<slot>`
    // component is an identity lambda. Handles both the pre-decode
    // `pair_pack(_, fn(x){x})` form and the post-decode
    // `Pair(_, fn(x){x})` form. Default-on (no flag) — the rewrite is
    // strictly local and id-equality gated.
    let pair_identity_inlined = prep.step("inline_pair_identity_arg", || {
        inline_pair_identity_arg::inline_pair_identity_arg(church_decoded)
    });
    // Inline constructor helpers (`fn pair_pack(a, b) { Pair(a, b) }`,
    // `fn pack_N(a, b, …) { (a, b, …) }`, `fn cons(h, t) { [h, ..t] }`)
    // at every call site, dropping the helper definition when no bare
    // refs survive. Only fires on the EXACT constructor-of-params body
    // shape `decode_church_to_native` produces; inert without it.
    let ctor_inlined = prep.step("inline_constructor_helpers", || {
        inline_constructor_helpers::inline_constructor_helpers(pair_identity_inlined)
    });
    // Convert a Scott-encoded list PRODUCER's cons cells (a 2-field stub-
    // `Constr` whose 2nd field is the enclosing rec fn's self-call) into
    // native `[head, ..self(…)]` cells — opt-in, inert unless
    // `--decode-church-to-native`. The nil completion below then rewrites
    // `[] -> church_true` → `[] -> []` once the sibling cons arm provably
    // commits to a native list (all value leaves are List cells / fail).
    // ORDER IS LOAD-BEARING for that completion: it needs this pass's native
    // cons cell, must follow `cse_church_list_map_helpers` (whose recognizer
    // needs the still-bare `Var` nil arm) and `inline_constructor_helpers`
    // (before which the cons route is still `Apply(church_cons, …)`, so the
    // witness can't hold), and must precede the `drop_dead_pure_lets` re-run
    // that drops the dead `const church_true`.
    let ctor_inlined = prep.step("recover_scott_list_builder", || {
        recover_scott_list_builder::recover_scott_list_builder(ctor_inlined, ctx)
    });
    let ctor_inlined = prep.step("complete_church_nil_to_empty_list", || {
        complete_church_nil_to_empty_list::complete_church_nil_to_empty_list(ctor_inlined)
    });
    // Inline church-pack-N use-site calls: rewrite `Apply(pack_var,
    // cont_lambda, …extras)` to a Let-chain that binds each cont
    // param to the corresponding pack field, then re-applies any
    // extras. `decode_church_to_native` decodes the binding's VALUE
    // to a native `Tuple`/`Pair` but leaves use sites as
    // `pack_var(cont, …)` — invalid surface syntax, tuples aren't callable.
    let ctor_inlined = prep.step("inline_pack_call_use_sites", || {
        inline_pack_call_use_sites::inline_pack_call_use_sites(ctor_inlined)
    });
    // Resolve `<pack>.<n>(args)` → `<element>(args)` where `<pack>` is a
    // let-bound Tuple literal of pure elements (a decoded church-pack-N).
    // Sound: a pure tuple projection, NOT a Scott eliminator. Run before the
    // ordinal normalization so the selector is still the raw numeric index —
    // the pass also accepts the ordinal form, so order is not load-bearing.
    let ctor_inlined = prep.step("resolve_pack_ordinal_projection", || {
        resolve_pack_ordinal_projection::resolve_pack_ordinal_projection(ctor_inlined)
    });
    // Re-run dead-let elimination: resolving the pack projections above turns
    // the pack tuple lets (and any element bound only inside them) into dead
    // pure bindings.
    let ctor_inlined = prep.step("drop_dead_pure_lets", || {
        drop_dead_pure_lets::drop_dead_pure_lets(ctor_inlined)
    });
    // Rewrite numeric tuple selectors (`.0`/`.7`) to ordinals
    // (`.1st`/`.8th`) — invalid bare-numeric access from all sources
    // (pack-call inlining + the initial tuple-unpack decode).
    let ctor_inlined = prep.step("normalize_tuple_field_ordinals", || {
        normalize_tuple_field_ordinals::normalize_tuple_field_ordinals(ctor_inlined)
    });
    // Eta-reduce `Pair(fn(a, b) { p.fst(a, b) }, p.snd)` → `p`. Fires
    // on residue produced by `inline_pack_call_use_sites`'s
    // sentinel-call decoder when an outer construction immediately
    // rewraps the same pair via its own projections.
    let ctor_inlined = prep.step("eta_reduce_pair_aliases", || {
        eta_reduce_pair_aliases::eta_reduce_pair_aliases(ctor_inlined)
    });
    // Decode church-list fold-partial: `[H1, …, HN, ..nil](k)` →
    // `fn(n) { let k_alias = k; k_alias(H1, k_alias(H2, …, k_alias(HN,
    // n))) }`. Eliminates the "list applied to one arg" residue that
    // `inline_pack_call_use_sites` left in some Tuple-N
    // lambda-continuation sites where the continuation returns a
    // church-list value that's then folded with a partial cons-step.
    let ctor_inlined = prep.step("decode_church_list_fold_partial", || {
        decode_church_list_fold_partial::decode_church_list_fold_partial(ctor_inlined)
    });
    // CSE alpha-equivalent let-bound Lambda helpers within the same
    // Let-chain. PlutusTx-compiled V1 scripts emit clusters of
    // structurally identical inner helpers — GHC's inlining plus the
    // decompiler's naming disambiguation — which collapse to a
    // single canonical helper + redirected uses.
    //
    // Runs BEFORE `beta_reduce_lambda_apply`, which destructively
    // consumes `Apply(Lambda, args)` into Let-chains; the post-CSE
    // redirects can expose new alpha-equivalences that CSE's
    // fixpoint loop catches in a later iteration.
    let ctor_inlined = prep.step("cse_alpha_equivalent_lambda_helpers", || {
        cse_alpha_equivalent_lambda_helpers::cse_alpha_equivalent_lambda_helpers(ctor_inlined)
    });
    // Reverse `If { condition: <Lambda/RecFn>, then, else }` — a
    // church/Scott eliminator that a conditional recognizer mistook
    // for a native `if`, leaving the invalid `if fn(...) { … } { … }
    // else { … }`. Restores `Apply(<eliminator>, [then, else])`. Runs
    // BEFORE `beta_reduce_lambda_apply`, which folds it into a legal
    // let-chain.
    let ctor_inlined = prep.step("undo_if_on_function_condition", || {
        undo_if_on_function_condition::undo_if_on_function_condition(ctor_inlined)
    });
    // Decode a fully-abstracted Church-pair constructor applied to its
    // two fields — `Apply(λa.λb.λk. k a b, [x, y])` → `Pair(x, y)`.
    // These applications are exposed by `undo_if_on_function_condition`
    // (they were hidden inside a malformed `If`) AFTER the earlier
    // `hoist_church_pair_pack` pass ran, so they need decoding here.
    // Consumers already destructure these sites as native `Pair`.
    let ctor_inlined = prep.step("decode_church_pair_application", || {
        decode_church_pair_application::decode_church_pair_application(ctor_inlined)
    });
    // Re-run the pair-eliminator collapse AFTER the native-`Pair` producers
    // above (decode_church_to_native / pack inlining / pair-application decode):
    // its native-`Pair(a,b).fst -> a` / `.snd -> b` branch folds the literal
    // Pair projections those passes emit (the early invocation ran before they
    // existed). Purity-gated; inert when decode_church_to_native is off.
    let ctor_inlined = prep.step("collapse_church_pair_eliminator_ast", || {
        church_pair_collapse::collapse_church_pair_eliminator_ast(ctor_inlined)
    });
    // Lower a multi-variant Scott ELIMINATOR application `v(k0,..,kN)` — whose
    // subject `v` is an opaque field extracted from decoded data — to native
    // `when v is { T_i(fields) -> ki_body }`. Sound-gated on origin-provenance
    // (`v` is a field/payload of stub-matched data) + stub-type arity
    // resolution (a signature shared by several stub types rebuilds with
    // UN-attributed positional patterns); inert otherwise. See the pass docs.
    let ctor_inlined = prep.step("resolve_scott_eliminator", || {
        resolve_scott_eliminator::resolve_scott_eliminator(ctor_inlined)
    });
    // Beta-reduce `Apply(Lambda(params, body), args)` to a Let-chain
    // (NOT in-place substitution) when arity matches exactly. Cleans
    // up immediately-applied lambdas introduced by upstream church-
    // decoding + pack-call use-site rewriters. `drop_dead_pure_lets`
    // downstream handles unused-let cleanup. Validator entry params
    // (`redeemer`, `datum`, `script_context`, …) skipped — the
    // promote-entry pass depends on the Lambda structure surviving.
    let ctor_inlined = prep.step("beta_reduce_lambda_apply", || {
        beta_reduce_lambda_apply::beta_reduce_lambda_apply(ctor_inlined)
    });
    // Eta-reduce `fn(p1, …, pN) { F(p1, …, pN) }` → `F` when F is a
    // closed value-shaped expression (Var, FieldAccess, IndexAccess):
    // the bare-forwarder counterpart to `eta_reduce_pair_aliases`.
    let ctor_inlined = prep.step("eta_reduce_lambda_forwarder", || {
        eta_reduce_lambda_forwarder::eta_reduce_lambda_forwarder(ctor_inlined)
    });
    // CSE-as-extraction: scan Lambda/RecFn bodies for repeated
    // non-trivial subexpressions and extract them into a local
    // `let w = …` — e.g. two alpha-equivalent
    // `when variant is { Pair → … }` blocks in a single BinOp. The
    // free-vars check skips candidates whose variables wouldn't be
    // in scope at the extraction point.
    let ctor_inlined = prep.step("extract_repeated_subexpr", || {
        extract_repeated_subexpr::extract_repeated_subexpr(ctor_inlined)
    });
    // ^ hoists `let w = <rep clone>` whose representative can carry binders
    // already present elsewhere — re-uniquify.
    let ctor_inlined = prep.step("uniquify_duplicate_binders", || {
        alpha_uniquify::uniquify_duplicate_binders(ctor_inlined)
    });
    // `extract_repeated_subexpr` names every extraction `let w = …`,
    // so nested or sequential extractions collide on `w`, and the
    // name-only printer would fuse those distinct `VarId` bindings —
    // silently capturing the wrong value (a degenerate `let w = w`,
    // or three different `w`s sharing one expression). Re-run the
    // shadow disambiguator so each extra `w` becomes `w_2`, `w_3`, …
    // with its uses rewired by `VarId`; the call at the top of
    // `prepare_for_render` ran before these binders existed.
    let ctor_inlined = prep.step("disambiguate_shadowed_lets", || {
        disambiguate_shadowed_lets(&ctor_inlined)
    });
    // TYPE-based Cardano sum naming, AFTER the CSE has minted its `let w = …`
    // extraction bindings. The name-based `name_cardano_sum_arms` above cannot
    // type a `when w is { … }` whose subject is a bare CSE binder with no
    // reserved Cardano name; the forward type-env can, by dataflow — it seeds
    // `script_context : ScriptContext` and propagates through the
    // `let w = <…>.fields[N]` chain, typing `w` as the sum type at that field.
    // With `w` typed, the env-aware `bind_cardano_sum_when_payload` reshapes
    // the inner nullary arms (`Constr<0>`/`Constr<2>` re-projecting
    // `w.fields[i]`) and `name_cardano_sum_arms` names them. Idempotent +
    // fail-closed: already-named arms are non-nullary so re-binding skips
    // them, and the same ABI-arity / version gates apply, so a mis-typed
    // subject yields the honest `Unknown_*` rather than a wrong name. Runs
    // post-CSE so the subject is the stable bare binder, not the inline ×N
    // repeated expression.
    let mut cardano_env = prep.step("build_cardano_type_env", || {
        cardano_type_env::build_cardano_type_env(&ctor_inlined, ctx)
    });
    // A PlutusTx-shaped context reaches here typed by nothing: its
    // records are peeled off `.fields` rather than indexed, so neither
    // the forward env nor the reserved-name path resolves a `when`
    // subject on one. Fold in what the peel can settle, and the two
    // passes below name those arms like any other Cardano sum.
    cardano_env.fill_gaps(name_context_field_peel::infer_context_types(
        &ctor_inlined,
        ctx,
    ));
    let ctor_inlined = prep.step("bind_cardano_sum_when_payload", || {
        bind_cardano_sum_when_payload::bind_cardano_sum_when_payload(
            ctor_inlined,
            &cardano_env,
            ctx,
        )
    });
    let ctor_inlined = prep.step("name_cardano_sum_arms", || {
        name_cardano_sum_arms::name_cardano_sum_arms(ctor_inlined, &cardano_env, ctx)
    });
    // The arms are named; a constructor of the same type built as a
    // VALUE beside one is still raw. `==` types it.
    let ctor_inlined = prep.step("name_cardano_sum_values", || {
        name_cardano_sum_values::name_cardano_sum_values(ctor_inlined, &cardano_env, ctx)
    });
    // Resolve positional `<record>.fields[N]` to the schema-named field for ANY
    // env-typed record — the type-driven counterpart to the TxInfo-only
    // `resolve_tx_info_field_indices` (a governance chain's `….fields[2]`
    // becomes `… .governance_action`). Builds its own env; no-op without an
    // explicit render version, so versionless renders are untouched.
    let ctor_inlined = prep.step("resolve_cardano_field_indices", || {
        cardano_type_env::resolve_cardano_field_indices(ctor_inlined, ctx)
    });
    // Rename a synthetic `let w = <…>.governance_action` binder to the field it
    // projects, so the following `when w is { … }` reads by the Cardano name.
    // Runs AFTER the field-index resolution that mints the accessor.
    // Drop-on-collision; version-gated.
    let ctor_inlined = prep.step("rename_let_to_cardano_field", || {
        rename_let_to_cardano_field::rename_let_to_cardano_field(ctor_inlined, ctx)
    });
    // The arm-naming above renames synthetic `when` PAYLOAD binders to schema
    // field names (`field_1 → new_parameters`). Those are pattern binders, so
    // a collision with another in-scope binder is resolved by the late
    // `disambiguate_shadowed_pattern_binders` near the end of this function,
    // not by `disambiguate_shadowed_lets` (lets/lambdas only). The rewires are
    // VarId-keyed, so such a collision is a visual relabel, never a capture.
    let ctor_inlined = prep.step("recfn_self_ref_probe", || {
        recfn_self_ref_probe::recfn_self_ref_probe(ctor_inlined)
    });
    // Collapse the Z-combinator's dead identity self-receiver param:
    // `const n = rec fn x(__k) { … x(d) … }` used as `n(d)`, where
    // `__k` is unused and every call site feeds the identity `d`.
    // Dropping `__k` and the identity arg at every site (self +
    // external alias) is a no-op beta-reduction that unblocks
    // `clarify_rec_self_value_use` and `flatten_recfn_unused_self`
    // below, which recover the real recursive call from the bogus
    // `when x(d) is { … }` Scott-decode. Inert unless the exact
    // all-sites-identity shape holds.
    let ctor_inlined = prep.step("collapse_identity_self_receiver", || {
        collapse_identity_self_receiver::collapse_identity_self_receiver(ctor_inlined)
    });
    // A rec fn used as a VALUE (when-subject, Apply-arg, bare-Var)
    // gets a `let _self = <rec_fn_name>` alias in its body and its
    // value-context refs redirected to it; calls in
    // `Apply.function` position keep the original VarId.
    let ctor_inlined = prep.step("clarify_rec_self_value_use", || {
        clarify_rec_self_value_use::clarify_rec_self_value_use(ctor_inlined)
    });
    // Flatten `rec fn name(_unused_outer) { fn(p1, …, pN) { body } }`
    // to `rec fn name(p1, …, pN) { body }` when the outer
    // self-receiver Lambda's params are unused. Removes the
    // Y-combinator residue and exposes the rec-fn's real arity.
    let ctor_inlined = prep.step("flatten_recfn_unused_self", || {
        flatten_recfn_unused_self::flatten_recfn_unused_self(ctor_inlined)
    });
    // Rename `helper_<N>` bindings whose body matches a known
    // arithmetic / church-bool / comparison shape (e.g. `fn(x,y){x+y}`
    // → `add_int`). Multi-instance shapes get a numeric suffix.
    let ctor_inlined = prep.step("rename_semantic_helpers", || {
        rename_semantic_helpers::rename_semantic_helpers(ctor_inlined)
    });
    // Recover native `if`/`else` from church-Boolean residue
    // (`let r = if c { e } else { b }; when r is { Constr1 -> A; _ -> B }`).
    // Inert when no top-level zero-arity Constr consts are bound.
    let bool_recovered = prep.step("recover_church_booleans", || {
        recover_church_booleans::recover_church_booleans(ctor_inlined)
    });
    // Recover the INVERTED *terminal* church-bool variant the two-level
    // recoverer above never sees: a church Boolean used directly as a
    // validator outcome that the simplify church-when collapse emitted as
    // `!cond || (trace MSG: church_false)`. Fail-closed on a
    // ScottPositional church_false witness on the `||` short-circuit
    // branch; a data-Bool `Constr<1>` is never touched.
    let bool_recovered = prep.step("recover_inverted_church_or", || {
        recover_inverted_church_or::recover_inverted_church_or(bool_recovered)
    });
    // Recover a native `Ordering` (`Less`/`Equal`/`Greater`) in the PRODUCER
    // branches of a 3-way `int.compare` comparator whose result is consumed
    // by a clean 3-arm Ordering `when` (tags {0,1,2}). `boolean_cleanup`
    // leaves a 3-way sum's nullary Constrs unfolded, so the comparator
    // survives as tag-faithful `if … {Constr<0>} … else {Constr<2>}` printed
    // as the stub `Unknown_E_0_<tag>` — inconsistent with the consumer's
    // names. Relabels each branch by its EXACT tag (never operator-sorted);
    // fail-closed, so a `== Constr<0>` equality or a wildcard-arm consumer
    // leaves the comparator honest.
    let bool_recovered = prep.step("recover_ordering_comparator", || {
        recover_ordering_comparator::recover_ordering_comparator(bool_recovered)
    });
    // Inline always-fail helpers: `fn h(_) { fail @"..." }` + call →
    // substitute the fail expression at each call site, drop the helper
    // when no bare refs remain.
    let fail_inlined = prep.step("inline_always_fail_helpers", || {
        inline_always_fail_helpers::inline_always_fail_helpers(bool_recovered)
    });
    // Collapse an over-applied divergent fail: `a(x, y)` → `a` when `a`
    // provably diverges (a `fail`/const-bound-to-fail), args carry no strict
    // failpoint. Removes ill-typed `fail(…)` surface; unifies with the bare
    // `_ -> a` default sites. Runs after fail-inlining materialises the fails.
    let fail_inlined = prep.step("collapse_over_applied_fail", || {
        collapse_over_applied_fail::collapse_over_applied_fail(fail_inlined)
    });
    // Eta-saturate a recursion knot whose visible param is a dead strictness
    // thunk and whose body under-applies a known callee by exactly one: `rec fn
    // o(dead) { helper(a, b) }` (helper 3-ary) → `rec fn o(z) { helper(a, b, z)
    // }`. Fixes the mis-lowered list-decoder knot.
    let fail_inlined = prep.step("saturate_dead_param_knot", || {
        saturate_dead_param_knot::saturate_dead_param_knot(fail_inlined)
    });
    // Collapse degenerate empty `when X is { }` (zero clauses) into `X` —
    // a no-dispatch eliminator left over from a church/Scott lowering
    // whose subject turned out to be a diverging value.
    let fail_inlined = prep.step("collapse_empty_when", || {
        collapse_empty_when::collapse_empty_when(fail_inlined)
    });
    // Re-label a tail `Bool(false)` as `None` when its `let` binding is
    // matched downstream against `Some`/`None` — a `None` that a decoder
    // collapsed to `False` (the two share a nullary encoding). Uses the
    // structural `Some`/`None` match as evidence, not inferred types
    // (which the same ambiguity can poison).
    let option_fixed = prep.step("fix_option_false_to_none", || {
        fix_option_false_to_none::fix_option_false_to_none(fail_inlined)
    });
    // The MIRROR of the pass above: re-label an `Option::None` tail leaf
    // that is actually `Bool(false)`. Fires ONLY when the program is proven
    // `InverseCip` (so `None` = `Constr<1>` = `church_false` = `False`) AND
    // the `None` sits in a Bool-CONSUMING position (an `&&`/`||` operand or
    // `if` condition provably Bool-or-None on every tail). A no-op under
    // CIP; never touches `Some`/`None` patterns or genuine Option-None
    // values (a call-site `if h(…) { None }` branch is not a Bool position).
    let option_fixed = prep.step("relabel_bool_none_to_false", || {
        relabel_bool_none_to_false::relabel_bool_none_to_false(option_fixed, ctx)
    });
    // Recover a native `if` from an `Option`-named `when` whose subject is
    // provably a Bool — the church-relabel residue left over a `list.any`
    // /`list.all` predicate result (`when ok is {None -> .; Some(_) -> .}`
    // where `ok` is a Bool). Tag-equivalent and compilable.
    let bool_if_recovered = prep.step("recover_if_from_bool_option_when", || {
        recover_if_from_bool_option_when::recover_if_from_bool_option_when(option_fixed)
    });
    // In an inverse-CIP program church_true ≡ Scott list-nil (both a nullary
    // `Constr<0>`), so a Bool predicate's base case is shaped `Known(Nil)`
    // and renders `[] -> Nil` instead of `[] -> True`. Relabel `Known(Nil)`
    // value leaves → `True`, but ONLY inside a PROVABLY-Bool function, where
    // a `Nil` leaf must be church_true and never a genuine list nil. No-op
    // under CIP and on any fn with a non-Bool leaf.
    let bool_if_recovered = prep.step("recover_inverse_cip_nil_as_true", || {
        recover_inverse_cip_nil_as_true::recover_inverse_cip_nil_as_true(bool_if_recovered, ctx)
    });
    // Normalize a HOISTED `church_false` reference used as a `when`-arm RESULT
    // to native `False`, but ONLY when that `when` is provably Bool-TYPED:
    // every arm is Bool-or-neutral (no arm is a concrete non-Bool value; an
    // opaque helper call is neutral) AND at least one arm has a definite Bool
    // leaf. The Bool-collapse already committed the inverse-CIP polarity
    // (`church_true = Constr<0>`, `Constr<1> = False`) on the INLINE sites,
    // leaving hoisted `fn church_false(_, f){f}` refs printed beside native
    // `False`/`&&` siblings — a rendering inconsistency, not a polarity
    // choice, so normalizing inherits that polarity and cannot invert.
    // Fail-closed: no Bool sibling means no change, a genuine
    // `church_false(x, y)` CALL (an `Apply`) is never touched, and a
    // church-TRUE selector never matches. Placed so the now-dead
    // `fn church_false` def is swept by the `drop_dead_pure_lets` re-run below.
    let bool_if_recovered = prep.step("normalize_church_false_arm_to_native", || {
        normalize_church_false_arm_to_native::normalize_church_false_arm_to_native(
            bool_if_recovered,
        )
    });
    // Late identity-helper re-run: `eta_reduce_lambda_forwarder` above mints
    // `const rec_fn_24 = map` ALIASES of identity fns after the only early
    // `inline_identity_helpers` call, so the alias branch fires only here.
    // ORDER IS LOAD-BEARING: it must run BEFORE
    // `promote_validator_entry_first`, whose reorder deliberately breaks
    // lexical scope (refs hoisted above their binder), while the inline
    // pass's drop gate counts refs in the Let BODY only — running after
    // would undercount and drop a live binder. `already_promoted` therefore
    // skips the re-run on a tree a nesting caller already promoted. The
    // `drop_dead_pure_lets` re-run then clears the identity fn the consumed
    // alias pointed at (`fn map(v) { v }`).
    let bool_if_recovered = if already_promoted(&bool_if_recovered) {
        bool_if_recovered
    } else {
        let inlined = inline_identity_helper::inline_identity_helpers(bool_if_recovered);
        drop_dead_pure_lets::drop_dead_pure_lets(inlined)
    };
    let final_expr = prep.step("promote_validator_entry_first", || {
        promote_validator_entry_first(bool_if_recovered)
    });
    // Decode SAFE Church-pair constructions `pair_pack(a, b)` → native
    // `Pair(a, b)`. The consumer side is already native `expect Pair(...)`
    // (decoded in simplify); this closes the producer/consumer gap left by
    // the off-by-default `decode_church_to_native`. Per-construction-site +
    // sound by construction: a mis-converted Church-applied pair becomes
    // `Pair(..)(..)` (an type error = honest-invalid, never silently
    // wrong); Scott-accumulator pairs (lambda component / applied value) are
    // left Church for readability. Inert when no `pair_pack` helper exists.
    let final_expr = prep.step("decode_safe_pair_pack", || {
        decode_safe_pair_pack::decode_safe_pair_pack(final_expr)
    });
    // Rebind surviving `[_, ..] -> ...xs.head...xs[1..]` cons-arms (the
    // ones `rewrite_native_list_map` did NOT fold into `list.map`, e.g. a
    // `church_true` nil arm) to idiomatic `[head, ..tail] -> ...head...tail`.
    // Placed LAST so it runs after all VarId-counter-sensitive CSE/naming
    // passes — it REUSES the wildcard binders' existing VarIds (never mints
    // fresh ones), so it cannot perturb synthetic helper numbering downstream.
    let final_expr = prep.step("bind_list_cons_head_tail", || {
        bind_list_cons_head_tail::bind_list_cons_head_tail(final_expr)
    });
    // `_`-prefix unused NON-placeholder `when`-pattern binders
    // (`Spending(output_reference, datum)` → `Spending(_output_reference,
    // datum)`). Rename-only. Runs after Scott-eliminator resolution and
    // inlining have materialized all references, so the use count reflects
    // the final render.
    let final_expr = prep.step("underscore_unused_pattern_binders", || {
        rename_unused_lambda_params::underscore_unused_pattern_binders(final_expr)
    });
    // Drop a stray trailing `()`/`force` on a fully-applied call whose callee
    // provably returns a non-callable literal (List/Pair/…), e.g. `f_58(x)()`
    // → `f_58(x)`. Runs LATE so the callee bodies are in their final,
    // structurally-recovered form, with their tails already List/Pair literals.
    let final_expr = prep.step("strip_void_apply_on_noncallable_result", || {
        strip_void_apply_on_noncallable_result::strip_void_apply_on_noncallable_result(final_expr)
    });
    // Element naming (late): name the cons-head of a list-typed TxInfo
    // field after the field SINGULAR, and an interproc rec-fn list parameter
    // (proven single-source) after the PLURAL. Must run AFTER
    // `bind_list_cons_head_tail` so the `[head, ..tail]` binders exist.
    let final_expr = prep.step("rename_list_element_binders_late", || {
        resolve_tx_info_field_indices::rename_list_element_binders_late(final_expr, ctx)
    });
    // Interprocedural identity-PARAMETER inlining (LATE): a single-call-site,
    // non-rec helper whose param is only ever the identity `fn(x){x}` applied as
    // `param(arg)` → inline `param(arg) → arg`, drop the param, and hoist the
    // dropped arg's `fail` selector to a statement-position guard (order-exact,
    // fail-closed). Runs LATE so the canonical 3-param-with-`When`-selector +
    // `fn(x){x}` shape produced by the structural-recovery/CPS passes exists.
    let final_expr = prep.step("inline_identity_params", || {
        inline_identity_param::inline_identity_params(final_expr)
    });
    // Re-disambiguate pattern binders ONE FINAL TIME, after every pass that
    // materializes or renames them: the early call at the top of
    // `prepare_for_render` precedes `inline_pattern_field_access`, whose
    // synthetic `field_N` binders can stack several live `field_0` in one
    // nested chain. Disambiguating on the FINAL names also avoids a premature
    // suffix where a later semantic rename already removed the outer shadow.
    // Scope-aware (scope truncated on clause/lambda/recfn exit) and rebound by
    // `VarId`, so only a binder genuinely shadowing an enclosing same-name
    // binder is suffixed (`field_0` → `field_0_2`); disjoint sibling scopes and
    // `_` are untouched. `Binder::renamed` mints no fresh VarIds, so helper
    // numbering cannot shift. Because `promote_validator_entry_first` has
    // already moved the promoted helper lets below `decompiled`, the scope walk
    // does not see those names inside the validator body: a pattern binder
    // shadowing a PROMOTED HELPER name is not suffixed — a miss, never a wrong
    // rename.
    let final_expr = prep.step("disambiguate_shadowed_pattern_binders", || {
        disambiguate_shadowed_pattern_binders(final_expr)
    });
    // A fn whose whole body is a bare `rec fn` returns that closure invisibly
    // — rewrap as define-then-reference so the trailing return line shows it.
    // Placed AFTER all the y-comb/half-Z matchers, which key on the bare
    // `Lambda{body: RecFn}` shape this rewrap changes.
    // Then copy-propagate pure single-use bare-Var aliases (`let p10 = w; …
    // p10 …` → `… w …`). Runs dead-late among the binder-touching passes: the
    // alias producers (`beta_reduce_lambda_apply` Let-chains,
    // `extract_repeated_subexpr`, pack/identity inlining) have all run, names
    // are final (underscore pass + both disambiguators above), and only the
    // globally-collision-guarded `fold_const_recfn_alias` /
    // `lower_constr_field_sugar` follow. Dual-keyed use count + print-capture
    // path gate; fail-closed everywhere; no fresh VarIds.
    let final_expr = prep.step("clarify_recfn_tail_return", || {
        clarify_recfn_tail_return::clarify_recfn_tail_return(final_expr)
    });
    let final_expr = prep.step("copy_propagate_var_aliases", || {
        copy_propagate_var_aliases::copy_propagate_var_aliases(final_expr)
    });
    // Fold a top-level synthetic-alias const whose value is a named rec fn
    // (`const field_0_64 = rec fn any(…)`) by renaming the opaque `field_N`
    // binder to the inner function's real name and rewiring its call sites,
    // so the pretty-printer's `let f = rec fn f` rule collapses it to the
    // bare `rec fn any(…)`. Guarded on the inner name being unique across
    // ALL binders (by sanitized identifier); inert otherwise. Runs DEAD-LAST
    // so that guard counts the FINAL rendered binder names — a binder minted
    // or renamed later could otherwise capture a rewritten reference.
    let final_expr = prep.step("fold_const_recfn_alias", || {
        fold_const_recfn_alias::fold_const_recfn_alias(final_expr)
    });
    // Recover Constr-encoded list cons cells whose tail is a hoisted const/let
    // ref into a native spread `[head, ..tail]`. `simplify_constr` folds only
    // INLINE cons chains terminating in nil, leaving a `Var` tail bound to a
    // CSE-hoisted list const (or a chain of such refs) as the stub
    // `Unknown_E_2_1(head, tail)`. Runs DEAD-LAST, after CSE has hoisted
    // those consts into top-level `Let`s, so the const-value table is
    // complete. Fail-closed: only tag-1 arity-2 cells whose SECOND field
    // provably resolves to a list are folded — the sibling tag-0
    // `Unknown_E_2_0(Data, Data)` PAIR and any non-list tail are untouched.
    // Mints no VarIds.
    let final_expr = prep.step("recover_constr_cons_spread", || {
        recover_constr_cons_spread::recover_constr_cons_spread(final_expr)
    });
    // The recursive builder the pass above stops at: its cons tail is a
    // self-call no value chase can resolve, and its nil arm is the shared
    // nullary stub. The walk proves both at once, so both arms
    // relabel together.
    let final_expr = prep.step("recover_recursive_list_builder", || {
        recover_recursive_list_builder::recover_recursive_list_builder(final_expr)
    });
    // Lower the raw-`Constr` field-access sugar (`record.tag` / `record.fields`)
    // to compilable `builtin.un_constr_data(record).1st` / `.2nd`; `.tag` and
    // `.fields` are not surface syntax, so the un-recovered raw-Constr spine is
    // otherwise non-compilable. GATE B fail-closes on a concrete blueprint
    // `Named` record, so a genuine schema-titled `tag`/`fields` field is never
    // rewritten. Runs dead-last, after every record-naming/typing pass.
    let final_expr = prep.step("lower_constr_field_sugar", || {
        lower_constr_field_sugar::lower_constr_field_sugar(final_expr, ctx)
    });
    // Surface currying at OVER-APPLIED helper calls: MID translate flattened
    // `helper(a, b)(c)` into one 3-arg `helper(a, b, c)` contradicting the
    // 2-param signature. Re-associate to `helper(a, b)(c)`. Runs DEAD-LAST:
    // needs `clarify_recfn_tail_return`'s `Let{rec fn}; Var` tail and the
    // final copy_propagate/fold_const_recfn_alias Var wiring settled, and
    // nothing may re-flatten after it. Mints no VarIds and clones no
    // binder-bearing subtrees (args are moved), so the uniqueness
    // debug_assert below holds.
    let final_expr = prep.step("split_over_applied_helper_calls", || {
        split_over_applied_helper_calls::split_over_applied_helper_calls(final_expr)
    });
    // Sweep helper functions nothing calls. Runs DEAD-LAST, after every
    // inline/hoist/CSE pass has settled where the call sites are, and
    // after `promote_validator_entry_first` broke lexical scope — its
    // whole-tree reference count does not depend on scope. Drops
    // bindings only; mints no VarIds.
    let final_expr = prep.step("drop_unreferenced_helper_fns", || {
        drop_unreferenced_helper_fns::drop_unreferenced_helper_fns(final_expr)
    });
    // Name a `ScriptContext` that a PlutusTx-compiled script peels off
    // its `.fields` list instead of indexing. Runs after every other
    // naming pass so it only fills placeholders none of them claimed,
    // and after the sweeps above so the peel it inspects is final.
    let final_expr = prep.step("name_context_field_peel", || {
        name_context_field_peel::name_context_field_peel(final_expr, ctx)
    });
    // Last: a `let` nothing reads, holding a check that must still run,
    // becomes the statement it already is. Runs after every naming pass
    // so a binder some pass deliberately named is judged on its final
    // name, and after the dead-let sweeps so only the effectful ones are
    // left to consider.
    let final_expr = prep.step("unname_discarded_check", || {
        unname_discarded_check::unname_discarded_check(final_expr)
    });
    // Binder-id uniqueness invariant: the entry uniquify and the
    // re-uniquify after every cloning pass must leave ZERO duplicate binder
    // ids. A failure means a new pass clones binder-bearing subtrees — add
    // a re-uniquify after it; a duplicate corrupts every id-keyed analysis.
    debug_assert_eq!(
        alpha_uniquify::count_duplicate_binder_ids(&final_expr),
        0,
        "duplicate binder VarIds escaped prepare_for_render"
    );
    // Inter-procedural param-slot provenance — ANALYSIS-ONLY instrumentation;
    // never mutates the tree. The report says which projection-eliminator
    // heads, if any, are soundly Scott.
    if crate::debug_env::provenance() {
        let prov = interproc_provenance::analyze(&final_expr);
        eprintln!("{}", interproc_provenance::report(&prov));
    }
    Prepared {
        expr: final_expr,
        church_notes,
        profile: prep.finish(),
    }
}

/// `true` when the top-level Let chain is already in
/// `promote_validator_entry_first`'s output shape: `decompiled` FIRST with
/// further top-level lets below it. Pre-promotion this cannot occur — a
/// validator value cannot reference helpers bound BELOW it (they'd be out
/// of scope), so helpers always precede `decompiled` in the unpromoted
/// chain. Used to skip the late identity-inline/DCE re-run when a caller
/// nests `prepare_for_render` on its own output, where lexical scope is
/// broken and the body-only ref counts would be unsound.
///
/// `promote_validator_entry_first` moves the synthetic `Let` named
/// `decompiled` — minted by `pipeline::wrap_validator_entry_for_render`,
/// tagged `VarKind::ValidatorEntry`, and reserved by that pass — to the
/// head of the chain, replacing the terminal body with `Unit` (rendered as
/// `Void`, then stripped by `decompile_program`). The reorder violates
/// PseudoExpr's lexical-scope invariant, since the entry body refers to
/// helpers now bound below it; that is safe because the pass runs only on
/// `prepare_for_render`'s render-only clone, the renderer does not enforce
/// scope, and the surface allows forward references between top-level
/// declarations.
fn already_promoted(expr: &PseudoExpr) -> bool {
    if let PseudoExpr::Let { name, body, .. } = expr
        && name == "decompiled"
    {
        return matches!(body.as_ref(), PseudoExpr::Let { .. });
    }
    false
}

fn promote_validator_entry_first(expr: PseudoExpr) -> PseudoExpr {
    /// Walk the Let chain, extract `(name, id, value)` triples, return
    /// the final non-Let terminal and the chain.
    fn unwind_chain(
        mut expr: PseudoExpr,
    ) -> (Vec<(String, Option<VarId>, PseudoExpr)>, PseudoExpr) {
        let mut chain = Vec::new();
        loop {
            match expr {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    chain.push((name, id, value.into_inner()));
                    expr = body.into_inner();
                }
                other => return (chain, other),
            }
        }
    }

    let (chain, terminal) = unwind_chain(expr);
    // Find the validator entry in the chain by name marker.
    let entry_idx = chain.iter().position(|(name, _, _)| name == "decompiled");
    let Some(entry_idx) = entry_idx else {
        // No validator entry to promote — rebuild as-is.
        let mut rebuilt = terminal;
        for (name, id, value) in chain.into_iter().rev() {
            rebuilt = PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(rebuilt),
            };
        }
        return rebuilt;
    };

    let mut chain = chain;
    let entry = chain.remove(entry_idx);

    // Build `Let { decompiled, body: Let helper_1, … Unit }`. The
    // original terminal is dropped — the rendering doesn't need it.
    let _ = terminal;
    let mut rebuilt = PseudoExpr::Unit;
    for (name, id, value) in chain.into_iter().rev() {
        rebuilt = PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(rebuilt),
        };
    }
    PseudoExpr::Let {
        name: entry.0,
        id: entry.1,
        value: PBox::new(entry.2),
        body: PBox::new(rebuilt),
    }
}

#[cfg(test)]
pub(crate) fn debug_inline_slice_chain_aliases(expr: PseudoExpr) -> PseudoExpr {
    inline_slice_chain_aliases(expr)
}

#[cfg(test)]
pub(crate) fn debug_rename_render_var_in_expr(
    expr: &PseudoExpr,
    old_name: &str,
    new_name: &str,
) -> PseudoExpr {
    rename_var_in_expr(expr, old_name, new_name)
}

#[cfg(test)]
fn rename_var_in_expr(expr: &PseudoExpr, old_name: &str, new_name: &str) -> PseudoExpr {
    rename_var_in_expr_with(expr, old_name, new_name, |_| true)
}

fn rename_compat_var_in_expr(expr: &PseudoExpr, old_name: &str, new_name: &str) -> PseudoExpr {
    rename_var_in_expr_with(expr, old_name, new_name, |id| id.get().is_none())
}

/// One pending step of the two `Var`-renaming walks' explicit job stacks.
enum RenameStep {
    /// Descend into this subtree.
    Enter(PseudoExpr),
    /// A subtree the scope rules exclude — pushed onto `done` verbatim.
    Keep(PseudoExpr),
    /// Rebuild this node from its rewritten children.
    Post(RenamePost),
}

/// Everything about a node that is NOT one of its child expressions, held
/// while those children are being rewritten.
enum RenamePost {
    Let {
        name: String,
        id: Option<VarId>,
    },
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    When {
        subject_name: Option<Binder>,
        /// Per clause: its pattern (never descended into, exactly as
        /// `map_children` leaves it) and whether it had a guard.
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(scope_recurse::PlainPost),
}

/// Rebuild one node from its already-rewritten children on `done`, mirroring
/// `map_children`'s reconstruction for the same node kind exactly. Children
/// were left on `done` in source order, so they come off in that order.
fn rename_rebuild(post: RenamePost, done: &mut Vec<PseudoExpr>) -> PseudoExpr {
    match post {
        RenamePost::Let { name, id } => {
            let body = done.pop().expect("let body");
            let value = done.pop().expect("let value");
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }
        RenamePost::Lambda { params } => PseudoExpr::Lambda {
            params,
            body: PBox::new(done.pop().expect("lambda body")),
        },
        RenamePost::RecFn { name, params } => PseudoExpr::RecFn {
            name,
            params,
            body: PBox::new(done.pop().expect("recfn body")),
        },
        RenamePost::When {
            subject_name,
            clause_meta,
        } => {
            let total = 1 + clause_meta
                .iter()
                .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                .sum::<usize>();
            let mut parts = scope_recurse::take(done, total).into_iter();
            let subject = parts.next().expect("when subject");
            let clauses = clause_meta
                .into_iter()
                .map(|(pattern, has_guard)| WhenClause {
                    pattern,
                    guard: has_guard.then(|| parts.next().expect("when guard")),
                    body: parts.next().expect("when clause body"),
                })
                .collect();
            PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses,
            }
        }
        RenamePost::Plain(kind) => scope_recurse::rebuild_plain(kind, done),
    }
}

/// Rename `Var` references named `old_name` to `new_name`, stopping at
/// any binder that REBINDS that name — a `let`'s body, a lambda / rec-fn
/// that takes it as a param, a `when` arm whose pattern or subject binder
/// declares it. Inside such a scope the name means something else, so
/// renaming there would capture.
///
/// `should_rename_id` narrows which references qualify: the plain rename
/// takes all of them, `rename_compat_var_in_expr` only the id-less ones.
///
/// The "don't descend, keep the subtree" decision made per
/// child rides on the job as [`RenameStep::Keep`] rather than being a
/// call argument; children are pushed in REVERSE so they pop in source
/// order.
fn rename_var_in_expr_with(
    expr: &PseudoExpr,
    old_name: &str,
    new_name: &str,
    should_rename_id: impl Fn(Option<VarId>) -> bool,
) -> PseudoExpr {
    let mut steps: Vec<RenameStep> = vec![RenameStep::Enter(expr.clone())];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        let expr = match step {
            RenameStep::Enter(expr) => expr,
            RenameStep::Keep(kept) => {
                done.push(kept);
                continue;
            }
            RenameStep::Post(post) => {
                let rebuilt = rename_rebuild(post, &mut done);
                done.push(rebuilt);
                continue;
            }
        };
        match expr {
            PseudoExpr::Var { name, id } => {
                let renamed = name == old_name && should_rename_id(id);
                done.push(PseudoExpr::Var {
                    name: if renamed { new_name.to_string() } else { name },
                    id,
                });
            }
            // The value is still in the OUTER scope; the body is not.
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                let shadows = name == old_name;
                steps.push(RenameStep::Post(RenamePost::Let { name, id }));
                let body = body.into_inner();
                steps.push(if shadows {
                    RenameStep::Keep(body)
                } else {
                    RenameStep::Enter(body)
                });
                steps.push(RenameStep::Enter(value.into_inner()));
            }
            PseudoExpr::Lambda { params, body } => {
                let binds_old = params.iter().any(|p| p == old_name);
                steps.push(RenameStep::Post(RenamePost::Lambda { params }));
                let body = body.into_inner();
                steps.push(if binds_old {
                    RenameStep::Keep(body)
                } else {
                    RenameStep::Enter(body)
                });
            }
            PseudoExpr::RecFn { name, params, body } => {
                let binds_old = name == old_name || params.iter().any(|p| p == old_name);
                steps.push(RenameStep::Post(RenamePost::RecFn { name, params }));
                let body = body.into_inner();
                steps.push(if binds_old {
                    RenameStep::Keep(body)
                } else {
                    RenameStep::Enter(body)
                });
            }
            // The subject is evaluated before the binder exists, so it is
            // always in the outer scope; each arm is skipped only if THAT arm
            // rebinds the name.
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                let subject_binds_old = subject_name.as_ref().is_some_and(|n| n == old_name);
                let mut clause_meta = Vec::with_capacity(clauses.len());
                let mut clause_steps: Vec<RenameStep> = Vec::new();
                for clause in clauses {
                    let binds_old =
                        subject_binds_old || pattern_binds_name(&clause.pattern, old_name);
                    let step = |e: PseudoExpr| {
                        if binds_old {
                            RenameStep::Keep(e)
                        } else {
                            RenameStep::Enter(e)
                        }
                    };
                    clause_meta.push((clause.pattern, clause.guard.is_some()));
                    if let Some(guard) = clause.guard {
                        clause_steps.push(step(guard));
                    }
                    clause_steps.push(step(clause.body));
                }
                steps.push(RenameStep::Post(RenamePost::When {
                    subject_name,
                    clause_meta,
                }));
                for step in clause_steps.into_iter().rev() {
                    steps.push(step);
                }
                steps.push(RenameStep::Enter(subject.into_inner()));
            }
            // `map_children(other, recur)`.
            other => match scope_recurse::plain_children(other) {
                Ok((kind, children)) => {
                    steps.push(RenameStep::Post(RenamePost::Plain(kind)));
                    for child in children.into_iter().rev() {
                        steps.push(RenameStep::Enter(child));
                    }
                }
                // `map_children` returns a leaf unchanged.
                Err(leaf) => done.push(leaf),
            },
        }
    }

    done.pop().expect("rename leaves exactly one result")
}

/// Rename every `Var` REFERENCE carrying `old_id` to `new_name`, plus a
/// `when`'s subject binder when it is that same id.
///
/// Reference-side only: `let` / lambda / rec-fn / pattern binders keep
/// their display names, because the callers use this to point a use at a
/// name a sibling pass already committed to the declaration.
fn rename_var_use_by_id_in_expr(expr: &PseudoExpr, old_id: VarId, new_name: &str) -> PseudoExpr {
    let mut steps: Vec<RenameStep> = vec![RenameStep::Enter(expr.clone())];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        let expr = match step {
            RenameStep::Enter(expr) => expr,
            // This walk never skips a subtree; the variant belongs to the
            // shared step type.
            RenameStep::Keep(kept) => {
                done.push(kept);
                continue;
            }
            RenameStep::Post(post) => {
                let rebuilt = rename_rebuild(post, &mut done);
                done.push(rebuilt);
                continue;
            }
        };
        match expr {
            PseudoExpr::Var { name, id } => done.push(PseudoExpr::Var {
                name: if id == Some(old_id) {
                    new_name.to_string()
                } else {
                    name
                },
                id,
            }),
            // `map_children` does not surface a `when`'s subject binder, and
            // that binder is a rename target here.
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                let subject_name = subject_name.map(|binder| {
                    if binder.id == old_id {
                        binder.renamed(new_name.to_string())
                    } else {
                        binder
                    }
                });
                let mut clause_meta = Vec::with_capacity(clauses.len());
                let mut clause_children: Vec<PseudoExpr> = Vec::new();
                for clause in clauses {
                    clause_meta.push((clause.pattern, clause.guard.is_some()));
                    if let Some(guard) = clause.guard {
                        clause_children.push(guard);
                    }
                    clause_children.push(clause.body);
                }
                steps.push(RenameStep::Post(RenamePost::When {
                    subject_name,
                    clause_meta,
                }));
                for child in clause_children.into_iter().rev() {
                    steps.push(RenameStep::Enter(child));
                }
                steps.push(RenameStep::Enter(subject.into_inner()));
            }
            // `map_children(other, recur)` — `Let` / `Lambda` / `RecFn` are
            // not "plain" nodes, so they need their own arms.
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                steps.push(RenameStep::Post(RenamePost::Let { name, id }));
                steps.push(RenameStep::Enter(body.into_inner()));
                steps.push(RenameStep::Enter(value.into_inner()));
            }
            PseudoExpr::Lambda { params, body } => {
                steps.push(RenameStep::Post(RenamePost::Lambda { params }));
                steps.push(RenameStep::Enter(body.into_inner()));
            }
            PseudoExpr::RecFn { name, params, body } => {
                steps.push(RenameStep::Post(RenamePost::RecFn { name, params }));
                steps.push(RenameStep::Enter(body.into_inner()));
            }
            other => match scope_recurse::plain_children(other) {
                Ok((kind, children)) => {
                    steps.push(RenameStep::Post(RenamePost::Plain(kind)));
                    for child in children.into_iter().rev() {
                        steps.push(RenameStep::Enter(child));
                    }
                }
                // `map_children` returns a leaf unchanged.
                Err(leaf) => done.push(leaf),
            },
        }
    }

    done.pop().expect("rename leaves exactly one result")
}

#[cfg(test)]
mod tests;
