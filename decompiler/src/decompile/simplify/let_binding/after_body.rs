use super::Simplifier;
use super::state::{LetAfterBodyState, LetPostResult};
use crate::decompile::list_traversal::is_list_tail_call;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

impl Simplifier {
    fn emitted_let_binding_id(name: &str, var_id: Option<VarId>) -> VarId {
        match var_id {
            Some(id) => id,
            None if name == "_" => VarId::fresh_compat_placeholder(),
            None => panic!(
                "named let binding `{name}` should have a concrete VarId after simplify_let_pre_process"
            ),
        }
    }

    fn make_var_for_let_binding_id(&self, name: &str, var_id: Option<VarId>) -> PseudoExpr {
        match var_id {
            Some(id) => PseudoExpr::var_with_id(self.get_renamed_with_id(name, Some(id)), id),
            None => self.make_var(name),
        }
    }

    /// Post-processing after the body is simplified: dethunking,
    /// dead-code elimination, inlining, RecFn conversion, renaming.
    pub(in crate::decompile::simplify) fn simplify_let_after_body(
        &mut self,
        state: LetAfterBodyState,
        mut simplified_body: PseudoExpr,
    ) -> LetPostResult {
        let name = state.name;
        let var_id = state.var_id;
        let name_shadow = state.name_shadow;
        let mut simplified_value = state.simplified_value;
        let is_y_comb = state.is_y_comb;
        let is_and = state.is_and;
        let is_or = state.is_or;
        let has_delayed_rec = state.has_delayed_rec;
        let has_delayed_fst = state.has_delayed_fst;
        let has_delayed_snd = state.has_delayed_snd;
        let is_builtin_alias = state.is_builtin_alias;
        let is_partial_app = state.is_partial_app;
        let selector_entry = state.selector_entry;
        let track_non_thunk = state.track_non_thunk;
        let already_tracked_non_thunk = state.already_tracked_non_thunk;
        let pre_context_name = state.pre_context_name;
        let emitted_let_id = Self::emitted_let_binding_id(&name, var_id);

        macro_rules! finish_let {
            ($expr:expr) => {{
                let result = $expr;
                self.restore_lexical_name(&name, name_shadow);
                return result;
            }};
        }

        let mut cached_body_use_count = None::<usize>;
        let mut cached_value_size = None::<usize>;
        let mut cached_force_chain_use_counts = Vec::<(u8, usize)>::new();

        macro_rules! invalidate_body_analysis {
            () => {{
                cached_body_use_count = None;
                cached_force_chain_use_counts.clear();
            }};
        }

        macro_rules! invalidate_value_analysis {
            () => {{
                cached_value_size = None;
            }};
        }

        macro_rules! body_use_count {
            () => {{
                *cached_body_use_count.get_or_insert_with(|| {
                    Self::count_var_uses_by_id(&simplified_body, &name, var_id)
                })
            }};
        }

        macro_rules! value_size {
            () => {{ *cached_value_size.get_or_insert_with(|| Self::expr_size(&simplified_value)) }};
        }

        macro_rules! force_chain_use_count {
            ($depth:expr) => {{
                let depth = $depth;
                if let Some((_, count)) = cached_force_chain_use_counts
                    .iter()
                    .find(|(cached_depth, _)| *cached_depth == depth)
                {
                    *count
                } else {
                    let count =
                        Self::count_force_chain_uses_by_id(&simplified_body, &name, var_id, depth);
                    cached_force_chain_use_counts.push((depth, count));
                    count
                }
            }};
        }

        if !self.safe_mode {
            simplified_body =
                self.introduce_field_index_aliases(&name, &simplified_value, simplified_body);
        }

        if let PseudoExpr::RecFn {
            name: rec_name,
            params,
            body,
        } = &simplified_body
            && rec_name == &name
            && Self::is_var_used_by_id(&simplified_value, &name, var_id)
        {
            finish_let!(LetPostResult::Resimplify(PseudoExpr::Let {
                name: name.clone(),
                id: Some(emitted_let_id),
                value: PBox::new(PseudoExpr::RecFn {
                    name: rec_name.clone(),
                    params: params.clone(),
                    body: body.clone(),
                }),
                body: PBox::new(simplified_value),
            }));
        }

        self.restore_selector_scope_binding(
            var_id,
            selector_entry,
            track_non_thunk,
            already_tracked_non_thunk,
        );
        // De-thunk syntactically safe delayed values in the let-body,
        // shadow-aware:
        //   let x = delay^d(v) in ... force^d(x) ... => ... v ...
        if let PseudoExpr::Delay(_) = &simplified_value {
            let mut depth: u8 = 0;
            let mut current = &simplified_value;
            while let PseudoExpr::Delay(inner) = current {
                depth = depth.saturating_add(1);
                current = inner.as_ref();
            }
            let current_expr = current.clone();

            let can_inline = Self::is_simple_value(&current_expr)
                || Self::is_fst_selector(&current_expr)
                || Self::is_snd_selector(&current_expr);

            let single_forced_closed_inline = !self.safe_mode
                && Self::is_closed_expr(&current_expr)
                && body_use_count!() == 1
                && force_chain_use_count!(depth) == 1;

            let single_forced_capture_safe_inline = if !self.safe_mode {
                let single_force_use = body_use_count!() == 1 && force_chain_use_count!(depth) == 1;
                if single_force_use {
                    let mut value_vars = Vec::new();
                    Self::collect_referenced_vars(&current_expr, &mut value_vars);
                    value_vars.retain(|v| v != &name);
                    value_vars.is_empty()
                        || !Self::has_binding_for_any(&simplified_body, &value_vars)
                } else {
                    false
                }
            } else {
                false
            };

            if can_inline || single_forced_closed_inline || single_forced_capture_safe_inline {
                simplified_body =
                    self.replace_forced_var(simplified_body, &name, var_id, &current_expr, depth);
                invalidate_body_analysis!();
            }

            // Delay-depth lowering when all uses are forced at least once:
            //   let x = delay^d(v) in ... force^k(x) ...
            //   => let x = delay^(d-1)(v) in ... force^(k-1)(x) ...
            // Semantics-preserving; cuts force(force(...)) noise.
            if !self.safe_mode && depth > 1 {
                let total_uses = body_use_count!();
                let forced_uses = force_chain_use_count!(1);
                if total_uses > 0
                    && total_uses == forced_uses
                    && let PseudoExpr::Delay(inner_once) = simplified_value.clone()
                {
                    simplified_value = inner_once.into_inner();
                    invalidate_value_analysis!();
                    let max_depth =
                        Self::max_force_chain_depth_by_id(&simplified_body, &name, var_id);
                    for k in (1..=max_depth).rev() {
                        let replacement = if k == 1 {
                            self.make_var_for_let_binding_id(&name, var_id)
                        } else {
                            Self::build_force_chain(
                                self.make_var_for_let_binding_id(&name, var_id),
                                k - 1,
                            )
                        };
                        simplified_body = self.replace_forced_var(
                            simplified_body,
                            &name,
                            var_id,
                            &replacement,
                            k,
                        );
                    }
                    invalidate_body_analysis!();
                    self.delays.delayed_value_depths.insert_binding(
                        name.clone(),
                        var_id,
                        depth - 1,
                    );
                }
            }

            // Multi-use lambda dethunk: when every use of `x` is force^n(x),
            // rewrite `let x = delay^n(fn...)` to `let x = fn...` and drop the
            // forces. A lambda is already a value, so thunk semantics survive
            // and nothing is duplicated.
            if !self.safe_mode
                && matches!(
                    &current_expr,
                    PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. }
                )
            {
                let total_uses = body_use_count!();
                let forced_uses = force_chain_use_count!(depth);
                if total_uses > 0 && total_uses == forced_uses {
                    let replacement = self.make_var_for_let_binding_id(&name, var_id);
                    simplified_body = self.replace_forced_var(
                        simplified_body,
                        &name,
                        var_id,
                        &replacement,
                        depth,
                    );
                    invalidate_body_analysis!();
                    simplified_value = current_expr;
                    invalidate_value_analysis!();
                    if let Some(vid) = var_id {
                        self.delays.delayed_value_depths.remove(vid);
                    }
                }
            }
        }

        // Trivial let inlining: `let x = e in x` => `e`
        if let PseudoExpr::Var {
            name: body_var,
            id: Some(body_id),
            ..
        } = &simplified_body
        {
            let ids_match =
                crate::decompile::var_match::refs_match(body_var, body_id.get(), &name, var_id);
            if ids_match {
                finish_let!(LetPostResult::Done(simplified_value));
            }
        }

        // Drop the Y-combinator definition itself; it is inlined as a rec fn.
        if is_y_comb {
            finish_let!(LetPostResult::Done(simplified_body));
        }

        // Check for simple builtin alias - inline and skip the let
        if is_builtin_alias {
            finish_let!(LetPostResult::Done(simplified_body));
        }

        // Check for partial application - inline and skip the let
        if is_partial_app {
            finish_let!(LetPostResult::Done(simplified_body));
        }

        // Drop the let when substitutions removed every use of the binding.
        //
        // Generated field/item aliases can be renamed or rebound with a fresh
        // VarId later in the same simplify walk, so the VarId-aware count reports
        // zero uses while same-named textual references still survive in the body;
        // dropping the binding there strands a free generated name. For those,
        // keep the let while textually-equal uses remain.
        //
        // Dispatch on VarKind when the binding's VarId is annotated, on the name
        // prefix otherwise — `fields_*` has no VarKind variant, and some bindings
        // are not annotated yet when this runs.
        let kind_says_synthetic = var_id
            .and_then(|id| self.var_kinds.kind_annotations.get(&id))
            .is_some_and(|kind| {
                matches!(
                    kind,
                    VarKind::FieldIndexAlias { .. }
                        | VarKind::DataLiteralHoist
                        | VarKind::ConstrPayload { .. }
                )
            });
        let name_says_synthetic = name.starts_with("field_")
            || name.starts_with("fields_")
            || name.starts_with("item_")
            // Same alias-id mismatch class as field_N; hoisted by
            // `simplify::apply::hoist::hoist_large_data_literals_from_apply_args`.
            || name.starts_with("data_literal_");
        let generated_name_like = kind_says_synthetic || name_says_synthetic;
        let name_only_use_count =
            generated_name_like.then(|| Self::count_var_uses(&simplified_body, &name));
        if body_use_count!() == 0
            // STRICT-FAILPOINT GATE: a dead let whose value can
            // FAIL when strictly bound must NOT be dropped — that would make
            // the render accept inputs the bytecode rejects. This is a strict
            // superset of `contains_explicit_error`: it also retains a
            // non-builtin call in strict position (`v_492(redeemer)`,
            // `expect!(...)`, a beta-redex) which can fail with no literal
            // Error node. Builtin partiality is intentionally NOT judged here.
            && !Self::contains_strict_failpoint(&simplified_value)
            && !Self::contains_explicit_trace(&simplified_value)
            && (!generated_name_like || name_only_use_count.unwrap_or(0) == 0)
        {
            finish_let!(LetPostResult::Done(simplified_body));
        }

        // Variable aliasing elimination: `let x = y in body` substitutes `y` for `x`,
        // killing renamings like `let u1 = f_45` while keeping the aliased VarId so
        // refs do not become same-name/different-id orphans. Skipped when the aliased
        // name is rebound anywhere in the body: a textual `x -> y` substitution under
        // an inner `y` binder would capture. An aliased ref with `id: None` resolves
        // by name only, like a compat-placeholder id.
        if let PseudoExpr::Var {
            name: aliased,
            id: aliased_id,
        } = &simplified_value
            && aliased != &name
            && !Self::has_binding_for_any(&simplified_body, std::slice::from_ref(aliased))
        {
            let substituted = if let Some(aliased_id) = aliased_id.get() {
                Self::substitute_var_for_var(&simplified_body, &name, var_id, aliased, aliased_id)
            } else {
                Self::rename_var_binding(&simplified_body, &name, var_id, aliased)
            };

            finish_let!(LetPostResult::Done(substituted));
        }

        // Skip and/or function definitions - they will be inlined via force(and/or(...))
        if is_and || is_or {
            finish_let!(LetPostResult::Done(simplified_body));
        }

        // Skip delayed fst/snd selectors — they were inlined via force(force(f))
        // dethunking above. Only drop the binding if ALL uses were resolved
        // (no remaining bare-value uses of the variable in the body).
        if (has_delayed_fst || has_delayed_snd) && body_use_count!() == 0 {
            finish_let!(LetPostResult::Done(simplified_body));
        }

        // Skip delayed Y-combinator definitions - they are used via force(force(a))
        if has_delayed_rec {
            finish_let!(LetPostResult::Done(simplified_body));
        }

        // Dead code elimination: `let name = { ...; Void } in fail` => `...; fail`
        if Self::is_fail(&simplified_body)
            && let Some(side_effects) = Self::extract_side_effects_before_void(&simplified_value)
        {
            finish_let!(LetPostResult::Done(Self::sequence_before_fail(
                side_effects,
                simplified_body,
            )));
        }

        // Inline Void/Unit - it's just a unit value
        let is_void = match &simplified_value {
            PseudoExpr::Unit => true,
            PseudoExpr::Constr { shape, fields, .. }
                if *shape == ConstructorShape::Known(KnownConstructor::Void)
                    && fields.is_empty() =>
            {
                true
            }
            _ => false,
        };
        if is_void {
            // Replace all uses of this name with Void (will become Unit in output)
            let replaced_body =
                Self::rename_var_binding(&simplified_body, &name, var_id, "__VOID__");
            // Then replace __VOID__ markers with actual Unit
            let final_body = Self::replace_void_markers(replaced_body);
            finish_let!(LetPostResult::Done(final_body));
        }

        // Convert Y-combinator lambda to RecFn:
        // let NAME = fn(SELF, params...) { ... SELF(SELF, ...) ... }
        // → let NAME = rec fn NAME(params...) { ... NAME(...) ... }
        // Also strip self-arg from initial calls NAME(NAME, args) → NAME(args) in body
        if let PseudoExpr::Lambda {
            params: ref lam_params,
            body: ref lam_body,
        } = simplified_value
        {
            if let Some(promoted_recfn) =
                self.try_promote_lambda_rec_wrapper(&name, emitted_let_id, lam_params, lam_body)
            {
                let simplified_body = if !lam_params.is_empty() {
                    Self::strip_thunked_self_calls(&simplified_body, &name)
                } else {
                    simplified_body
                };

                finish_let!(LetPostResult::Done(PseudoExpr::Let {
                    name: name.clone(),
                    id: Some(emitted_let_id),
                    value: PBox::new(promoted_recfn),
                    body: PBox::new(simplified_body),
                }));
            }

            if lam_params.len() >= 2 {
                let self_param = &lam_params[0];
                let stripped_let_body = Self::strip_rec_self_arg(&simplified_body, &name);
                let has_seeded_entry = !stripped_let_body.structural_eq(&simplified_body);
                let has_recursive_self_call = Self::has_self_call(lam_body, self_param);
                let has_direct_self_call =
                    has_seeded_entry && Self::has_direct_self_call(lam_body, self_param);
                if (has_recursive_self_call || has_direct_self_call)
                    && Self::count_var_uses(lam_body, &name) == 0
                {
                    let real_params: Vec<crate::pseudo::ast::Binder> = lam_params[1..].to_vec();
                    // Rename self param to function name in body
                    let renamed_body = Self::rename_var(lam_body, self_param, &name);
                    // Strip the seeded self-arg only for the `f(f, ...)` style.
                    // Direct `self(args...)` wrappers are already in RecFn shape once
                    // the self binder is renamed to the recursive function name.
                    let stripped_body = if has_recursive_self_call {
                        Self::strip_rec_self_arg(&renamed_body, &name)
                    } else {
                        renamed_body
                    };

                    // Strip thunked self-calls: f() → f (0-arg self-calls are thunks)
                    let stripped_body = if !real_params.is_empty() {
                        Self::strip_thunked_self_calls(&stripped_body, &name)
                    } else {
                        stripped_body
                    };
                    let stripped_let_body = if !real_params.is_empty() {
                        Self::strip_thunked_self_calls(&stripped_let_body, &name)
                    } else {
                        stripped_let_body
                    };

                    // Preserve self_param's VarId as the RecFn
                    // self-binder id — body refs were renamed from
                    // self_param → name keeping the original id.
                    // `name.clone().into()` would mint a fresh id
                    // and strand them as name-orphans.
                    let recfn_self_id = self_param.var_id();
                    finish_let!(LetPostResult::Done(PseudoExpr::Let {
                        name: name.clone(),
                        id: Some(emitted_let_id),
                        value: PBox::new(PseudoExpr::RecFn {
                            name: crate::pseudo::ast::Binder::new(name.clone(), recfn_self_id),
                            params: real_params,
                            body: PBox::new(stripped_body),
                        }),
                        body: PBox::new(stripped_let_body),
                    }));
                }
            }
        }

        // Check for RecFn from Apply simplification - rename to let name
        if let PseudoExpr::RecFn {
            name: rec_name,
            params,
            body: rec_body,
        } = simplified_value
        {
            // Reuse rec_name's VarId as the RecFn self-binder id:
            // `rename_var` is name-textual and id-preserving, so body
            // refs renamed rec_name → name still carry that id.
            let recfn_self_id = rec_name.var_id();
            // Rename recursive calls from rec_name to let name
            let renamed_body = if rec_name != name {
                Self::rename_var(&rec_body, &rec_name, &name)
            } else {
                (*rec_body).clone()
            };

            // Strip thunked self-calls: f() → f
            let renamed_body = if !params.is_empty() {
                Self::strip_thunked_self_calls(&renamed_body, &name)
            } else {
                renamed_body
            };
            let simplified_body = if !params.is_empty() {
                Self::strip_thunked_self_calls(&simplified_body, &name)
            } else {
                simplified_body
            };

            finish_let!(LetPostResult::Done(PseudoExpr::Let {
                name: name.clone(),
                id: Some(emitted_let_id),
                value: PBox::new(PseudoExpr::RecFn {
                    name: crate::pseudo::ast::Binder::new(name.clone(), recfn_self_id),
                    params,
                    body: PBox::new(renamed_body),
                }),
                body: PBox::new(simplified_body),
            }));
        }

        // Check for __y_comb_X(fn(self, params...) { body }) -> RecFn
        if let PseudoExpr::Apply { function, args } = &simplified_value
            && let PseudoExpr::Var { name: fn_name, .. } = function.as_ref()
            && fn_name.starts_with("__y_comb_")
            && args.len() == 1
            && let PseudoExpr::Lambda {
                params,
                body: fn_body,
            } = &args[0]
            && !params.is_empty()
        {
            let self_name = &params[0];
            // Reuse the original param binders so
            // their VarIds survive.
            let real_params: Vec<crate::pseudo::ast::Binder> = params[1..].to_vec();

            // Replace self_name with the function name in body
            let renamed_body = Self::rename_var(fn_body, self_name, &name);
            // Strip self-arg from recursive calls: f(f, a, b) -> f(a, b)
            let stripped_body = Self::strip_rec_self_arg(&renamed_body, &name);

            // Strip thunked self-calls: f() → f
            let stripped_body = if !real_params.is_empty() {
                Self::strip_thunked_self_calls(&stripped_body, &name)
            } else {
                stripped_body
            };
            let simplified_body = if !real_params.is_empty() {
                Self::strip_thunked_self_calls(&simplified_body, &name)
            } else {
                simplified_body
            };

            // Use self_name's VarId as the
            // RecFn self-binder id, matching body refs
            // that were renamed from self_name → name.
            let recfn_self_id = self_name.var_id();
            finish_let!(LetPostResult::Done(PseudoExpr::Let {
                name: name.clone(),
                id: Some(emitted_let_id),
                value: PBox::new(PseudoExpr::RecFn {
                    name: crate::pseudo::ast::Binder::new(name.clone(), recfn_self_id),
                    params: real_params,
                    body: PBox::new(stripped_body),
                }),
                body: PBox::new(simplified_body),
            }));
        }

        // Small function inlining: `let f = fn(params) { small_body } in rest`.
        // Inline the lambda at every use site when the body is small and used
        // few times; the resulting IIFEs (`fn(x){body}(arg)`) are folded by
        // simplify_apply into let bindings or direct substitution.
        //
        // Bindings in `preserved_helper_ids` (Let-bound lambdas with a
        // fully-concrete MIR FnSignature) are user-declared helpers and must
        // reach the output, so the whole heuristic is skipped for them —
        // otherwise a helper like `fn is_small(n: Int) -> Bool { n < 10 }`
        // collapses at every call site.
        let is_preserved_helper = var_id
            .map(|vid| self.helpers.preserved_helper_ids.contains(&vid))
            .unwrap_or(false);
        if !self.safe_mode
            && !is_preserved_helper
            && let PseudoExpr::Lambda {
                ref params,
                ref body,
            } = simplified_value
        {
            // Only inline non-recursive small lambdas
            let body_size = Self::expr_size(body);
            let use_count = body_use_count!();
            // Size <= 4 covers `x.fields`, `x[0]`, `Data.to_int(x)`, `x.fst`; the
            // use-count cap prevents code explosion. Even a single use keeps a size
            // limit, or a large body ending in `}` gets over-applied: `}(args...)`.
            // Trivial accessors (body_size <= 2) and unary projection accessors
            // inline at any use count: they are pure, use the parameter once, and
            // each call site becomes a let binding or an access chain like
            // `x.fields.head` that simplifies away.
            let is_projection_accessor = Self::is_single_param_projection_accessor(params, body);
            let is_multi_param_selector_alias =
                params.len() >= 2 && Self::selector_signature(params, body).is_some();
            let is_small_delayed_wrapper = use_count > 0
                && use_count <= 2
                && Self::is_small_delayed_call_wrapper(params, body);
            let is_small_boolean_helper =
                use_count > 0 && use_count <= 4 && Self::is_small_boolean_helper(params, body);
            let should_inline = !is_multi_param_selector_alias
                && use_count > 0
                && ((body_size <= 4 && use_count <= 6)
                    || body_size <= 2
                    || is_projection_accessor
                    || is_small_delayed_wrapper
                    || is_small_boolean_helper
                    || (use_count == 1 && body_size <= 6));
            if should_inline && !params.is_empty() {
                let inlined =
                    self.replace_forced_var(simplified_body, &name, var_id, &simplified_value, 0);
                finish_let!(LetPostResult::Resimplify(inlined));
            }
        }

        // Single-use non-lambda inlining: `let x = small_expr in body` where `x` is
        // used exactly once, dropping intermediaries like
        // `let to_bytes_partial_45 = Data.to_bytes(x)`.
        //
        // Structural access (IndexAccess, FieldAccess, List.tail) is excluded: the
        // list head/tail and field destructuring detection that runs after
        // simplification needs those shapes. Inlining is also refused when the value
        // references a variable the body rebinds (Lambda/Let/RecFn param), which would
        // capture.
        if !self.safe_mode {
            let is_excluded_value = matches!(
                simplified_value,
                PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. }
            ) || matches!(
                &simplified_value,
                PseudoExpr::Delay(inner)
                    if matches!(inner.as_ref(), PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. })
            );
            // Don't inline structural access patterns needed by destructuring detection
            let is_structural_access = match &simplified_value {
                PseudoExpr::IndexAccess { .. } => true,
                PseudoExpr::FieldAccess { .. } => {
                    // Allow single-use FieldAccess inlining — it produces
                    // clean y.fields[N] when used as IndexAccess(x, N)
                    let use_count = body_use_count!();
                    use_count != 1
                }
                _ if is_list_tail_call(&simplified_value) => true,
                _ => false,
            };
            if !is_excluded_value && !is_structural_access {
                let value_size = value_size!();
                let use_count = body_use_count!();
                // Keep force-applied helper bindings when the body force-uses them,
                // otherwise single-use inlining can recreate force(force(...)) noise.
                let force_apply_used_via_force = matches!(
                    &simplified_value,
                    PseudoExpr::Apply { function, .. }
                        if matches!(function.as_ref(), PseudoExpr::Force(_))
                ) && force_chain_use_count!(1) > 0;
                let allow_single_use_delay_inline =
                    use_count == 1 && matches!(&simplified_value, PseudoExpr::Delay(_));
                // Dispatch on `call_result_callee_for_binding_name`, not a brittle
                // `name.contains("_result")` substring match. It is the predicate
                // `record_call_result_kind_annotation` uses, so the decision matches
                // the VarKind that would be minted — without needing the annotation
                // recorded yet, since this runs before that record-call site below.
                let allow_single_use_result_inline = use_count == 1
                    && Self::call_result_callee_for_binding_name(&name, &simplified_value)
                        .is_some()
                    && !matches!(
                        &simplified_value,
                        PseudoExpr::Let { .. } | PseudoExpr::If { .. } | PseudoExpr::When { .. }
                    );
                if use_count == 1
                    && (value_size <= 4
                        || allow_single_use_delay_inline
                        || allow_single_use_result_inline)
                    && !force_apply_used_via_force
                {
                    let mut value_vars = Vec::new();
                    Self::collect_referenced_vars(&simplified_value, &mut value_vars);
                    let capture_safe = value_vars.is_empty()
                        || !Self::has_binding_for_any(&simplified_body, &value_vars);
                    if capture_safe {
                        let inlined = self.replace_forced_var(
                            simplified_body,
                            &name,
                            var_id,
                            &simplified_value,
                            0,
                        );
                        finish_let!(LetPostResult::Resimplify(inlined));
                    }
                }
            }
        }

        // Context-aware field propagation: apply the rename resolved before body
        // simplification (`pre_context_name`), so inner lets already saw the name.
        if let Some(semantic_name) = pre_context_name {
            // Avoid self-shadowing like `let x = x[0]` when the suggested semantic
            // name is already referenced by the binding value.
            if !Self::is_var_used(&simplified_value, &semantic_name) {
                let renamed_body =
                    Self::rename_var_binding(&simplified_body, &name, var_id, &semantic_name);
                // Drop the old generated name from `context_field_names`: a later variable
                // that draws the same generated name (e.g. `fields_0_2` from a different
                // `.fields[0]`) must not inherit this variable's context mapping.
                if name != semantic_name {
                    self.context.context_field_names.remove(&name);
                }
                if let Some(vid) = var_id {
                    self.naming.renames.remove(vid);
                }
                self.naming.renames.insert_binding(
                    semantic_name.clone(),
                    var_id,
                    semantic_name.clone(),
                );
                if let Some(vid) = var_id {
                    self.naming.name_to_id.insert(semantic_name.clone(), vid);
                }
                finish_let!(LetPostResult::Done(PseudoExpr::Let {
                    name: semantic_name,
                    id: Some(emitted_let_id),
                    value: PBox::new(simplified_value),
                    body: PBox::new(renamed_body),
                }));
            }
        }

        // A rename committed in an earlier fixed-point iteration is
        // never re-suggested: `is_generated_temp_name` treats any
        // digit-suffixed name as a candidate, so a deduped `int_1`
        // would drift to `int_2`, `int_3`, … on every later pass.
        let rename_already_committed = var_id
            .map(|vid| self.naming.renamed_binding_ids.contains(&vid))
            .unwrap_or(false);

        if !self.safe_mode
            && !rename_already_committed
            && let Some(pretty_name) =
                self.suggest_generated_binding_name(&name, &simplified_value, &simplified_body)
        {
            // Short type-based stems (int, bytes, map, …) collide across closures;
            // only these get global dedup — other names are distinctive enough.
            let is_short_type_stem = matches!(
                pretty_name.as_str(),
                "int" | "bytes" | "map" | "list" | "hash" | "value"
            ) || pretty_name.ends_with("_int")
                || pretty_name.ends_with("_bytes")
                || pretty_name.ends_with("_map");

            // A selector-derived stem (`fields`, from `let v = x.fields`)
            // collides across sibling ScriptContext projections:
            // `script_info.fields` and `tx_info.fields` both want the bare
            // name. `name_to_id` keeps only the innermost, so an id-less ref
            // in the outer binding resolves by name-fallback to the inner
            // one — an own-input `output_reference` comparand captured into
            // a `find` closure then reads `tx_info`'s record. Dedup the stem
            // when it is already bound in scope under a DIFFERENT id, so
            // each `.fields`/`.tag` projection keeps a distinct name the
            // fallback cannot cross.
            let selector_stem_collision = matches!(pretty_name.as_str(), "fields" | "tag")
                && self
                    .naming
                    .name_to_id
                    .get(&pretty_name)
                    .is_some_and(|existing| Some(*existing) != var_id);

            let final_name = if Self::is_var_used(&simplified_value, &pretty_name)
                || selector_stem_collision
                || (is_short_type_stem && self.global_used_names.contains(&pretty_name))
            {
                let mut used_names = std::collections::HashSet::new();
                Self::collect_var_names(&simplified_value, &mut used_names);
                Self::collect_var_names(&simplified_body, &mut used_names);
                used_names.insert(name.clone());
                if is_short_type_stem {
                    for gn in &self.global_used_names {
                        used_names.insert(gn.clone());
                    }
                }
                // For a selector-stem collision, the conflicting binding may
                // live in an OUTER scope (not referenced in this value/body),
                // so seed the taken stem explicitly to force a fresh suffix.
                if selector_stem_collision {
                    used_names.insert(pretty_name.clone());
                }
                self.fresh_name_for_scope(&mut used_names, pretty_name)
            } else {
                pretty_name
            };
            // Register short type stems in global set for cross-scope dedup
            if is_short_type_stem {
                self.global_used_names.insert(final_name.clone());
            }

            if final_name != name {
                let renamed_body =
                    Self::rename_var_binding(&simplified_body, &name, var_id, &final_name);
                if let Some(vid) = var_id {
                    self.naming.renames.remove(vid);
                }
                self.naming
                    .renames
                    .insert_binding(final_name.clone(), var_id, final_name.clone());
                if let Some(vid) = var_id {
                    self.naming.name_to_id.insert(final_name.clone(), vid);
                    // Lock this commit across future passes.
                    self.naming.renamed_binding_ids.insert(vid);
                    // CallResult mint-site: tag the binder
                    // `VarKind::CallResult` when the name ends in
                    // `_result` and the value is `Apply(Var(callee),
                    // args)` with a matching stem.
                    self.record_call_result_kind_annotation(
                        &final_name,
                        Some(vid),
                        &simplified_value,
                    );
                }
                finish_let!(LetPostResult::Done(PseudoExpr::Let {
                    name: final_name,
                    id: Some(emitted_let_id),
                    value: PBox::new(simplified_value),
                    body: PBox::new(renamed_body),
                }));
            }
        }

        // Convert: let x = when subj is { Pattern(vars) -> var_i; _ -> fail } ; body
        // Into: when subj is { Pattern(vars with var_i→x) -> body; _ -> fail }
        // This enables the pretty printer to render it as `expect Pattern = subj`.
        if !self.safe_mode
            && let Some(rewritten) = Self::try_rewrite_when_return_binding(
                &name,
                var_id,
                &simplified_value,
                &simplified_body,
            )
        {
            finish_let!(LetPostResult::Done(rewritten));
        }

        // Avoid self-shadowing in let values: `let x = x[...]` or `let x = f(x)`.
        // Rename binder to a fresh name and rewrite body references only.
        if Self::is_var_used_by_id(&simplified_value, &name, var_id) {
            let mut used_names = std::collections::HashSet::new();
            Self::collect_var_names(&simplified_value, &mut used_names);
            Self::collect_var_names(&simplified_body, &mut used_names);
            used_names.insert(name.clone());
            let fresh_name = self.fresh_name_for_scope(&mut used_names, name.clone());
            if fresh_name != name {
                let renamed_body =
                    Self::rename_var_binding(&simplified_body, &name, var_id, &fresh_name);
                if let Some(vid) = var_id {
                    self.naming.renames.remove(vid);
                }
                self.naming
                    .renames
                    .insert_binding(fresh_name.clone(), var_id, fresh_name.clone());
                if let Some(vid) = var_id {
                    self.naming.name_to_id.insert(fresh_name.clone(), vid);
                    self.record_call_result_kind_annotation(
                        &fresh_name,
                        Some(vid),
                        &simplified_value,
                    );
                }
                finish_let!(LetPostResult::Done(PseudoExpr::Let {
                    name: fresh_name,
                    id: Some(emitted_let_id),
                    value: PBox::new(simplified_value),
                    body: PBox::new(renamed_body),
                }));
            }
        }
        self.record_call_result_kind_annotation(&name, var_id, &simplified_value);
        let result = LetPostResult::Done(PseudoExpr::Let {
            name: name.clone(),
            id: Some(emitted_let_id),
            value: PBox::new(simplified_value),
            body: PBox::new(simplified_body),
        });
        self.restore_lexical_name(&name, name_shadow);
        result
    }
}
