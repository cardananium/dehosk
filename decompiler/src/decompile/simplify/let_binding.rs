//! Let binding simplification methods for Simplifier.

use crate::pseudo::ast::PBox;
mod after_body;
mod aliases;
mod boolean;
mod call_result;
mod constructors;
mod partial;
mod recursive;
mod selector_scope;
mod self_ref;
mod state;
mod when_return;

use super::Simplifier;
use super::postprocess::context_field_type_from_display_name;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::var_id::VarId;
pub(super) use state::{LetAfterBodyState, LetAfterValueState, LetPostResult, LetWalkerPhase};

impl Simplifier {
    /// Builds a Let with a concrete binding id and runs the `Walker`
    /// hooks: `pre_let` + `enter_let` + `post_let`.
    pub(super) fn simplify_let(
        &mut self,
        name: String,
        var_id: VarId,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        self.simplify(PseudoExpr::Let {
            name,
            id: Some(var_id),
            value: PBox::new(value),
            body: PBox::new(body),
        })
    }

    /// Compatibility ingress for let bindings that still carry a placeholder id.
    pub(super) fn simplify_compat_let(
        &mut self,
        name: String,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        self.simplify(PseudoExpr::Let {
            name,
            id: None,
            value: PBox::new(value),
            body: PBox::new(body),
        })
    }

    /// Analyses the raw (unsimplified) value and body, registers tracking
    /// facts on `self`, and returns the state later phases need.
    ///
    /// Called from the CPS task loop on `Enter(Let{…})`; the loop pushes
    /// `Enter(value)` next.
    pub(super) fn simplify_let_pre_process(
        &mut self,
        name: String,
        var_id: Option<VarId>,

        value: &PseudoExpr,
        body: PseudoExpr,
    ) -> LetAfterValueState {
        let var_id = var_id.or_else(|| {
            if name == "_" {
                None
            } else {
                Some(self.fresh_synthetic_binding_id())
            }
        });

        // Hide outer lexical metadata for the same source name while this
        // binding is in scope.
        let name_shadow = self.shadow_lexical_name(&name, var_id);

        // Track special function patterns BEFORE simplifying
        // (because simplify will transform the pattern)
        let is_y_comb = Self::is_y_combinator(value);
        let is_and = self.is_and_definition(value);
        let is_or = self.is_or_definition(value);

        // Check for delayed Y-combinator: delay(delay(fn(b) { ... c(c) }))
        let delayed_rec = Self::is_delayed_y_combinator(value);

        let is_delayed_fst = Self::is_delayed_fst_selector(value);
        let is_delayed_snd = Self::is_delayed_snd_selector(value);

        let is_single_delayed_fst = Self::is_single_delayed_fst_selector(value);
        let is_single_delayed_snd = Self::is_single_delayed_snd_selector(value);

        if is_y_comb {
            self.recursion.rec_vars.insert_binding(name.clone(), var_id);
        }
        if is_and {
            self.booleans.and_vars.insert_binding(name.clone(), var_id);
        }
        if is_or {
            self.booleans.or_vars.insert_binding(name.clone(), var_id);
        }

        // Track delayed patterns for force(force(var)) simplification
        if let Some(delay_count) = delayed_rec {
            self.recursion.delayed_rec_vars.insert_binding(
                name.clone(),
                var_id,
                (delay_count, value.clone()),
            );
        }
        if is_delayed_fst.is_some() {
            self.selectors
                .delayed_fst_selectors
                .insert_binding(name.clone(), var_id);
        }
        if is_delayed_snd.is_some() {
            self.selectors
                .delayed_snd_selectors
                .insert_binding(name.clone(), var_id);
        }
        if is_single_delayed_fst {
            self.selectors
                .single_delayed_fst_params
                .insert_binding(name.clone(), var_id);
        }
        if is_single_delayed_snd {
            self.selectors
                .single_delayed_snd_params
                .insert_binding(name.clone(), var_id);
        }

        // Add renames BEFORE simplifying body so they get applied
        if is_y_comb {
            let internal_name = format!("__y_comb_{}", name);
            self.naming
                .renames
                .insert_binding(name.clone(), var_id, internal_name.clone());
            self.recursion
                .rec_vars
                .insert_binding(internal_name, var_id);
        }
        if is_and {
            self.naming
                .renames
                .insert_binding(name.clone(), var_id, "and".to_string());
            self.booleans
                .and_vars
                .insert_binding("and".to_string(), var_id);
        }
        if is_or {
            self.naming
                .renames
                .insert_binding(name.clone(), var_id, "or".to_string());
            self.booleans
                .or_vars
                .insert_binding("or".to_string(), var_id);
        }

        let raw_lambda_body_size =
            matches!(value, PseudoExpr::Lambda { .. }).then(|| Self::expr_size(&body));
        let raw_flat_params =
            matches!(value, PseudoExpr::Lambda { .. }).then(|| Self::flatten_curried_params(value));
        let need_raw_call_arg_observations = matches!(value, PseudoExpr::Lambda { .. })
            && raw_lambda_body_size.unwrap_or(usize::MAX) <= 10_000
            && ((self.script_version.is_some() && !self.context.context_var_types.is_empty())
                || !self.safe_mode);
        let raw_call_arg_observations = need_raw_call_arg_observations
            .then(|| Self::collect_call_arg_observations(&body, &name, var_id));

        // Interprocedural context propagation: when every call site in the outer
        // body passes a context-typed var at param i, register that param type
        // BEFORE simplifying the lambda body so inner field accesses resolve.
        if self.script_version.is_some()
            && !self.context.context_var_types.is_empty()
            && let Some(flat_params) = raw_flat_params.as_ref()
        {
            // Call-arg observations hold only the first Var arg per call position,
            // not whole arg lists, and the body-size gate above skips the scan on
            // huge scripts, where it would be O(n²).
            if let Some(call_arg_observations) = raw_call_arg_observations.as_ref() {
                for (i, param) in flat_params.iter().enumerate() {
                    if param == "_" {
                        continue;
                    }
                    // Check if ALL call sites pass a context-typed var at position i
                    let mut consistent_type: Option<String> = None;
                    let mut consistent_name: Option<String> = None;
                    let mut all_match = true;

                    for observation in call_arg_observations {
                        if let Some(Some((arg_name, arg_id))) = observation.first_var_args.get(i) {
                            if let Some((ctx_type, sem_name)) =
                                self.get_var_context_info(arg_name, *arg_id)
                            {
                                if let Some(ref existing) = consistent_type {
                                    if &ctx_type != existing {
                                        all_match = false;
                                        break;
                                    }
                                } else {
                                    consistent_type = Some(ctx_type);
                                    consistent_name = Some(sem_name);
                                }
                            } else {
                                all_match = false;
                                break;
                            }
                        } else {
                            all_match = false;
                            break;
                        }
                    }

                    if all_match
                        && let (Some(ctx_type), Some(_sem_name)) =
                            (consistent_type, consistent_name)
                    {
                        self.context
                            .context_var_types
                            .insert(param.clone(), ctx_type.clone());
                        self.context
                            .context_field_names
                            .insert(param.clone(), param.clone());
                        // Dual-write by VarId (lambda params use name_to_id bridge)
                        if let Some(&vid) = self.naming.name_to_id.get(param) {
                            self.context
                                .context_var_types_by_id
                                .insert(vid, ctx_type.clone());
                            self.context
                                .context_field_names_by_id
                                .insert(vid, param.clone());
                            self.var_kinds.kind_annotations.insert(
                                vid,
                                crate::pseudo::nameless::VarKind::CardanoContext {
                                    context_type: ctx_type,
                                },
                            );
                        }
                    }
                }
            }
        }

        // Interprocedural CPS elimination:
        // If ALL call sites wrap arg[i] in delay() AND the function body
        // only uses param[i] via force(param[i]), mark for dethunking.
        if !self.safe_mode
            && let Some(flat_params) = raw_flat_params.as_ref()
            && raw_lambda_body_size.unwrap_or(usize::MAX) <= 10_000
            && let Some(call_arg_observations) = raw_call_arg_observations.as_ref()
        {
            // Navigate to the innermost body of the curried lambda
            let mut lambda_body: &PseudoExpr = value;
            while let PseudoExpr::Lambda { body: inner, .. } = lambda_body {
                lambda_body = inner.as_ref();
            }
            let mut dethunk_indices = std::collections::HashSet::new();

            for (i, param) in flat_params.iter().enumerate() {
                if param == "_" {
                    continue;
                }

                let all_delayed = call_arg_observations
                    .iter()
                    .all(|obs| obs.delayed_args.get(i).copied().unwrap_or(false));

                if all_delayed {
                    // Check: function body ONLY uses param via force(param)
                    let total = Self::count_var_uses(lambda_body, param);
                    let forced = Self::count_force_of_var(lambda_body, param);
                    if total > 0 && total == forced {
                        dethunk_indices.insert(i);
                    }
                }
            }

            if !dethunk_indices.is_empty() {
                self.dethunk
                    .dethunk_params
                    .insert_binding(name.clone(), var_id, dethunk_indices);
            }
        }

        LetAfterValueState {
            name,
            var_id,
            name_shadow,
            body,
            is_y_comb,
            is_and,
            is_or,
            has_delayed_rec: delayed_rec.is_some(),
            has_delayed_fst: is_delayed_fst.is_some(),
            has_delayed_snd: is_delayed_snd.is_some(),
        }
    }

    /// Performs delay-depth tracking, alias detection, partial-app tracking,
    /// context propagation, and name renaming, then returns the state for
    /// body processing with the still-unsimplified body for the task loop.
    pub(super) fn simplify_let_after_value(
        &mut self,
        state: LetAfterValueState,
        simplified_value: PseudoExpr,
    ) -> (LetAfterBodyState, PseudoExpr) {
        let name = state.name;
        let var_id = state.var_id;
        let name_shadow = state.name_shadow;
        let body = state.body;
        let is_y_comb = state.is_y_comb;
        let is_and = state.is_and;
        let is_or = state.is_or;
        let has_delayed_rec = state.has_delayed_rec;
        let has_delayed_fst = state.has_delayed_fst;
        let has_delayed_snd = state.has_delayed_snd;

        // Interprocedural CPS dethunking: Force(Var(param)) -> Var(param) in the
        // simplified Lambda body, for each param index marked in pre-processing.
        let simplified_value = if !self.safe_mode {
            if let Some(dethunk_indices) =
                self.tracked_var(&self.dethunk.dethunk_params, &name, var_id)
            {
                if let PseudoExpr::Lambda { .. } = &simplified_value {
                    let flat_params = Self::flatten_curried_param_binders(&simplified_value);
                    let mut val = simplified_value;
                    for &idx in &dethunk_indices {
                        if let Some(param) = flat_params.get(idx)
                            && param != "_"
                        {
                            val = Self::replace_force_of_var_with_id(
                                val,
                                param.as_str(),
                                param.id.get(),
                                param.as_str(),
                                param.id,
                            );
                        }
                    }
                    val
                } else {
                    simplified_value
                }
            } else {
                simplified_value
            }
        } else {
            simplified_value
        };
        let simplified_value =
            self.restore_let_value_self_refs(simplified_value, &name, var_id, &name_shadow);

        let mut delay_depth: u8 = 0;
        let mut cur = &simplified_value;
        while let PseudoExpr::Delay(inner) = cur {
            delay_depth = delay_depth.saturating_add(1);
            cur = inner.as_ref();
        }
        if delay_depth == 0
            && let PseudoExpr::Var {
                name: aliased,
                id: Some(aliased_id),
                ..
            } = &simplified_value
        {
            if let Some(aliased_depth) =
                self.tracked_var(&self.delays.delayed_value_depths, aliased, aliased_id.get())
            {
                delay_depth = aliased_depth;
            }
            if let Some((rec_delay, rec_expr)) =
                self.tracked_var(&self.recursion.delayed_rec_vars, aliased, aliased_id.get())
            {
                self.recursion.delayed_rec_vars.insert_binding(
                    name.clone(),
                    var_id,
                    (rec_delay, rec_expr),
                );
            }
            if self.tracked_binding(
                &self.selectors.delayed_fst_selectors,
                aliased,
                aliased_id.get(),
            ) {
                self.selectors
                    .delayed_fst_selectors
                    .insert_binding(name.clone(), var_id);
            }
            if self.tracked_binding(
                &self.selectors.delayed_snd_selectors,
                aliased,
                aliased_id.get(),
            ) {
                self.selectors
                    .delayed_snd_selectors
                    .insert_binding(name.clone(), var_id);
            }
            if self.tracked_binding(
                &self.selectors.single_delayed_fst_params,
                aliased,
                aliased_id.get(),
            ) {
                self.selectors
                    .single_delayed_fst_params
                    .insert_binding(name.clone(), var_id);
            }
            if self.tracked_binding(
                &self.selectors.single_delayed_snd_params,
                aliased,
                aliased_id.get(),
            ) {
                self.selectors
                    .single_delayed_snd_params
                    .insert_binding(name.clone(), var_id);
            }
            if self.tracked_binding(&self.selectors.non_thunk_vars, aliased, aliased_id.get()) {
                self.selectors
                    .non_thunk_vars
                    .insert_binding(name.clone(), var_id);
            }
            if let Some(alias_builtin) = self.builtin_alias_for_var(aliased, aliased_id.get()) {
                self.naming
                    .builtin_aliases
                    .insert_binding(name.clone(), var_id, alias_builtin);
            }
            if let Some(cond) =
                self.tracked_var(&self.booleans.partial_if_conds, aliased, aliased_id.get())
            {
                self.booleans
                    .partial_if_conds
                    .insert_binding(name.clone(), var_id, cond);
            }
            if let Some(subject) = self.tracked_var(
                &self.delays.partial_choose_list_subjects,
                aliased,
                aliased_id.get(),
            ) {
                self.delays.partial_choose_list_subjects.insert_binding(
                    name.clone(),
                    var_id,
                    subject,
                );
            }
            if let Some(unpack_subj) = self.tracked_var(
                &self.constructors.constr_unpack_subjects,
                aliased,
                aliased_id.get(),
            ) {
                self.constructors.constr_unpack_subjects.insert_binding(
                    name.clone(),
                    var_id,
                    unpack_subj,
                );
            }
            if let Some(tag_subj) = self.tracked_var(
                &self.constructors.constr_tag_subjects,
                aliased,
                aliased_id.get(),
            ) {
                self.constructors.constr_tag_subjects.insert_binding(
                    name.clone(),
                    var_id,
                    tag_subj,
                );
            }
            if let Some(tail_offset) = self.tracked_var(
                &self.constructors.tail_chain_offsets,
                aliased,
                aliased_id.get(),
            ) {
                self.constructors.tail_chain_offsets.insert_binding(
                    name.clone(),
                    var_id,
                    tail_offset,
                );
            }
            if let Some(fields_src) = self.tracked_var(
                &self.constructors.fields_bindings,
                aliased,
                aliased_id.get(),
            ) {
                self.constructors
                    .fields_bindings
                    .insert_binding(name.clone(), var_id, fields_src);
            }
        }
        if delay_depth > 0 {
            self.delays
                .delayed_value_depths
                .insert_binding(name.clone(), var_id, delay_depth);
        }

        // Check for simple builtin alias AFTER simplifying
        // e.g. let a = Pair.second -> inline 'a' as 'Pair.second'
        let is_builtin_alias =
            if let Some(builtin_name) = Self::get_simple_builtin(&simplified_value) {
                self.naming
                    .builtin_aliases
                    .insert_binding(name.clone(), var_id, builtin_name);
                true
            } else {
                false
            };

        let is_partial_app = self.track_partial_binding_facts(&name, var_id, &simplified_value);
        self.track_constructor_binding_facts(&name, var_id, &simplified_value);

        self.track_boolean_lambda_binding_facts(&name, var_id, &simplified_value, is_and, is_or);

        let (selector_entry, track_non_thunk, already_tracked_non_thunk) =
            self.track_selector_scope_binding(&name, var_id, &simplified_value);
        // Register context field names BEFORE body simplification so inner lets
        // resolve through the original binding name: `a1 = script_context.fields`
        // registers `a1` → `script_context_fields`, so `a1[0]` resolves to `tx_info`.
        let pre_context_name = if self.script_version.is_some() {
            self.resolve_context_field_name(&name, &simplified_value)
        } else {
            None
        };
        if let Some(ref semantic_name) = pre_context_name {
            self.context
                .context_field_names
                .insert(name.clone(), semantic_name.clone());
            // Register semantic name → itself (for subsequent passes)
            self.context
                .context_field_names
                .insert(semantic_name.clone(), semantic_name.clone());
            // Dual-write by VarId
            if let Some(vid) = var_id {
                self.context
                    .context_field_names_by_id
                    .insert(vid, semantic_name.clone());
            }
            // Track type for the semantic name
            if let Some(script_version) = self.script_version
                && let Some(var_type) =
                    context_field_type_from_display_name(semantic_name, script_version)
                        .map(|t| t.display_name().to_string())
            {
                self.context
                    .context_var_types
                    .insert(semantic_name.clone(), var_type.clone());
                if let Some(vid) = var_id {
                    self.context
                        .context_var_types_by_id
                        .insert(vid, var_type.clone());
                    self.var_kinds.kind_annotations.insert(
                        vid,
                        crate::pseudo::nameless::VarKind::CardanoContext {
                            context_type: var_type,
                        },
                    );
                }
            }
            if let PseudoExpr::FieldAccess {
                ref record,
                ref selector,
                ..
            } = simplified_value
                && selector.as_pretty_name() == "fields"
            {
                self.constructors.fields_bindings.insert_binding(
                    semantic_name.clone(),
                    var_id,
                    (**record).clone(),
                );
            }
        }
        // Rename auto-generated `_partial_` bindings when the value supplies a semantic
        // name: `let to_list_partial_22 = Data.to_list(tx_info.outputs)` → `outputs`.
        //
        // Bindings already renamed in an earlier iteration are skipped via
        // `renamed_binding_ids`; without that, the committed name is still in
        // `global_used_names` and every pass bumps the collision suffix again.
        let already_renamed = var_id
            .map(|vid| self.naming.renamed_binding_ids.contains(&vid))
            .unwrap_or(false);
        let name = if !already_renamed && pre_context_name.is_none() && name.contains("_partial_") {
            if let PseudoExpr::BuiltinCall {
                name: ref fn_name,
                ref args,
            } = simplified_value
            {
                if matches!(
                    fn_name.as_str(),
                    "Data.to_list"
                        | "Data.un_list"
                        | "Data.to_map"
                        | "Data.un_map"
                        | "Data.to_bytes"
                        | "Data.un_bytearray"
                        | "Data.to_int"
                        | "Data.un_int"
                ) && args.len() == 1
                {
                    // For Var sources, use composite name to avoid shadowing:
                    // Data.to_bytes(policy_id) → policy_id_bytes
                    let type_suffix = match fn_name.as_str() {
                        "Data.to_bytes" | "Data.un_bytearray" => Some("bytes"),
                        "Data.to_int" | "Data.un_int" => Some("int"),
                        _ => None, // to_list/to_map don't need suffix (content is the same type)
                    };
                    let semantic = match &args[0] {
                        PseudoExpr::FieldAccess { selector, .. } => {
                            Some(selector.as_pretty_name().to_string())
                        }
                        PseudoExpr::Var { name: var_name, .. } if type_suffix.is_some() => {
                            // Only use context-known names + type suffix
                            self.context
                                .context_field_names
                                .get(var_name)
                                .cloned()
                                .filter(|s| !s.contains("_partial_"))
                                .and_then(|base| {
                                    type_suffix.map(|suffix| format!("{}_{}", base, suffix))
                                })
                        }
                        _ => None,
                    };
                    if let Some(ref better_name) = semantic {
                        // Check local renames AND global_used_names so two Data.un_int in
                        // different scopes don't both get "int".
                        let is_taken = |n: &str| -> bool {
                            self.naming.renames.values().any(|v| v == n)
                                || self.global_used_names.contains(n)
                        };
                        let final_name = if is_taken(better_name) {
                            let mut candidate = format!("{}_2", better_name);
                            let mut suffix = 3;
                            while is_taken(&candidate) {
                                candidate = format!("{}_{}", better_name, suffix);
                                suffix += 1;
                            }
                            candidate
                        } else {
                            better_name.clone()
                        };
                        // Register in global set for cross-scope dedup
                        self.global_used_names.insert(final_name.clone());
                        // Record the commit so subsequent
                        // fixed-point iterations treat this name as final.
                        if let Some(vid) = var_id {
                            self.naming.renamed_binding_ids.insert(vid);
                        }
                        self.naming.renames.insert_binding(
                            name.clone(),
                            var_id,
                            final_name.clone(),
                        );
                        // Register in context for further propagation
                        if let Some(version) = self.script_version {
                            self.context
                                .context_field_names
                                .insert(final_name.clone(), final_name.clone());
                            // Dual-write by VarId
                            if let Some(vid) = var_id {
                                self.context
                                    .context_field_names_by_id
                                    .insert(vid, final_name.clone());
                            }
                            if let Some(var_type) =
                                context_field_type_from_display_name(&final_name, version)
                                    .map(|t| t.display_name().to_string())
                            {
                                self.context
                                    .context_var_types
                                    .insert(final_name.clone(), var_type.clone());
                                if let Some(vid) = var_id {
                                    self.context.context_var_types_by_id.insert(vid, var_type);
                                }
                            }
                        }
                        final_name
                    } else {
                        name
                    }
                } else {
                    name
                }
            } else {
                name
            }
        } else {
            name
        };

        (
            LetAfterBodyState {
                name,
                var_id,
                name_shadow,
                simplified_value,
                is_y_comb,
                is_and,
                is_or,
                has_delayed_rec,
                has_delayed_fst,
                has_delayed_snd,
                is_builtin_alias,
                is_partial_app,
                selector_entry,
                track_non_thunk,
                already_tracked_non_thunk,
                pre_context_name,
            },
            body,
        )
    }
}
