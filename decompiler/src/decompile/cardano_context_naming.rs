use crate::pseudo::ast::PBox;
use std::collections::HashMap;
use std::rc::Rc;

use super::ScriptVersion;
use super::blueprint_registry::{BlueprintHintRegistry, TypeHintId};
use super::simplify::postprocess::CardanoTypeRef;
use crate::cardano::BlueprintHints;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;

#[derive(Default)]
struct ScopeFrame {
    types_by_id: HashMap<VarId, CardanoTypeRef>,
    types_by_name: HashMap<String, CardanoTypeRef>,
}

struct ScopedTypeEnv {
    frames: Vec<ScopeFrame>,
}

impl Default for ScopedTypeEnv {
    fn default() -> Self {
        Self {
            frames: vec![ScopeFrame::default()],
        }
    }
}

impl ScopedTypeEnv {
    fn push_scope(&mut self) {
        self.frames.push(ScopeFrame::default());
    }

    fn pop_scope(&mut self) {
        debug_assert!(
            self.frames.len() > 1,
            "cardano_context_naming attempted to pop the root type scope"
        );
        if self.frames.len() > 1 {
            self.frames.pop();
        }
    }

    fn bind_var(&mut self, name: &str, id: Option<VarId>, ty: CardanoTypeRef) {
        if name == "_" {
            return;
        }
        let frame = self
            .frames
            .last_mut()
            .expect("ScopedTypeEnv always keeps a root frame");
        if let Some(vid) = id {
            frame.types_by_id.insert(vid, ty);
        }
        frame.types_by_name.insert(name.to_string(), ty);
    }

    fn bind_binder(&mut self, binder: &Binder, ty: CardanoTypeRef) {
        self.bind_var(binder.as_str(), Some(binder.var_id()), ty);
    }

    fn lookup_var(&self, name: &str, id: Option<VarId>) -> Option<CardanoTypeRef> {
        self.frames
            .iter()
            .rev()
            .find_map(|frame| id.and_then(|vid| frame.types_by_id.get(&vid).copied()))
            .or_else(|| {
                self.frames
                    .iter()
                    .rev()
                    .find_map(|frame| frame.types_by_name.get(name).copied())
            })
    }
}

// Cardano context type propagation + named field resolution
//
// `propagate_types_and_name_constructors` walks top-down, tracking types
// through `let` / `FieldAccess` / `IndexAccess`, and fills constructor
// names into `when` patterns whose subject is a known Cardano sum type.
// `resolve_cardano_field_names` converts `.#N` / `IndexAccess` / `.fst` /
// `.snd` into named field accesses via the `context_field_at` table from
// `simplify::postprocess`.
//
// Both passes must run AFTER `rename_validator_params` (so the validator
// parameter is named `script_context`) and AFTER `solve_type_constraints`.

/// Fill in constructor names on When/expect patterns whose subject type is
/// known, tracking variable types through `let` bindings and field access.
///
/// The pipeline calls the `_with_blueprint` variant; this entry passes no
/// blueprint hints and stays as a crate API for tests and diagnostics.
#[allow(dead_code)]
pub(crate) fn propagate_types_and_name_constructors(
    expr: PseudoExpr,
    version: ScriptVersion,
    registry: &mut BlueprintHintRegistry,
) -> PseudoExpr {
    propagate_types_and_name_constructors_impl(expr, version, registry, None, None)
}

/// Variant accepting blueprint hints for user-ADT field naming and a
/// kind-annotation map populated for `UserAdtField` field-binders.
pub(crate) fn propagate_types_and_name_constructors_with_blueprint(
    expr: PseudoExpr,
    version: ScriptVersion,
    registry: &mut BlueprintHintRegistry,
    blueprint_hints: Option<&BlueprintHints>,
    kind_annotations: &mut HashMap<VarId, VarKind>,
) -> PseudoExpr {
    propagate_types_and_name_constructors_impl(
        expr,
        version,
        registry,
        blueprint_hints,
        Some(kind_annotations),
    )
}

fn propagate_types_and_name_constructors_impl(
    expr: PseudoExpr,
    version: ScriptVersion,
    registry: &mut BlueprintHintRegistry,
    blueprint_hints: Option<&BlueprintHints>,
    kind_annotations: Option<&mut HashMap<VarId, VarKind>>,
) -> PseudoExpr {
    use crate::decompile::simplify::postprocess::{
        CardanoTypeRef, ContextField, ContextType, ListCombinatorShape, SumTypeId,
        builtin_cardano_return, context_field_at, context_field_type_from_display_name,
        context_field_type_full, list_combinator_element_param_index, sum_type_constructor_names,
    };
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;
    use crate::pseudo::fold::{ExprFolder, FoldAction};

    struct TypePropagator<'a> {
        var_types: ScopedTypeEnv,
        version: ScriptVersion,
        registry: &'a mut BlueprintHintRegistry,
        blueprint_hints: Option<&'a BlueprintHints>,
        kind_annotations: Option<&'a mut HashMap<VarId, VarKind>>,
    }

    impl<'a> TypePropagator<'a> {
        fn bind_inferred_type(&mut self, name: &str, id: Option<VarId>, value: &PseudoExpr) {
            if let Some(ty) = self.infer_type(value) {
                self.var_types.bind_var(name, id, ty);
            } else if let PseudoExpr::Var {
                name: source,
                id: source_id,
            } = value
                && let Some(ty) = self.var_types.lookup_var(source, *source_id)
            {
                self.var_types.bind_var(name, id, ty);
            }
        }

        /// Infer a value's Cardano type, list-aware.
        fn infer_type(&self, value: &PseudoExpr) -> Option<CardanoTypeRef> {
            fn children<'e>(node: &'e PseudoExpr, out: &mut Vec<&'e PseudoExpr>) {
                match node {
                    PseudoExpr::FieldAccess { record, .. } => out.push(record),
                    PseudoExpr::IndexAccess { collection, .. } => out.push(collection),
                    PseudoExpr::BuiltinCall { args, .. } => out.extend(args.iter()),
                    PseudoExpr::Apply { function, args } => {
                        if let PseudoExpr::BuiltinCall {
                            args: builtin_args, ..
                        } = function.as_ref()
                        {
                            out.extend(builtin_args.iter());
                            out.extend(args.iter());
                        }
                    }
                    _ => {}
                }
            }

            // Post-order: revisit a popped node a second time (marked
            // `true`) only after its children have all been queued and
            // resolved, so `order` ends up child-before-parent. Children
            // are pushed reversed so they still get processed left to
            // right.
            let mut order: Vec<&PseudoExpr> = Vec::new();
            let mut stack: Vec<(&PseudoExpr, bool)> = vec![(value, false)];
            while let Some((node, expanded)) = stack.pop() {
                if expanded {
                    order.push(node);
                    continue;
                }
                stack.push((node, true));
                let mut kids = Vec::new();
                children(node, &mut kids);
                for kid in kids.into_iter().rev() {
                    stack.push((kid, false));
                }
            }

            let mut results: HashMap<*const PseudoExpr, Option<CardanoTypeRef>> =
                HashMap::with_capacity(order.len());
            for node in order {
                let get = |e: &PseudoExpr| -> Option<CardanoTypeRef> {
                    results.get(&(e as *const PseudoExpr)).copied().flatten()
                };
                let computed = self.infer_type_node(node, &get);
                results.insert(node as *const PseudoExpr, computed);
            }
            results
                .get(&(value as *const PseudoExpr))
                .copied()
                .flatten()
        }

        /// One node's worth of `infer_type`'s original logic, with
        /// recursive calls replaced by `get`, a memo lookup of an
        /// already-computed child result. See `infer_type`.
        fn infer_type_node(
            &self,
            value: &PseudoExpr,
            get: &dyn Fn(&PseudoExpr) -> Option<CardanoTypeRef>,
        ) -> Option<CardanoTypeRef> {
            match value {
                PseudoExpr::FieldAccess {
                    record, selector, ..
                } => {
                    let field = selector.as_pretty_name();
                    // Prefer the *full* (list-aware) field type so
                    // collection fields keep their list element info.
                    if let Some(parent_type) = get(record) {
                        if parent_type.record().is_some()
                            && let Some(field_id) = ContextField::from_display_name(field)
                            && let Some(full) = context_field_type_full(field_id, self.version)
                        {
                            return Some(full);
                        }
                        if let Some(ty) = context_field_type_from_display_name(field, self.version)
                        {
                            return Some(CardanoTypeRef::from_field_type_ref(ty));
                        }
                    }
                    // No known parent — try the field name in isolation.
                    if let Some(field_id) = ContextField::from_display_name(field)
                        && let Some(full) = context_field_type_full(field_id, self.version)
                    {
                        return Some(full);
                    }
                    context_field_type_from_display_name(field, self.version)
                        .map(CardanoTypeRef::from_field_type_ref)
                }
                PseudoExpr::IndexAccess { collection, index } => {
                    // If collection is x.fields and x has known type, resolve the field type
                    if let PseudoExpr::FieldAccess {
                        record, selector, ..
                    } = collection.as_ref()
                        && selector.as_pretty_name() == "fields"
                        && let Some(parent_type) = get(record)
                    {
                        return parent_type
                            .record()
                            .and_then(|t| context_field_at(t, *index, self.version))
                            .and_then(|field| context_field_type_full(field, self.version));
                    }
                    // Indexing a list-typed collection: element type.
                    if let Some(elem) = get(collection).and_then(|t| t.element_type()) {
                        let _ = index; // index value not needed for element type
                        return Some(elem);
                    }
                    None
                }
                PseudoExpr::BuiltinCall { name, args } => {
                    // Resolve Cardano-aware returns for list combinators
                    // and pair projections (List.head, List.tail,
                    // Pair.first, Pair.second).
                    let arg_types: Vec<Option<CardanoTypeRef>> =
                        args.iter().map(|a| get(a)).collect();
                    builtin_cardano_return(*name, &arg_types)
                }
                PseudoExpr::Apply { function, args } => {
                    // Some passes emit Apply(BuiltinCall, args), so
                    // `List.head(inputs)` resolves through that form.
                    if let PseudoExpr::BuiltinCall {
                        name,
                        args: builtin_args,
                    } = function.as_ref()
                    {
                        // Combine the curried builtin args with the
                        // outer apply args.
                        let mut combined: Vec<Option<CardanoTypeRef>> =
                            builtin_args.iter().map(|a| get(a)).collect();
                        combined.extend(args.iter().map(|a| get(a)));
                        return builtin_cardano_return(*name, &combined);
                    }
                    None
                }
                PseudoExpr::Var { name, id } => self.var_types.lookup_var(name, *id),
                _ => None,
            }
        }

        fn register_pattern_bindings(
            &mut self,
            pattern: &WhenPattern,
            subject_type: CardanoTypeRef,
        ) {
            if let WhenPattern::Constructor { fields, .. } = pattern {
                let Some(parent) = subject_type.record() else {
                    return;
                };
                for (index, field_binder) in fields.iter().enumerate() {
                    let Some(field_id) = context_field_at(parent, index, self.version) else {
                        continue;
                    };
                    // Prefer the full (list-aware) type when available; the
                    // by-name fallback loses the list wrapper.
                    if let Some(full) = context_field_type_full(field_id, self.version) {
                        self.var_types.bind_binder(field_binder, full);
                    } else if let Some(field_type) =
                        context_field_type_from_display_name(field_id.display_name(), self.version)
                    {
                        self.var_types.bind_binder(
                            field_binder,
                            CardanoTypeRef::from_field_type_ref(field_type),
                        );
                    }
                }
            }
        }

        /// Annotate field-binders with `VarKind::UserAdtField`
        /// when the pattern's `TypeHintId` names a user-ADT in
        /// `blueprint_hints.types`. Cardano-schema sum types are
        /// excluded; `record_cardano_context_kind` owns those.
        fn register_user_adt_field_bindings(&mut self, pattern: &WhenPattern) {
            let WhenPattern::Constructor {
                fields,
                tag,
                type_hint,
                ..
            } = pattern
            else {
                return;
            };
            let Some(type_hint) = type_hint else { return };
            let Some(hints) = self.blueprint_hints else {
                return;
            };
            let type_name = type_hint.as_str();
            // Skip if this TypeHintId is actually a Cardano-schema sum
            // type — those flow through `register_pattern_bindings` and
            // `record_cardano_context_kind` separately.
            if SumTypeId::from_display_name(type_name).is_some()
                || ContextType::from_display_name(type_name).is_some()
            {
                return;
            }
            if !hints.types.contains_key(type_name) {
                return;
            }
            let field_names = hints.get_field_names(type_name, *tag);
            let Some(kind_annotations) = self.kind_annotations.as_deref_mut() else {
                return;
            };
            for (field_binder, slot) in fields.iter().zip(field_names.iter()) {
                let Some(field_name) = slot.as_ref() else {
                    continue;
                };
                if field_name.is_empty() {
                    continue;
                }
                let id = field_binder.var_id();
                // First write wins: an upstream populator may already
                // have annotated this binder.
                kind_annotations
                    .entry(id)
                    .or_insert_with(|| VarKind::UserAdtField {
                        type_name: type_name.to_string(),
                        field_name: field_name.clone(),
                    });
            }
        }

        fn constructor_hint(
            &mut self,
            subject_type: Option<CardanoTypeRef>,
        ) -> Option<(TypeHintId, &'static [&'static str])> {
            let sum = subject_type?.sum()?;
            let ctor_names = sum_type_constructor_names(sum, self.version)?;
            let hint = TypeHintId::new(Rc::<str>::from(sum.display_name()));
            for (tag, ctor_name) in ctor_names.iter().enumerate() {
                self.registry.register_user(hint.clone(), tag, *ctor_name);
            }
            Some((hint, ctor_names))
        }

        fn annotate_pattern(
            &self,
            pattern: WhenPattern,
            constructor_hint: Option<&(TypeHintId, &'static [&'static str])>,
        ) -> WhenPattern {
            let Some((type_hint, ctor_names)) = constructor_hint else {
                return pattern;
            };

            match pattern {
                WhenPattern::Constructor {
                    type_hint: existing_hint,
                    tag,
                    fields,
                    shape,
                } => {
                    if shape.is_known() {
                        WhenPattern::Constructor {
                            type_hint: existing_hint,
                            tag,
                            fields,
                            shape,
                        }
                    } else if let Some(&ctor_name) = ctor_names.get(tag) {
                        let shape =
                            ConstructorShape::from_name_and_tag(Some(ctor_name), tag, fields.len());
                        WhenPattern::Constructor {
                            type_hint: Some(type_hint.clone()),
                            tag,
                            fields,
                            shape,
                        }
                    } else {
                        WhenPattern::Constructor {
                            type_hint: existing_hint,
                            tag,
                            fields,
                            shape,
                        }
                    }
                }
                other => other,
            }
        }

        /// Fold an `Apply { function: Var, args }` as a known
        /// list-combinator call, binding the callback's element
        /// parameter to the list's Cardano element type before
        /// folding its body.
        ///
        /// `None` if the name does not match or the element type
        /// is unknown; the caller falls back to the generic walk.
        fn try_fold_list_combinator_apply(
            &mut self,
            function: &PseudoExpr,
            args: &[PseudoExpr],
        ) -> Option<PseudoExpr> {
            let PseudoExpr::Var { name, .. } = function else {
                return None;
            };
            let shape: ListCombinatorShape = list_combinator_element_param_index(name.as_str())?;
            if args.len() <= shape.callback_arg_index {
                return None;
            }
            // Only fire on a *known* Cardano element type
            // (ListOfRecords / ListOfSums); List<Data> and
            // List<Unknown> bind nothing meaningful.
            let element_ty: CardanoTypeRef = self
                .infer_type(&args[shape.list_arg_index])
                .and_then(|t| t.element_type())?;

            let folded_function = self.fold(function.clone());
            let folded_args: Vec<PseudoExpr> = args
                .iter()
                .cloned()
                .enumerate()
                .map(|(idx, arg)| {
                    if idx != shape.callback_arg_index {
                        return self.fold(arg);
                    }
                    let PseudoExpr::Lambda { params, body } = arg else {
                        return self.fold(arg);
                    };
                    // Manually push scope (mirroring enter_lambda) and
                    // bind the element param before folding the body.
                    self.var_types.push_scope();
                    if let Some(param) = params.get(shape.element_param_index) {
                        self.var_types.bind_binder(param, element_ty);
                    }
                    let body = self.fold(body.into_inner());
                    self.var_types.pop_scope();
                    PseudoExpr::Lambda {
                        params,
                        body: PBox::new(body),
                    }
                })
                .collect();

            Some(PseudoExpr::Apply {
                function: PBox::new(folded_function),
                args: folded_args.into(),
            })
        }

        fn fold_when_scoped(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            let subject = self.fold(subject);
            let subject_type = self.infer_type(&subject);
            let constructor_hint = self.constructor_hint(subject_type);

            self.var_types.push_scope();
            if let (Some(subject_name), Some(subject_type)) = (subject_name.as_ref(), subject_type)
            {
                self.var_types.bind_binder(subject_name, subject_type);
            }

            let clauses = clauses
                .into_iter()
                .map(|clause| {
                    self.var_types.push_scope();
                    let pattern = self.fold_pattern(clause.pattern);
                    if let Some(subject_type) = subject_type {
                        self.register_pattern_bindings(&pattern, subject_type);
                    }
                    // User-ADT field naming from the pattern's own
                    // `TypeHintId`; runs regardless of subject_type,
                    // so patterns over an uninferable subject (e.g.
                    // Data) still get blueprint field names.
                    self.register_user_adt_field_bindings(&pattern);
                    let guard = clause.guard.map(|guard| self.fold(guard));
                    let body = self.fold(clause.body);
                    self.var_types.pop_scope();
                    let pattern = self.annotate_pattern(pattern, constructor_hint.as_ref());
                    // Re-run after `annotate_pattern`, which may attach
                    // a Cardano-schema `TypeHintId`; the early
                    // `SumTypeId::from_display_name` skip keeps those out.
                    self.register_user_adt_field_bindings(&pattern);
                    WhenClause {
                        pattern,
                        guard,
                        body,
                    }
                })
                .collect();

            self.var_types.pop_scope();
            PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses,
            }
        }
    }

    impl<'a> ExprFolder for TypePropagator<'a> {
        /// Intercept a list-combinator call before the descent: the callback's
        /// element parameter has to be bound to the list's Cardano element type
        /// before its body is folded.
        ///
        /// Hooks rather than a `fold` override — both take the arguments by
        /// reference already, so nothing is cloned, and the driver keeps the
        /// descent instead of putting the subtree back on the call stack.
        fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
            let PseudoExpr::Apply { function, args } = expr else {
                return FoldAction::Walk;
            };
            match self.try_fold_list_combinator_apply(function, args) {
                Some(rebuilt) => FoldAction::Replace(rebuilt),
                None => FoldAction::Walk,
            }
        }

        /// A `when`'s clause bodies are folded with the subject's Cardano type
        /// and the pattern's payload binders in scope.
        fn fold_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            self.fold_when_scoped(subject, subject_name, clauses)
        }

        fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
            self.var_types.push_scope();
            // Seed the validator entry's `script_context` param with its type so
            // ScriptContext-rooted constructor naming fires; without it the
            // `when purpose is { … }` arms stay `Unknown_S_<n>` instead of
            // Minting/Spending/Rewarding/Certifying.
            for p in params {
                if p == "script_context" {
                    self.var_types
                        .bind_binder(p, CardanoTypeRef::Record(ContextType::ScriptContext));
                }
            }
            params.to_vec()
        }

        fn exit_lambda(&mut self, _params: &[Binder]) {
            self.var_types.pop_scope();
        }

        fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
            self.var_types.push_scope();
            for p in params {
                if p == "script_context" {
                    self.var_types
                        .bind_binder(p, CardanoTypeRef::Record(ContextType::ScriptContext));
                }
            }
            (name.clone(), params.to_vec())
        }

        fn exit_recfn(&mut self, _name: &Binder, _params: &[Binder]) {
            self.var_types.pop_scope();
        }

        fn enter_let(&mut self, name: &str, id: &Option<VarId>, value: &PseudoExpr) -> String {
            self.var_types.push_scope();
            self.bind_inferred_type(name, *id, value);
            name.to_string()
        }

        fn exit_let(&mut self, _name: &str) {
            self.var_types.pop_scope();
        }
    }

    let mut propagator = TypePropagator {
        var_types: ScopedTypeEnv::default(),
        version,
        registry,
        blueprint_hints,
        kind_annotations,
    };
    propagator.fold(expr)
}

/// Rewrite numeric field access (`.#N`) and `IndexAccess` to named
/// Cardano fields, using `context_field_at` on the parent's context
/// type. Types are seeded from the `script_context` parameter and
/// tracked through let-bindings, field accesses and When patterns.
///
/// Must run AFTER `rename_validator_params` (so the parameter is named
/// `script_context`) and AFTER `propagate_types_and_name_constructors`.
///
/// The pipeline calls `resolve_cardano_field_names_with_var_kinds`; this
/// entry stays as a crate API for tests and diagnostics.
#[allow(dead_code)]
pub(crate) fn resolve_cardano_field_names(expr: PseudoExpr, version: ScriptVersion) -> PseudoExpr {
    resolve_cardano_field_names_impl(expr, version, None)
}

pub(crate) fn resolve_cardano_field_names_with_var_kinds(
    expr: PseudoExpr,
    version: ScriptVersion,
    kind_annotations: &mut HashMap<VarId, VarKind>,
) -> PseudoExpr {
    resolve_cardano_field_names_impl(expr, version, Some(kind_annotations))
}

fn resolve_cardano_field_names_impl(
    expr: PseudoExpr,
    version: ScriptVersion,
    kind_annotations: Option<&mut HashMap<VarId, VarKind>>,
) -> PseudoExpr {
    use crate::decompile::simplify::postprocess::{
        CardanoTypeRef, ContextField, ContextType, ListCombinatorShape, builtin_cardano_return,
        context_field_at, context_field_type_from_display_name, context_field_type_full,
        list_combinator_element_param_index,
    };
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::field_selector::FieldSelector;
    use crate::pseudo::fold::{ExprFolder, FoldAction};

    struct CardanoFieldResolver<'a> {
        var_types: ScopedTypeEnv,
        version: ScriptVersion,
        kind_annotations: Option<&'a mut HashMap<VarId, VarKind>>,
    }

    impl CardanoFieldResolver<'_> {
        fn record_cardano_context_kind(
            &mut self,
            id: VarId,
            context_type: CardanoTypeRef,
            binder_name: &str,
        ) {
            let Some(kind_annotations) = self.kind_annotations.as_deref_mut() else {
                return;
            };
            // List variants have no scalar Cardano-context name and
            // would render as `list<tx_in_info>`, an invalid
            // identifier; the binder name comes from elsewhere (e.g.
            // the field name on the let-binding RHS).
            if matches!(
                context_type,
                CardanoTypeRef::ListOfRecords(_) | CardanoTypeRef::ListOfSums(_)
            ) {
                return;
            }
            // Do not stamp the CardanoContext kind on a `datum`
            // or `redeemer` validator-entry slot, even when the
            // body uses it like a context (e.g. passes it to a
            // helper that projects `.tx_info`): it and
            // `script_context` would then share a context_type,
            // collide in `assign_names::candidate_name` dedup, and
            // one would be suffixed to `script_context_1`. The
            // `script_context` slot IS tagged here — this is the
            // canonical site for that kind.
            if matches!(binder_name, "datum" | "redeemer") {
                return;
            }
            kind_annotations
                .entry(id)
                .or_insert_with(|| VarKind::CardanoContext {
                    context_type: context_type.display_name(),
                });
        }

        fn bind_var_with_kind(&mut self, name: &str, id: Option<VarId>, ty: CardanoTypeRef) {
            self.var_types.bind_var(name, id, ty);
            if let Some(real_id) = id {
                self.record_cardano_context_kind(real_id, ty, name);
            }
        }

        fn bind_binder_with_kind(&mut self, binder: &Binder, ty: CardanoTypeRef) {
            self.var_types.bind_binder(binder, ty);
            self.record_cardano_context_kind(binder.var_id(), ty, binder.as_str());
        }

        fn bind_inferred_type(&mut self, name: &str, id: Option<VarId>, expr: &PseudoExpr) {
            if let Some(ty) = self.infer_type(expr) {
                self.bind_var_with_kind(name, id, ty);
            } else if let PseudoExpr::Var {
                name: source,
                id: source_id,
            } = expr
                && let Some(ty) = self.var_types.lookup_var(source, *source_id)
            {
                self.bind_var_with_kind(name, id, ty);
            }
        }

        /// Infer a value's Cardano type, list-aware.
        fn infer_type(&self, expr: &PseudoExpr) -> Option<CardanoTypeRef> {
            fn children<'e>(node: &'e PseudoExpr, out: &mut Vec<&'e PseudoExpr>) {
                match node {
                    PseudoExpr::FieldAccess { record, .. } => out.push(record),
                    PseudoExpr::IndexAccess { collection, .. } => out.push(collection),
                    PseudoExpr::BuiltinCall { args, .. } => out.extend(args.iter()),
                    PseudoExpr::Apply { function, args } => {
                        if let PseudoExpr::BuiltinCall {
                            args: builtin_args, ..
                        } = function.as_ref()
                        {
                            out.extend(builtin_args.iter());
                            out.extend(args.iter());
                        }
                    }
                    _ => {}
                }
            }

            let mut order: Vec<&PseudoExpr> = Vec::new();
            let mut stack: Vec<(&PseudoExpr, bool)> = vec![(expr, false)];
            while let Some((node, expanded)) = stack.pop() {
                if expanded {
                    order.push(node);
                    continue;
                }
                stack.push((node, true));
                let mut kids = Vec::new();
                children(node, &mut kids);
                for kid in kids.into_iter().rev() {
                    stack.push((kid, false));
                }
            }

            let mut results: HashMap<*const PseudoExpr, Option<CardanoTypeRef>> =
                HashMap::with_capacity(order.len());
            for node in order {
                let get = |e: &PseudoExpr| -> Option<CardanoTypeRef> {
                    results.get(&(e as *const PseudoExpr)).copied().flatten()
                };
                let computed = self.infer_type_node(node, &get);
                results.insert(node as *const PseudoExpr, computed);
            }
            results.get(&(expr as *const PseudoExpr)).copied().flatten()
        }

        /// One node's worth of `infer_type`'s original logic; see
        /// `infer_type` and its sibling in `TypePropagator`.
        fn infer_type_node(
            &self,
            expr: &PseudoExpr,
            get: &dyn Fn(&PseudoExpr) -> Option<CardanoTypeRef>,
        ) -> Option<CardanoTypeRef> {
            match expr {
                PseudoExpr::Var { name, id } => self.var_types.lookup_var(name, *id),
                PseudoExpr::FieldAccess {
                    record, selector, ..
                } => {
                    let field = selector.as_pretty_name();
                    // Prefer the full (list-aware) field type if the field
                    // name is a known ContextField.
                    if let Some(field_id) = ContextField::from_display_name(field)
                        && let Some(full) = context_field_type_full(field_id, self.version)
                    {
                        return Some(full);
                    }
                    // If the field itself maps to a known Cardano sub-type, use it
                    if let Some(ty) = context_field_type_from_display_name(field, self.version) {
                        return Some(CardanoTypeRef::from_field_type_ref(ty));
                    }
                    // If the parent has a known type, try to resolve field → sub-type
                    if let Some(_parent_type) = get(record) {
                        return context_field_type_from_display_name(field, self.version)
                            .map(CardanoTypeRef::from_field_type_ref);
                    }
                    None
                }
                PseudoExpr::IndexAccess {
                    collection,
                    index: _,
                } => {
                    // Indexing into a list-typed collection: produce the
                    // element type.
                    get(collection).and_then(|t| t.element_type())
                }
                PseudoExpr::BuiltinCall { name, args } => {
                    let arg_types: Vec<Option<CardanoTypeRef>> =
                        args.iter().map(|a| get(a)).collect();
                    builtin_cardano_return(*name, &arg_types)
                }
                PseudoExpr::Apply { function, args } => {
                    if let PseudoExpr::BuiltinCall {
                        name,
                        args: builtin_args,
                    } = function.as_ref()
                    {
                        let mut combined: Vec<Option<CardanoTypeRef>> =
                            builtin_args.iter().map(|a| get(a)).collect();
                        combined.extend(args.iter().map(|a| get(a)));
                        return builtin_cardano_return(*name, &combined);
                    }
                    None
                }
                _ => None,
            }
        }

        /// Parse a `#N` field name to a 0-based index (e.g. "#1" → 0, "#2" → 1).
        fn parse_hash_index(field: &str) -> Option<usize> {
            field
                .strip_prefix('#')?
                .parse::<usize>()
                .ok()
                .map(|n| n.saturating_sub(1))
        }

        /// Determine the Cardano type of the record in a field/index access.
        fn record_type(&self, record: &PseudoExpr) -> Option<CardanoTypeRef> {
            fn children<'e>(node: &'e PseudoExpr, out: &mut Vec<&'e PseudoExpr>) {
                match node {
                    PseudoExpr::BuiltinCall { args, .. } => out.extend(args.iter()),
                    PseudoExpr::Apply { function, args } => {
                        if let PseudoExpr::BuiltinCall {
                            args: builtin_args, ..
                        } = function.as_ref()
                        {
                            out.extend(builtin_args.iter());
                            out.extend(args.iter());
                        } else {
                            // Fallback chain: `f()()()` peels one `function`
                            // layer per level.
                            out.push(function);
                        }
                    }
                    _ => {}
                }
            }

            let mut order: Vec<&PseudoExpr> = Vec::new();
            let mut stack: Vec<(&PseudoExpr, bool)> = vec![(record, false)];
            while let Some((node, expanded)) = stack.pop() {
                if expanded {
                    order.push(node);
                    continue;
                }
                stack.push((node, true));
                let mut kids = Vec::new();
                children(node, &mut kids);
                for kid in kids.into_iter().rev() {
                    stack.push((kid, false));
                }
            }

            let mut results: HashMap<*const PseudoExpr, Option<CardanoTypeRef>> =
                HashMap::with_capacity(order.len());
            for node in order {
                let get = |e: &PseudoExpr| -> Option<CardanoTypeRef> {
                    results.get(&(e as *const PseudoExpr)).copied().flatten()
                };
                let computed = self.record_type_node(node, &get);
                results.insert(node as *const PseudoExpr, computed);
            }
            results
                .get(&(record as *const PseudoExpr))
                .copied()
                .flatten()
        }

        /// One node's worth of `record_type`'s original logic; see
        /// `record_type`.
        fn record_type_node(
            &self,
            record: &PseudoExpr,
            get: &dyn Fn(&PseudoExpr) -> Option<CardanoTypeRef>,
        ) -> Option<CardanoTypeRef> {
            match record {
                PseudoExpr::Var { name, id } => self.var_types.lookup_var(name, *id),
                PseudoExpr::FieldAccess { selector, .. } => {
                    let field = selector.as_pretty_name();
                    if let Some(field_id) = ContextField::from_display_name(field)
                        && let Some(full) = context_field_type_full(field_id, self.version)
                    {
                        return Some(full);
                    }
                    context_field_type_from_display_name(field, self.version)
                        .map(CardanoTypeRef::from_field_type_ref)
                }
                PseudoExpr::BuiltinCall { name, args } => {
                    // Pair.first / Pair.second / List.head returns whose
                    // Cardano shape is recoverable from the arg types.
                    let arg_types: Vec<Option<CardanoTypeRef>> =
                        args.iter().map(|a| get(a)).collect();
                    builtin_cardano_return(*name, &arg_types)
                }
                PseudoExpr::Apply { function, args } => {
                    if let PseudoExpr::BuiltinCall {
                        name,
                        args: builtin_args,
                    } = function.as_ref()
                    {
                        let mut combined: Vec<Option<CardanoTypeRef>> =
                            builtin_args.iter().map(|a| get(a)).collect();
                        combined.extend(args.iter().map(|a| get(a)));
                        return builtin_cardano_return(*name, &combined);
                    }
                    // Fall back: fn_call() — check the function var.
                    get(function)
                }
                PseudoExpr::IndexAccess {
                    collection,
                    index: _,
                } => self.infer_type(collection).and_then(|t| t.element_type()),
                _ => None,
            }
        }

        /// Register field bindings from a When pattern whose subject has a known type.
        ///
        /// Matching a `script_context` subject with `Constr<0>(field_0, field_1)`
        /// registers field_0 → "tx_info", field_1 → "purpose" (V2).
        fn register_pattern_bindings(
            &mut self,
            pattern: &WhenPattern,
            subject_type: CardanoTypeRef,
        ) {
            if let WhenPattern::Constructor { fields, .. } = pattern {
                let Some(parent) = subject_type.record() else {
                    return;
                };
                for (index, field_binder) in fields.iter().enumerate() {
                    let Some(field_id) = context_field_at(parent, index, self.version) else {
                        continue;
                    };
                    if let Some(full) = context_field_type_full(field_id, self.version) {
                        self.bind_binder_with_kind(field_binder, full);
                    } else if let Some(field_type) =
                        context_field_type_from_display_name(field_id.display_name(), self.version)
                    {
                        self.bind_binder_with_kind(
                            field_binder,
                            CardanoTypeRef::from_field_type_ref(field_type),
                        );
                    }
                }
            }
        }

        /// Same idea as `TypePropagator::try_fold_list_combinator_apply`,
        /// but additionally records a `VarKind::CardanoContext` annotation
        /// for the bound lambda parameter via `bind_binder_with_kind`, so
        /// the field-name pass can resolve `.#N` on it downstream.
        fn try_fold_list_combinator_apply(
            &mut self,
            function: &PseudoExpr,
            args: &[PseudoExpr],
        ) -> Option<PseudoExpr> {
            let PseudoExpr::Var { name, .. } = function else {
                return None;
            };
            let shape: ListCombinatorShape = list_combinator_element_param_index(name.as_str())?;
            if args.len() <= shape.callback_arg_index {
                return None;
            }
            let element_ty: CardanoTypeRef = self
                .infer_type(&args[shape.list_arg_index])
                .and_then(|t| t.element_type())?;

            let folded_function = self.fold(function.clone());
            let folded_args: Vec<PseudoExpr> = args
                .iter()
                .cloned()
                .enumerate()
                .map(|(idx, arg)| {
                    if idx != shape.callback_arg_index {
                        return self.fold(arg);
                    }
                    let PseudoExpr::Lambda { params, body } = arg else {
                        return self.fold(arg);
                    };
                    self.var_types.push_scope();
                    if let Some(param) = params.get(shape.element_param_index) {
                        self.bind_binder_with_kind(param, element_ty);
                    }
                    let body = self.fold(body.into_inner());
                    self.var_types.pop_scope();
                    PseudoExpr::Lambda {
                        params,
                        body: PBox::new(body),
                    }
                })
                .collect();

            Some(PseudoExpr::Apply {
                function: PBox::new(folded_function),
                args: folded_args.into(),
            })
        }

        fn fold_when_scoped(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            let subject = self.fold(subject);
            let subject_type = self.infer_type(&subject);

            self.var_types.push_scope();
            if let (Some(subject_name), Some(subject_type)) = (subject_name.as_ref(), subject_type)
            {
                self.var_types.bind_binder(subject_name, subject_type);
            }

            let clauses = clauses
                .into_iter()
                .map(|clause| {
                    self.var_types.push_scope();
                    let pattern = self.fold_pattern(clause.pattern);
                    if let Some(subject_type) = subject_type {
                        self.register_pattern_bindings(&pattern, subject_type);
                    }
                    let guard = clause.guard.map(|guard| self.fold(guard));
                    let body = self.fold(clause.body);
                    self.var_types.pop_scope();
                    WhenClause {
                        pattern,
                        guard,
                        body,
                    }
                })
                .collect();

            self.var_types.pop_scope();
            PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses,
            }
        }
    }

    impl ExprFolder for CardanoFieldResolver<'_> {
        /// Intercept a list-combinator call before the descent: the callback's
        /// element parameter has to be bound to the list's Cardano element type
        /// before its body is folded.
        ///
        /// Hooks rather than a `fold` override — both take the arguments by
        /// reference already, so nothing is cloned, and the driver keeps the
        /// descent instead of putting the subtree back on the call stack.
        fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
            let PseudoExpr::Apply { function, args } = expr else {
                return FoldAction::Walk;
            };
            match self.try_fold_list_combinator_apply(function, args) {
                Some(rebuilt) => FoldAction::Replace(rebuilt),
                None => FoldAction::Walk,
            }
        }

        /// A `when`'s clause bodies are folded with the subject's Cardano type
        /// and the pattern's payload binders in scope.
        fn fold_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            self.fold_when_scoped(subject, subject_name, clauses)
        }

        fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
            self.var_types.push_scope();
            for p in params {
                if p == "script_context" {
                    self.bind_binder_with_kind(
                        p,
                        CardanoTypeRef::Record(ContextType::ScriptContext),
                    );
                }
            }
            params.to_vec()
        }

        fn exit_lambda(&mut self, _params: &[Binder]) {
            self.var_types.pop_scope();
        }

        fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
            self.var_types.push_scope();
            for param in params {
                if param == "script_context" {
                    self.bind_binder_with_kind(
                        param,
                        CardanoTypeRef::Record(ContextType::ScriptContext),
                    );
                }
            }
            (name.clone(), params.to_vec())
        }

        fn exit_recfn(&mut self, _name: &Binder, _params: &[Binder]) {
            self.var_types.pop_scope();
        }

        fn enter_let(&mut self, name: &str, id: &Option<VarId>, value: &PseudoExpr) -> String {
            self.var_types.push_scope();
            self.bind_inferred_type(name, *id, value);
            name.to_string()
        }

        fn exit_let(&mut self, _name: &str) {
            self.var_types.pop_scope();
        }

        fn post_field_access(&mut self, record: PseudoExpr, selector: FieldSelector) -> PseudoExpr {
            // Convert .#N to named field when record has a known Cardano type
            if let Some(index) = Self::parse_hash_index(selector.as_pretty_name())
                && let Some(parent_type) = self.record_type(&record)
                && let Some(field_name) = parent_type
                    .record()
                    .and_then(|t| context_field_at(t, index, self.version))
            {
                return PseudoExpr::field_access(record, field_name.display_name());
            }
            // Also handle .fst/.snd on known pair-like types:
            // `script_context.fst` → `script_context.tx_info` (for V1/V2 where fst is index 0)
            if selector.is_pair_fst()
                && let Some(parent_type) = self.record_type(&record)
                && let Some(field_name) = parent_type
                    .record()
                    .and_then(|t| context_field_at(t, 0, self.version))
            {
                return PseudoExpr::field_access(record, field_name.display_name());
            }
            if selector.is_pair_snd()
                && let Some(parent_type) = self.record_type(&record)
                && let Some(field_name) = parent_type
                    .record()
                    .and_then(|t| context_field_at(t, 1, self.version))
            {
                return PseudoExpr::field_access(record, field_name.display_name());
            }
            PseudoExpr::field_access_typed(record, selector)
        }

        fn post_index_access(&mut self, collection: PseudoExpr, index: usize) -> PseudoExpr {
            // Convert [N] to named field when collection has a known Cardano type
            if let Some(parent_type) = self.record_type(&collection)
                && let Some(field_name) = parent_type
                    .record()
                    .and_then(|t| context_field_at(t, index, self.version))
            {
                return PseudoExpr::field_access(collection, field_name.display_name());
            }
            PseudoExpr::IndexAccess {
                collection: PBox::new(collection),
                index,
            }
        }
    }

    let mut resolver = CardanoFieldResolver {
        var_types: ScopedTypeEnv::default(),
        version,
        kind_annotations,
    };
    resolver.fold(expr)
}
