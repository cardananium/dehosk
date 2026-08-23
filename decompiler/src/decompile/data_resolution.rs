use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::var_id::{OptionVarIdGet, VarId};
use std::collections::HashSet;

pub(crate) fn resolve_data_constr(expr: PseudoExpr) -> PseudoExpr {
    use crate::decompile::constructor_data::{
        normalize_constructor_data_expr, normalize_convertible_data_expr,
    };
    use crate::pseudo::ast::PseudoData;
    use crate::pseudo::fold::ExprFolder;

    struct DataConstrResolver;

    impl ExprFolder for DataConstrResolver {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_builtin_call(
            &mut self,
            name: crate::builtins::BuiltinId,
            args: Vec<PseudoExpr>,
        ) -> PseudoExpr {
            if *name == crate::BuiltinId::DataConstr && args.len() == 2 {
                let mut args = args.into_iter();
                return normalize_constructor_data_expr(args.next().unwrap(), args.next().unwrap());
            }
            PseudoExpr::BuiltinCall {
                name,
                args: args.into(),
            }
        }

        fn post_data(&mut self, data: Box<PseudoData>) -> PseudoExpr {
            normalize_convertible_data_expr(PseudoExpr::Data(data))
        }
    }

    DataConstrResolver.fold(expr)
}

/// Convert `BuiltinCall("Data.case", [scrutinee, h0, h1, h2, h3, h4, h5, h6])` into a
/// `when`: handlers equal to the repeated fallback collapse into the wildcard arm.
///
/// Handler index is the Data tag: Constr(0), Map(1), List(2), Int(3), ByteString(4),
/// plus optional extension handlers at indices 5 and 6.
pub(crate) fn resolve_data_case(expr: PseudoExpr) -> PseudoExpr {
    use crate::decompile::blueprint_registry::{DATA_TYPE_HINT_NAME, TypeHintId};
    use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;
    use crate::pseudo::fold::{ExprFolder, ExprVisitor};

    /// Count of named Data case tags (Constr, Map, List, Int, ByteString).
    /// Names themselves live in the blueprint-hint registry under
    /// [`DATA_TYPE_HINT_NAME`].
    const DATA_CASE_COUNT: usize = 5;

    /// Check if a handler is a "fallback" (identity, constant Constr, etc.)
    fn is_fallback_handler(h: &PseudoExpr) -> bool {
        match h {
            // Bare Constr with no fields (e.g. Constr<2>) — sentinel/fallback
            PseudoExpr::Constr { fields, .. } if fields.is_empty() => true,
            // Identity lambda fn(x) { x }
            PseudoExpr::Lambda { params, body } if params.len() == 1 => {
                matches!(body.as_ref(), PseudoExpr::Var { id, .. } if *id == Some(params[0].var_id()))
            }
            _ => false,
        }
    }

    fn repeated_fallback_handler(handlers: &[PseudoExpr]) -> Option<&PseudoExpr> {
        if let Some(explicit) = handlers.iter().find(|handler| is_fallback_handler(handler)) {
            return Some(explicit);
        }

        for (index, candidate) in handlers.iter().enumerate() {
            if handlers
                .iter()
                .skip(index + 1)
                .any(|other| other == candidate)
            {
                return Some(candidate);
            }
        }

        None
    }

    fn collect_let_names(expr: &PseudoExpr) -> HashSet<String> {
        struct LetNameCollector {
            names: HashSet<String>,
        }

        impl ExprVisitor for LetNameCollector {
            fn visit_let_pre(&mut self, name: &str) {
                self.names.insert(name.to_string());
            }
        }

        let mut collector = LetNameCollector {
            names: HashSet::new(),
        };
        collector.walk(expr);
        collector.names
    }

    fn unique_let_name(preferred: &str, used_let_names: &mut HashSet<String>) -> String {
        if used_let_names.insert(preferred.to_string()) {
            return preferred.to_string();
        }

        let mut suffix = 2;
        loop {
            let candidate = format!("{preferred}_{suffix}");
            if used_let_names.insert(candidate.clone()) {
                return candidate;
            }
            suffix += 1;
        }
    }

    fn rename_var_display_name_by_id(
        expr: PseudoExpr,
        target_name: &str,
        target_id: VarId,
        new_name: &str,
    ) -> PseudoExpr {
        #[derive(Clone, Copy, Default)]
        struct RenameShadow {
            exact: bool,
            fallback: bool,
        }

        impl RenameShadow {
            fn with_binder(self, binder: &Binder, target_name: &str, target_id: VarId) -> Self {
                Self {
                    exact: self.exact || binder.id == target_id,
                    fallback: self.fallback
                        || (binder.id != target_id && binder.as_str() == target_name),
                }
            }

            fn with_pattern(
                self,
                pattern: &WhenPattern,
                target_name: &str,
                target_id: VarId,
            ) -> Self {
                match pattern {
                    WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                        fields.iter().fold(self, |shadow, field| {
                            shadow.with_binder(field, target_name, target_id)
                        })
                    }
                    WhenPattern::List { elements, tail } => {
                        let shadow = elements.iter().fold(self, |shadow, element| {
                            shadow.with_binder(element, target_name, target_id)
                        });
                        tail.as_ref().map_or(shadow, |tail| {
                            shadow.with_binder(tail, target_name, target_id)
                        })
                    }
                    WhenPattern::Pair(first, second) => self
                        .with_binder(first, target_name, target_id)
                        .with_binder(second, target_name, target_id),
                    WhenPattern::Var(name) => self.with_binder(name, target_name, target_id),
                    WhenPattern::Wildcard | WhenPattern::Literal(_) => self,
                }
            }
        }

        fn var_matches_target(
            name: &str,
            id: &Option<VarId>,
            target_name: &str,
            target_id: VarId,
            shadow: RenameShadow,
        ) -> bool {
            (*id == Some(target_id) && !shadow.exact)
                || (id.get().is_none() && name == target_name && !shadow.fallback)
        }

        /// A job on [`go`]'s stack. The `RenameShadow` travels WITH the node
        /// rather than as a call argument, so a scope opened between two child
        /// descents (a `let`'s body, a clause's guard/body) still sees exactly
        /// the shadow set computed for it.
        enum RenameStep {
            Visit(PseudoExpr, RenameShadow),
            Post(RenamePost),
        }

        enum RenamePost {
            Lambda {
                params: Vec<Binder>,
            },
            RecFn {
                name: Binder,
                params: Vec<Binder>,
            },
            Let {
                name: String,
                id: Option<VarId>,
            },
            When {
                subject_name: Option<Binder>,
                layout: Vec<ClauseLayout>,
            },
            /// Any other node: its rewritten children sit on `done`; put them
            /// back into the shell they were taken out of.
            Plain {
                shell: PseudoExpr,
                count: usize,
            },
        }

        /// One `when` clause awaiting reassembly: everything that is NOT a
        /// walked child, plus how many children it left on `done`.
        struct ClauseLayout {
            /// `None` for a `Literal` pattern, whose payload went through the
            /// walk and is rebuilt from `done`.
            pattern: Option<WhenPattern>,
            has_guard: bool,
        }

        impl ClauseLayout {
            fn child_count(&self) -> usize {
                usize::from(self.pattern.is_none()) + usize::from(self.has_guard) + 1
            }

            fn rebuild(self, parts: &mut impl Iterator<Item = PseudoExpr>) -> WhenClause {
                let pattern = match self.pattern {
                    Some(pattern) => pattern,
                    None => WhenPattern::Literal(parts.next().expect("literal payload")),
                };
                let guard = if self.has_guard {
                    Some(parts.next().expect("clause guard"))
                } else {
                    None
                };
                WhenClause {
                    pattern,
                    guard,
                    body: parts.next().expect("clause body"),
                }
            }
        }

        /// Split a node into a SHELL — every immediate child replaced by a
        /// `Unit` placeholder — plus those children in `map_children` order.
        fn split_children(expr: PseudoExpr) -> (PseudoExpr, Vec<PseudoExpr>) {
            let mut kids: Vec<PseudoExpr> = Vec::new();
            let shell = crate::decompile::render_prep::scope_recurse::map_children(expr, |c| {
                kids.push(c);
                PseudoExpr::Unit
            });
            (shell, kids)
        }

        /// Put rewritten children back into a shell from [`split_children`].
        fn join_children(shell: PseudoExpr, kids: Vec<PseudoExpr>) -> PseudoExpr {
            let mut kids = kids.into_iter();
            crate::decompile::render_prep::scope_recurse::map_children(shell, |_| {
                kids.next().expect("split_children left one child per slot")
            })
        }

        /// Takes the last `n` items off `done`, in source order.
        fn take_done(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
            let at = done.len() - n;
            done.split_off(at)
        }

        fn go(
            expr: PseudoExpr,
            target_name: &str,
            target_id: VarId,
            new_name: &str,
            shadow: RenameShadow,
        ) -> PseudoExpr {
            let mut steps: Vec<RenameStep> = vec![RenameStep::Visit(expr, shadow)];
            let mut done: Vec<PseudoExpr> = Vec::new();

            while let Some(step) = steps.pop() {
                match step {
                    RenameStep::Visit(expr, shadow) => match expr {
                        PseudoExpr::Var { name, id } => done.push(PseudoExpr::Var {
                            name: if var_matches_target(&name, &id, target_name, target_id, shadow)
                            {
                                new_name.to_string()
                            } else {
                                name
                            },
                            id,
                        }),
                        PseudoExpr::Lambda { params, body } => {
                            let next_shadow = params.iter().fold(shadow, |shadow, param| {
                                shadow.with_binder(param, target_name, target_id)
                            });
                            steps.push(RenameStep::Post(RenamePost::Lambda { params }));
                            steps.push(RenameStep::Visit(body.into_inner(), next_shadow));
                        }
                        PseudoExpr::RecFn { name, params, body } => {
                            let next_shadow = params.iter().fold(
                                shadow.with_binder(&name, target_name, target_id),
                                |shadow, param| shadow.with_binder(param, target_name, target_id),
                            );
                            steps.push(RenameStep::Post(RenamePost::RecFn { name, params }));
                            steps.push(RenameStep::Visit(body.into_inner(), next_shadow));
                        }
                        PseudoExpr::Let {
                            name,
                            id,
                            value,
                            body,
                        } => {
                            // The binding comes into scope BETWEEN the value
                            // and the body: the value keeps the outer shadow.
                            let id_concrete = id.unwrap_or_else(VarId::fresh_compat_placeholder);
                            let next_shadow = shadow.with_binder(
                                &Binder::new(name.clone(), id_concrete),
                                target_name,
                                target_id,
                            );
                            steps.push(RenameStep::Post(RenamePost::Let { name, id }));
                            steps.push(RenameStep::Visit(body.into_inner(), next_shadow));
                            steps.push(RenameStep::Visit(value.into_inner(), shadow));
                        }
                        PseudoExpr::When {
                            subject,
                            subject_name,
                            clauses,
                        } => {
                            let subject_shadow = subject_name.as_ref().map_or(shadow, |name| {
                                shadow.with_binder(name, target_name, target_id)
                            });
                            let mut layout: Vec<ClauseLayout> = Vec::with_capacity(clauses.len());
                            // Built in source order, then drained onto `steps`
                            // in reverse so the jobs pop in source order.
                            let mut jobs: Vec<RenameStep> = Vec::new();
                            for clause in clauses {
                                // A literal payload is renamed under the
                                // OUTER shadow, not the clause's.
                                let pattern = match clause.pattern {
                                    WhenPattern::Literal(payload) => {
                                        jobs.push(RenameStep::Visit(payload, shadow));
                                        None
                                    }
                                    other => Some(other),
                                };
                                let clause_shadow =
                                    pattern.as_ref().map_or(subject_shadow, |pattern| {
                                        subject_shadow.with_pattern(pattern, target_name, target_id)
                                    });
                                let has_guard = clause.guard.is_some();
                                if let Some(guard) = clause.guard {
                                    jobs.push(RenameStep::Visit(guard, clause_shadow));
                                }
                                jobs.push(RenameStep::Visit(clause.body, clause_shadow));
                                layout.push(ClauseLayout { pattern, has_guard });
                            }
                            steps.push(RenameStep::Post(RenamePost::When {
                                subject_name,
                                layout,
                            }));
                            while let Some(job) = jobs.pop() {
                                steps.push(job);
                            }
                            steps.push(RenameStep::Visit(subject.into_inner(), shadow));
                        }
                        // The non-binding variants, in `map_children`'s order;
                        // leaves split into zero children and rejoin unchanged.
                        other => {
                            let (shell, kids) = split_children(other);
                            steps.push(RenameStep::Post(RenamePost::Plain {
                                shell,
                                count: kids.len(),
                            }));
                            for kid in kids.into_iter().rev() {
                                steps.push(RenameStep::Visit(kid, shadow));
                            }
                        }
                    },
                    RenameStep::Post(post) => {
                        let rebuilt = match post {
                            RenamePost::Lambda { params } => PseudoExpr::Lambda {
                                params,
                                body: PBox::new(done.pop().expect("lambda body")),
                            },
                            RenamePost::RecFn { name, params } => PseudoExpr::RecFn {
                                name,
                                params,
                                body: PBox::new(done.pop().expect("recfn body")),
                            },
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
                            RenamePost::When {
                                subject_name,
                                layout,
                            } => {
                                let children: usize =
                                    layout.iter().map(ClauseLayout::child_count).sum::<usize>() + 1;
                                let mut parts = take_done(&mut done, children).into_iter();
                                let subject = PBox::new(parts.next().expect("when subject"));
                                let clauses =
                                    layout.into_iter().map(|c| c.rebuild(&mut parts)).collect();
                                PseudoExpr::When {
                                    subject,
                                    subject_name,
                                    clauses,
                                }
                            }
                            RenamePost::Plain { shell, count } => {
                                let kids = take_done(&mut done, count);
                                join_children(shell, kids)
                            }
                        };
                        done.push(rebuilt);
                    }
                }
            }

            done.pop().expect("go leaves exactly one result")
        }

        go(
            expr,
            target_name,
            target_id,
            new_name,
            RenameShadow::default(),
        )
    }

    fn resolve_data_case_args(
        args: Vec<PseudoExpr>,
        used_let_names: &mut HashSet<String>,
    ) -> Option<PseudoExpr> {
        if args.len() < 6 {
            return None;
        }

        let scrutinee = args[0].clone();
        let handlers = &args[1..];
        let fallback_handler = repeated_fallback_handler(handlers).cloned();

        let meaningful: Vec<(usize, &PseudoExpr)> = handlers
            .iter()
            .enumerate()
            .filter(|(_, handler)| {
                fallback_handler
                    .as_ref()
                    .is_none_or(|fallback| *handler != fallback)
            })
            .collect();

        let meaningful_count = meaningful.len();
        let fallback_count = handlers.len() - meaningful_count;
        if meaningful.is_empty() || fallback_count == 0 {
            return None;
        }

        let mut clauses: Vec<WhenClause> = Vec::new();

        for &(i, handler) in &meaningful {
            let type_hint = if i < DATA_CASE_COUNT {
                Some(TypeHintId::new(DATA_TYPE_HINT_NAME))
            } else {
                None
            };
            let body = match handler {
                PseudoExpr::Lambda { params, body } => {
                    let mut result = body.as_ref().clone();
                    if params.len() == 1 {
                        let param = &params[0];
                        let let_name = unique_let_name(param.as_str(), used_let_names);
                        if let_name != param.as_str() {
                            result = rename_var_display_name_by_id(
                                result,
                                param.as_str(),
                                param.var_id(),
                                &let_name,
                            );
                        }
                        result = PseudoExpr::Let {
                            name: let_name,
                            id: Some(param.var_id()),
                            value: PBox::new(scrutinee.clone()),
                            body: PBox::new(result),
                        };
                    }
                    result
                }
                other => other.clone(),
            };

            let shape = ConstructorShape::from_name_and_tag(None, i, 0);
            clauses.push(WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint,
                    tag: i,
                    fields: vec![],
                    shape,
                },
                guard: None,
                body,
            });
        }

        clauses.push(WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body: fallback_handler.unwrap_or(PseudoExpr::Error {
                message: Some("unreachable".to_string()),
            }),
        });

        Some(PseudoExpr::When {
            subject: PBox::new(scrutinee),
            subject_name: None,
            clauses,
        })
    }

    fn peel_force_wrapped_builtin(expr: PseudoExpr) -> PseudoExpr {
        let mut current = expr;
        loop {
            match current {
                PseudoExpr::Force(inner) => current = inner.into_inner(),
                other => return other,
            }
        }
    }

    struct DataCaseResolver {
        used_let_names: HashSet<String>,
    }

    impl ExprFolder for DataCaseResolver {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_builtin_call(
            &mut self,
            name: crate::builtins::BuiltinId,
            args: Vec<PseudoExpr>,
        ) -> PseudoExpr {
            if *name == crate::BuiltinId::DataCase
                && let Some(resolved) =
                    resolve_data_case_args(args.clone(), &mut self.used_let_names)
            {
                return resolved;
            }
            PseudoExpr::BuiltinCall {
                name,
                args: args.into(),
            }
        }

        fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
            let function = peel_force_wrapped_builtin(function);
            if let PseudoExpr::BuiltinCall {
                name,
                args: builtin_args,
            } = function
            {
                if *name == crate::BuiltinId::DataCase {
                    let mut all_args = builtin_args;
                    all_args.extend(args);
                    if let Some(resolved) = resolve_data_case_args(
                        (all_args.clone()).into_vec(),
                        &mut self.used_let_names,
                    ) {
                        return resolved;
                    }
                    return PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::BuiltinCall {
                            name,
                            args: all_args,
                        }),
                        args: vec![].into(),
                    };
                }

                return PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::BuiltinCall {
                        name,
                        args: builtin_args,
                    }),
                    args: args.into(),
                };
            }

            PseudoExpr::Apply {
                function: PBox::new(function),
                args: args.into(),
            }
        }
    }

    let used_let_names = collect_let_names(&expr);
    DataCaseResolver { used_let_names }.fold(expr)
}
