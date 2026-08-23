use crate::decompile::simplify::Simplifier;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

#[derive(Clone, Copy)]
struct BindingUseTarget<'a> {
    name: &'a str,
    id: Option<VarId>,
}

impl Simplifier {
    pub(crate) fn is_var_used(expr: &PseudoExpr, var_name: &str) -> bool {
        Self::count_var_uses(expr, var_name) > 0
    }

    /// Count variable occurrences with lexical shadowing awareness.
    ///
    pub(crate) fn count_var_uses(expr: &PseudoExpr, var_name: &str) -> usize {
        let mut total = 0usize;
        let mut stack: Vec<&PseudoExpr> = vec![expr];
        while let Some(expr) = stack.pop() {
            match expr {
                PseudoExpr::Var { name, .. } => {
                    if name == var_name {
                        total += 1;
                    }
                }
                PseudoExpr::Lambda { params, body } => {
                    if !params.iter().any(|p| p == var_name) {
                        stack.push(body);
                    }
                }
                PseudoExpr::Apply { function, args } => {
                    for a in args.iter().rev() {
                        stack.push(a);
                    }
                    stack.push(function);
                }
                PseudoExpr::Let {
                    name, value, body, ..
                } => {
                    if name != var_name {
                        stack.push(body);
                    }
                    stack.push(value);
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    stack.push(else_branch);
                    stack.push(then_branch);
                    stack.push(condition);
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    stack.push(right);
                    stack.push(left);
                }
                PseudoExpr::UnOp { operand, .. } => stack.push(operand),
                PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => stack.push(inner),
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                    ..
                } => {
                    for clause in clauses.iter().rev() {
                        let shadowed = subject_name
                            .as_ref()
                            .is_some_and(|subject_name| subject_name == var_name)
                            || Self::pattern_binds_var(&clause.pattern, var_name);
                        if !shadowed {
                            stack.push(&clause.body);
                            if let Some(guard) = &clause.guard {
                                stack.push(guard);
                            }
                        }
                    }
                    stack.push(subject);
                }
                PseudoExpr::RecFn { name, params, body } => {
                    if name != var_name && !params.iter().any(|p| p == var_name) {
                        stack.push(body);
                    }
                }
                PseudoExpr::BuiltinCall { args, .. } => {
                    stack.extend(args.iter().rev());
                }
                PseudoExpr::Constr { fields, .. } => {
                    stack.extend(fields.iter().rev());
                }
                PseudoExpr::FieldAccess { record, .. } => stack.push(record),
                PseudoExpr::IndexAccess { collection, .. } => stack.push(collection),
                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail {
                        stack.push(t);
                    }
                    stack.extend(elements.iter().rev());
                }
                PseudoExpr::Tuple(elements) => {
                    stack.extend(elements.iter().rev());
                }
                PseudoExpr::Pair(first, second) => {
                    stack.push(second);
                    stack.push(first);
                }
                _ => {}
            }
        }
        total
    }

    /// Check whether a variable is used, with VarId-aware matching.
    ///
    /// When `var_id` is `Some` and the candidate also carries a VarId,
    /// identity comparison is authoritative. Otherwise falls back to name.
    pub(crate) fn is_var_used_by_id(
        expr: &PseudoExpr,
        var_name: &str,
        var_id: Option<VarId>,
    ) -> bool {
        Self::count_var_uses_by_id(expr, var_name, var_id) > 0
    }

    /// Count variable occurrences with VarId-aware matching and lexical
    /// shadowing awareness.
    ///
    /// At a `Var` site, VarIds decide when both the target `var_id` and
    /// the node's id are `Some`; otherwise names do.
    ///
    /// Shadowing uses those two channels independently: a binder whose
    /// VarId matches blocks id matches below it, one whose name matches
    /// blocks name matches. `Lambda`, `Let`, `RecFn` and `when`
    /// subject/pattern binders all shadow.
    pub(crate) fn count_var_uses_by_id(
        expr: &PseudoExpr,
        var_name: &str,
        var_id: Option<VarId>,
    ) -> usize {
        let mut total = 0usize;
        let mut stack = vec![(expr, false, false)];

        while let Some((current, exact_blocked, fallback_blocked)) = stack.pop() {
            match current {
                PseudoExpr::Var { name, id, .. } => {
                    let matches = match (var_id, id.get()) {
                        (Some(target), Some(candidate)) => !exact_blocked && target == candidate,
                        _ => !fallback_blocked && name == var_name,
                    };
                    total += usize::from(matches);
                }
                PseudoExpr::Lambda { params, body } => {
                    let exact_shadowed = params.iter().any(|param| {
                        crate::decompile::var_match::ids_match_strict(var_id, param.id.get())
                    });
                    let fallback_shadowed = params.iter().any(|param| param == var_name);
                    stack.push((
                        body,
                        exact_blocked || exact_shadowed,
                        fallback_blocked || fallback_shadowed,
                    ));
                }
                PseudoExpr::Apply { function, args } => {
                    for arg in args.iter().rev() {
                        stack.push((arg, exact_blocked, fallback_blocked));
                    }
                    stack.push((function, exact_blocked, fallback_blocked));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                    ..
                } => {
                    let exact_shadowed =
                        crate::decompile::var_match::ids_match_strict(var_id, id.get());
                    let fallback_shadowed = name == var_name;
                    stack.push((
                        body,
                        exact_blocked || exact_shadowed,
                        fallback_blocked || fallback_shadowed,
                    ));
                    stack.push((value, exact_blocked, fallback_blocked));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    stack.push((else_branch, exact_blocked, fallback_blocked));
                    stack.push((then_branch, exact_blocked, fallback_blocked));
                    stack.push((condition, exact_blocked, fallback_blocked));
                }
                PseudoExpr::BinOp { left, right, .. } | PseudoExpr::Pair(left, right) => {
                    stack.push((right, exact_blocked, fallback_blocked));
                    stack.push((left, exact_blocked, fallback_blocked));
                }
                PseudoExpr::UnOp { operand, .. }
                | PseudoExpr::Force(operand)
                | PseudoExpr::Delay(operand)
                | PseudoExpr::FieldAccess {
                    record: operand, ..
                }
                | PseudoExpr::IndexAccess {
                    collection: operand,
                    ..
                } => {
                    stack.push((operand, exact_blocked, fallback_blocked));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                    ..
                } => {
                    for clause in clauses.iter().rev() {
                        let exact_shadowed =
                            subject_name.as_ref().is_some_and(|subject_name| {
                                Self::binder_matches_var_id(subject_name, var_name, var_id)
                            }) || Self::pattern_binds_var_id(&clause.pattern, var_name, var_id);
                        let fallback_shadowed = subject_name
                            .as_ref()
                            .is_some_and(|subject_name| subject_name == var_name)
                            || Self::pattern_binds_var(&clause.pattern, var_name);
                        stack.push((
                            &clause.body,
                            exact_blocked || exact_shadowed,
                            fallback_blocked || fallback_shadowed,
                        ));
                        if let Some(guard) = &clause.guard {
                            stack.push((
                                guard,
                                exact_blocked || exact_shadowed,
                                fallback_blocked || fallback_shadowed,
                            ));
                        }
                    }
                    stack.push((subject, exact_blocked, fallback_blocked));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    let exact_shadowed =
                        crate::decompile::var_match::ids_match_strict(var_id, name.id.get())
                            || params.iter().any(|param| {
                                crate::decompile::var_match::ids_match_strict(
                                    var_id,
                                    param.id.get(),
                                )
                            });
                    let fallback_shadowed =
                        name == var_name || params.iter().any(|p| p == var_name);
                    stack.push((
                        body,
                        exact_blocked || exact_shadowed,
                        fallback_blocked || fallback_shadowed,
                    ));
                }
                PseudoExpr::BuiltinCall { args, .. } => {
                    for arg in args.iter().rev() {
                        stack.push((arg, exact_blocked, fallback_blocked));
                    }
                }
                PseudoExpr::Constr { fields, .. } | PseudoExpr::Tuple(fields) => {
                    for field in fields.iter().rev() {
                        stack.push((field, exact_blocked, fallback_blocked));
                    }
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(tail) = tail {
                        stack.push((tail, exact_blocked, fallback_blocked));
                    }
                    for element in elements.iter().rev() {
                        stack.push((element, exact_blocked, fallback_blocked));
                    }
                }
                PseudoExpr::Trace { message, value } => {
                    stack.push((value, exact_blocked, fallback_blocked));
                    stack.push((message, exact_blocked, fallback_blocked));
                }
                PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::Unit
                | PseudoExpr::Error { .. }
                | PseudoExpr::Raw { .. }
                | PseudoExpr::Data(_)
                | PseudoExpr::HelperSymbol(_) => {}
            }
        }

        total
    }

    fn count_binding_uses_by_id_impl(
        expr: &PseudoExpr,
        targets: &[BindingUseTarget<'_>],
        exact_shadow_depths: &mut [u32],
        fallback_shadow_depths: &mut [u32],
        counts: &mut [usize],
    ) {
        enum Frame<'a> {
            Enter(&'a PseudoExpr),
            EnterLetBody(&'a str, Option<VarId>, &'a PseudoExpr),
            EnterWhenClause(&'a Option<Binder>, &'a WhenClause),
            ExitLambda(&'a [Binder]),
            ExitLet(&'a str, Option<VarId>),
            ExitWhenClause(&'a Option<Binder>, &'a WhenPattern),
            ExitRecFn(&'a Binder, &'a [Binder]),
        }

        let mut stack = vec![Frame::Enter(expr)];

        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Enter(current) => match current {
                    PseudoExpr::Var { name, id, .. } => {
                        for (index, target) in targets.iter().enumerate() {
                            let matches = match (target.id, id.get()) {
                                (Some(target_id), Some(candidate_id)) => {
                                    exact_shadow_depths[index] == 0 && target_id == candidate_id
                                }
                                _ => fallback_shadow_depths[index] == 0 && name == target.name,
                            };
                            if matches {
                                counts[index] += 1;
                            }
                        }
                    }
                    PseudoExpr::Lambda { params, body } => {
                        for (index, target) in targets.iter().enumerate() {
                            if params.iter().any(|param| {
                                crate::decompile::var_match::ids_match_strict(
                                    target.id,
                                    param.id.get(),
                                )
                            }) {
                                exact_shadow_depths[index] += 1;
                            }
                            if params.iter().any(|param| param == target.name) {
                                fallback_shadow_depths[index] += 1;
                            }
                        }
                        stack.push(Frame::ExitLambda(params));
                        stack.push(Frame::Enter(body));
                    }
                    PseudoExpr::Apply { function, args } => {
                        for arg in args.iter().rev() {
                            stack.push(Frame::Enter(arg));
                        }
                        stack.push(Frame::Enter(function));
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                        ..
                    } => {
                        stack.push(Frame::EnterLetBody(name, id.get(), body));
                        stack.push(Frame::Enter(value));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        stack.push(Frame::Enter(else_branch));
                        stack.push(Frame::Enter(then_branch));
                        stack.push(Frame::Enter(condition));
                    }
                    PseudoExpr::BinOp { left, right, .. } | PseudoExpr::Pair(left, right) => {
                        stack.push(Frame::Enter(right));
                        stack.push(Frame::Enter(left));
                    }
                    PseudoExpr::UnOp { operand, .. }
                    | PseudoExpr::Force(operand)
                    | PseudoExpr::Delay(operand)
                    | PseudoExpr::FieldAccess {
                        record: operand, ..
                    }
                    | PseudoExpr::IndexAccess {
                        collection: operand,
                        ..
                    } => {
                        stack.push(Frame::Enter(operand));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                        ..
                    } => {
                        for clause in clauses.iter().rev() {
                            stack.push(Frame::EnterWhenClause(subject_name, clause));
                        }
                        stack.push(Frame::Enter(subject));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        for (index, target) in targets.iter().enumerate() {
                            let matches_name_or_param =
                                crate::decompile::var_match::ids_match_strict(
                                    target.id,
                                    name.id.get(),
                                ) || params.iter().any(|param| {
                                    crate::decompile::var_match::ids_match_strict(
                                        target.id,
                                        param.id.get(),
                                    )
                                });
                            if matches_name_or_param {
                                exact_shadow_depths[index] += 1;
                            }
                            if name == target.name
                                || params.iter().any(|param| param == target.name)
                            {
                                fallback_shadow_depths[index] += 1;
                            }
                        }
                        stack.push(Frame::ExitRecFn(name, params));
                        stack.push(Frame::Enter(body));
                    }
                    PseudoExpr::BuiltinCall { args, .. } => {
                        for arg in args.iter().rev() {
                            stack.push(Frame::Enter(arg));
                        }
                    }
                    PseudoExpr::Constr { fields, .. } | PseudoExpr::Tuple(fields) => {
                        for field in fields.iter().rev() {
                            stack.push(Frame::Enter(field));
                        }
                    }
                    PseudoExpr::List { elements, tail } => {
                        if let Some(tail) = tail {
                            stack.push(Frame::Enter(tail));
                        }
                        for element in elements.iter().rev() {
                            stack.push(Frame::Enter(element));
                        }
                    }
                    PseudoExpr::Trace { message, value } => {
                        stack.push(Frame::Enter(value));
                        stack.push(Frame::Enter(message));
                    }
                    PseudoExpr::Int(_)
                    | PseudoExpr::ByteArray(_)
                    | PseudoExpr::String(_)
                    | PseudoExpr::Bool(_)
                    | PseudoExpr::Unit
                    | PseudoExpr::Error { .. }
                    | PseudoExpr::Raw { .. }
                    | PseudoExpr::Data(_)
                    | PseudoExpr::HelperSymbol(_) => {}
                },
                Frame::EnterLetBody(name, id, body) => {
                    for (index, target) in targets.iter().enumerate() {
                        if crate::decompile::var_match::ids_match_strict(target.id, id) {
                            exact_shadow_depths[index] += 1;
                        }
                        if name == target.name {
                            fallback_shadow_depths[index] += 1;
                        }
                    }
                    stack.push(Frame::ExitLet(name, id));
                    stack.push(Frame::Enter(body));
                }
                Frame::EnterWhenClause(subject_name, clause) => {
                    for (index, target) in targets.iter().enumerate() {
                        let exact_shadowed_by_subject =
                            subject_name.as_ref().is_some_and(|subject_name| {
                                Self::binder_matches_var_id(subject_name, target.name, target.id)
                            });
                        let exact_shadowed_by_pattern =
                            Self::pattern_binds_var_id(&clause.pattern, target.name, target.id);
                        let fallback_shadowed_by_subject = subject_name
                            .as_ref()
                            .is_some_and(|subject_name| subject_name == target.name);
                        let fallback_shadowed_by_pattern =
                            Self::pattern_binds_var(&clause.pattern, target.name);

                        if exact_shadowed_by_subject || exact_shadowed_by_pattern {
                            exact_shadow_depths[index] += 1;
                        }
                        if fallback_shadowed_by_subject || fallback_shadowed_by_pattern {
                            fallback_shadow_depths[index] += 1;
                        }
                    }
                    stack.push(Frame::ExitWhenClause(subject_name, &clause.pattern));
                    stack.push(Frame::Enter(&clause.body));
                    if let Some(guard) = &clause.guard {
                        stack.push(Frame::Enter(guard));
                    }
                }
                Frame::ExitLambda(params) => {
                    for (index, target) in targets.iter().enumerate() {
                        if params.iter().any(|param| {
                            crate::decompile::var_match::ids_match_strict(target.id, param.id.get())
                        }) {
                            exact_shadow_depths[index] -= 1;
                        }
                        if params.iter().any(|param| param == target.name) {
                            fallback_shadow_depths[index] -= 1;
                        }
                    }
                }
                Frame::ExitLet(name, id) => {
                    for (index, target) in targets.iter().enumerate() {
                        if crate::decompile::var_match::ids_match_strict(target.id, id) {
                            exact_shadow_depths[index] -= 1;
                        }
                        if name == target.name {
                            fallback_shadow_depths[index] -= 1;
                        }
                    }
                }
                Frame::ExitWhenClause(subject_name, pattern) => {
                    for (index, target) in targets.iter().enumerate() {
                        let exact_shadowed_by_subject =
                            subject_name.as_ref().is_some_and(|subject_name| {
                                Self::binder_matches_var_id(subject_name, target.name, target.id)
                            });
                        let exact_shadowed_by_pattern =
                            Self::pattern_binds_var_id(pattern, target.name, target.id);
                        let fallback_shadowed_by_subject = subject_name
                            .as_ref()
                            .is_some_and(|subject_name| subject_name == target.name);
                        let fallback_shadowed_by_pattern =
                            Self::pattern_binds_var(pattern, target.name);

                        if exact_shadowed_by_subject || exact_shadowed_by_pattern {
                            exact_shadow_depths[index] -= 1;
                        }
                        if fallback_shadowed_by_subject || fallback_shadowed_by_pattern {
                            fallback_shadow_depths[index] -= 1;
                        }
                    }
                }
                Frame::ExitRecFn(name, params) => {
                    for (index, target) in targets.iter().enumerate() {
                        let matches_name_or_param =
                            crate::decompile::var_match::ids_match_strict(target.id, name.id.get())
                                || params.iter().any(|param| {
                                    crate::decompile::var_match::ids_match_strict(
                                        target.id,
                                        param.id.get(),
                                    )
                                });
                        if matches_name_or_param {
                            exact_shadow_depths[index] -= 1;
                        }
                        if name == target.name || params.iter().any(|param| param == target.name) {
                            fallback_shadow_depths[index] -= 1;
                        }
                    }
                }
            }
        }
    }

    pub(crate) fn count_binding_uses_by_id(
        expr: &PseudoExpr,
        binders: &[Binder],
        binder_ids: &[Option<VarId>],
    ) -> Vec<usize> {
        assert_eq!(binders.len(), binder_ids.len());
        match binders.len() {
            0 => return Vec::new(),
            1 => {
                return vec![Self::count_var_uses_by_id(
                    expr,
                    binders[0].as_str(),
                    binder_ids[0],
                )];
            }
            _ => {}
        }
        let targets: Vec<_> = binders
            .iter()
            .zip(binder_ids.iter().copied())
            .map(|(binder, id)| BindingUseTarget {
                name: binder.as_str(),
                id,
            })
            .collect();
        let mut exact_shadow_depths = vec![0u32; targets.len()];
        let mut fallback_shadow_depths = vec![0u32; targets.len()];
        let mut counts = vec![0; targets.len()];
        Self::count_binding_uses_by_id_impl(
            expr,
            &targets,
            &mut exact_shadow_depths,
            &mut fallback_shadow_depths,
            &mut counts,
        );
        counts
    }

    pub(crate) fn count_binding_uses(expr: &PseudoExpr, binders: &[Binder]) -> Vec<usize> {
        match binders.len() {
            0 => Vec::new(),
            1 => vec![Self::count_var_uses(expr, binders[0].as_str())],
            _ => Self::count_binding_uses_by_id(expr, binders, &vec![None; binders.len()]),
        }
    }
}
