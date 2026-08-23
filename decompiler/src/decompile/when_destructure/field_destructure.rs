use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use super::super::blueprint_registry::BlueprintHintRegistry;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

pub(crate) fn destructure_when_fields(
    expr: PseudoExpr,
    blueprint_hints: Option<&crate::cardano::BlueprintHints>,
    registry: Option<&BlueprintHintRegistry>,
) -> PseudoExpr {
    use crate::pseudo::ast::BinaryOp;
    use crate::pseudo::fold::ExprFolder;
    use num_traits::ToPrimitive;

    struct Destructurer<'a> {
        blueprint_hints: Option<&'a crate::cardano::BlueprintHints>,
        registry: Option<&'a BlueprintHintRegistry>,
    }

    // `ctor_name` is a user-chosen constructor name from blueprint
    // JSON, not a member of the closed `KnownConstructor` set, so the
    // string lookup (`c.name == ctor_name`) cannot move to
    // `ConstructorShape` without a richer typed identity.
    fn blueprint_field_names(
        hints: Option<&crate::cardano::BlueprintHints>,
        ctor_name: Option<&str>,
        tag: usize,
        max_field: usize,
    ) -> Vec<String> {
        if let Some(hints) = hints {
            if let Some(ctor_name) = ctor_name {
                for type_def in hints.types.values() {
                    if let Some(ctor) = type_def
                        .constructors
                        .iter()
                        .find(|c| c.tag == tag && c.name == ctor_name)
                    {
                        let names: Vec<String> = (0..=max_field)
                            .map(|i| {
                                ctor.fields
                                    .get(i)
                                    .and_then(|f| f.name.clone())
                                    .unwrap_or_else(|| format!("field_{}", i))
                            })
                            .collect();
                        return names;
                    }
                }
            }
            let mut candidate: Option<Vec<String>> = None;
            let mut ambiguous = false;
            for type_def in hints.types.values() {
                if let Some(ctor) = type_def.constructors.iter().find(|c| c.tag == tag)
                    && ctor.fields.len() > max_field
                {
                    let names: Vec<String> = (0..=max_field)
                        .map(|i| {
                            ctor.fields
                                .get(i)
                                .and_then(|f| f.name.clone())
                                .unwrap_or_else(|| format!("field_{}", i))
                        })
                        .collect();
                    if candidate.is_some() {
                        ambiguous = true;
                        break;
                    }
                    candidate = Some(names);
                }
            }
            if !ambiguous && let Some(names) = candidate {
                return names;
            }
        }
        (0..=max_field).map(|i| format!("field_{}", i)).collect()
    }

    fn allocate_binders_avoiding(names: Vec<String>, avoid_names: &HashSet<String>) -> Vec<Binder> {
        let mut used = avoid_names.clone();
        names
            .into_iter()
            .map(|base_name| {
                let mut name = base_name.clone();
                let mut suffix = 2usize;
                while used.contains(&name) {
                    name = format!("{}_{}", base_name, suffix);
                    suffix += 1;
                }
                used.insert(name.clone());
                Binder::new(name, VarId::fresh_binding())
            })
            .collect()
    }

    fn collect_pattern_binder_names(pattern: &WhenPattern, names: &mut Vec<String>) {
        match pattern {
            WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                names.extend(fields.iter().map(|field| field.to_string()));
            }
            WhenPattern::List { elements, tail } => {
                names.extend(elements.iter().map(|element| element.to_string()));
                if let Some(tail) = tail {
                    names.push(tail.to_string());
                }
            }
            WhenPattern::Pair(first, second) => {
                names.push(first.to_string());
                names.push(second.to_string());
            }
            WhenPattern::Var(binder) => names.push(binder.to_string()),
            WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
        }
    }

    fn collect_free_var_names(
        expr: &PseudoExpr,
        bound: &mut Vec<String>,
        names: &mut HashSet<String>,
    ) {
        enum Step<'a> {
            Visit(&'a PseudoExpr),
            Truncate(usize),
            /// A `let`: its VALUE is walked outside the binding, its body
            /// inside.
            EnterLetBody {
                name: &'a str,
                body: &'a PseudoExpr,
            },
            /// A `when` clause: pattern binders (plus subject name) are in
            /// scope for its guard and body only.
            EnterClause {
                subject_name: Option<&'a Binder>,
                clause: &'a WhenClause,
            },
        }

        let mut steps: Vec<Step<'_>> = vec![Step::Visit(expr)];
        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(expr) => match expr {
                    PseudoExpr::Var { name, .. } => {
                        if !bound.iter().any(|bound_name| bound_name == name) {
                            names.insert(name.clone());
                        }
                    }
                    PseudoExpr::Lambda { params, body } => {
                        let start = bound.len();
                        bound.extend(params.iter().map(|param| param.to_string()));
                        steps.push(Step::Truncate(start));
                        steps.push(Step::Visit(body));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let start = bound.len();
                        bound.push(name.to_string());
                        bound.extend(params.iter().map(|param| param.to_string()));
                        steps.push(Step::Truncate(start));
                        steps.push(Step::Visit(body));
                    }
                    PseudoExpr::Let {
                        name, value, body, ..
                    } => {
                        steps.push(Step::EnterLetBody { name, body });
                        steps.push(Step::Visit(value));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        for clause in clauses.iter().rev() {
                            steps.push(Step::EnterClause {
                                subject_name: subject_name.as_ref(),
                                clause,
                            });
                        }
                        steps.push(Step::Visit(subject));
                    }
                    PseudoExpr::Apply { function, args } => {
                        for arg in args.iter().rev() {
                            steps.push(Step::Visit(arg));
                        }
                        steps.push(Step::Visit(function));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        steps.push(Step::Visit(else_branch));
                        steps.push(Step::Visit(then_branch));
                        steps.push(Step::Visit(condition));
                    }
                    PseudoExpr::BinOp { left, right, .. } | PseudoExpr::Pair(left, right) => {
                        steps.push(Step::Visit(right));
                        steps.push(Step::Visit(left));
                    }
                    PseudoExpr::UnOp { operand, .. }
                    | PseudoExpr::FieldAccess {
                        record: operand, ..
                    }
                    | PseudoExpr::IndexAccess {
                        collection: operand,
                        ..
                    }
                    | PseudoExpr::Delay(operand)
                    | PseudoExpr::Force(operand) => steps.push(Step::Visit(operand)),
                    PseudoExpr::BuiltinCall { args, .. }
                    | PseudoExpr::Constr { fields: args, .. } => {
                        for arg in args.iter().rev() {
                            steps.push(Step::Visit(arg));
                        }
                    }
                    PseudoExpr::List { elements, tail } => {
                        if let Some(tail) = tail {
                            steps.push(Step::Visit(tail));
                        }
                        for element in elements.iter().rev() {
                            steps.push(Step::Visit(element));
                        }
                    }
                    PseudoExpr::Tuple(elements) => {
                        for element in elements.iter().rev() {
                            steps.push(Step::Visit(element));
                        }
                    }
                    PseudoExpr::Trace { message, value } => {
                        steps.push(Step::Visit(value));
                        steps.push(Step::Visit(message));
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
                Step::Truncate(start) => bound.truncate(start),
                Step::EnterLetBody { name, body } => {
                    let start = bound.len();
                    bound.push(name.to_string());
                    steps.push(Step::Truncate(start));
                    steps.push(Step::Visit(body));
                }
                Step::EnterClause {
                    subject_name,
                    clause,
                } => {
                    let start = bound.len();
                    if let Some(subject_name) = subject_name {
                        bound.push(subject_name.to_string());
                    }
                    collect_pattern_binder_names(&clause.pattern, bound);
                    steps.push(Step::Truncate(start));
                    steps.push(Step::Visit(&clause.body));
                    if let Some(guard) = &clause.guard {
                        steps.push(Step::Visit(guard));
                    }
                }
            }
        }
    }

    fn generated_binder_avoid_names(
        subject_name: Option<&Binder>,
        guard: Option<&PseudoExpr>,
        body: &PseudoExpr,
    ) -> HashSet<String> {
        let mut names = HashSet::new();
        if let Some(subject_name) = subject_name {
            names.insert(subject_name.to_string());
        }
        let mut bound = Vec::new();
        if let Some(guard) = guard {
            collect_free_var_names(guard, &mut bound, &mut names);
        }
        collect_free_var_names(body, &mut bound, &mut names);
        names
    }

    fn is_unpack_of(expr: &PseudoExpr, subject_id: VarId) -> bool {
        if let PseudoExpr::BuiltinCall { name, args } = expr
            && (*name == crate::BuiltinId::ConstrUnpack || *name == crate::BuiltinId::DataUnConstr)
            && args.len() == 1
            && let PseudoExpr::Var { id, .. } = args[0]
        {
            return id == Some(subject_id);
        }
        false
    }

    fn is_unpack_snd(expr: &PseudoExpr, subject_id: VarId) -> bool {
        if let PseudoExpr::FieldAccess {
            record, selector, ..
        } = expr
            && selector.is_pair_snd()
        {
            return is_unpack_of(record, subject_id);
        }
        false
    }

    fn count_list_tail_depth(expr: &PseudoExpr) -> (&PseudoExpr, usize) {
        let mut current = expr;
        let mut depth = 0usize;
        loop {
            if let PseudoExpr::BuiltinCall { name, args } = current
                && *name == crate::BuiltinId::ListTail
                && args.len() == 1
            {
                depth += 1;
                current = &args[0];
                continue;
            }
            if let PseudoExpr::Apply { function, args } = current
                && let PseudoExpr::BuiltinCall { name, args: ba } = function.as_ref()
                && *name == crate::BuiltinId::ListTail
                && ba.is_empty()
                && args.len() == 1
            {
                depth += 1;
                current = &args[0];
                continue;
            }
            return (current, depth);
        }
    }

    fn extract_field_index(expr: &PseudoExpr, subject_id: VarId) -> Option<usize> {
        if let PseudoExpr::FieldAccess {
            record, selector, ..
        } = expr
            && selector.is_list_head()
        {
            let (inner, depth) = count_list_tail_depth(record);
            if is_unpack_snd(inner, subject_id) {
                return Some(depth);
            }
        }
        if let PseudoExpr::IndexAccess { collection, index } = expr {
            let (inner, depth) = count_list_tail_depth(collection);
            if is_unpack_snd(inner, subject_id) {
                return Some(depth + index);
            }
        }
        None
    }

    fn collect_field_indices(
        expr: &PseudoExpr,
        subject_id: VarId,
        indices: &mut std::collections::BTreeSet<usize>,
    ) {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            if let Some(idx) = extract_field_index(current, subject_id) {
                indices.insert(idx);
                continue;
            }
            match current {
                PseudoExpr::Let { value, body, .. } => {
                    pending.push(body);
                    pending.push(value);
                }
                PseudoExpr::Apply { function, args } => {
                    for a in args.iter().rev() {
                        pending.push(a);
                    }
                    pending.push(function);
                }
                PseudoExpr::Lambda { body, .. } => pending.push(body),
                PseudoExpr::RecFn { body, .. } => pending.push(body),
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.push(else_branch);
                    pending.push(then_branch);
                    pending.push(condition);
                }
                PseudoExpr::When {
                    subject, clauses, ..
                } => {
                    for c in clauses.iter().rev() {
                        pending.push(&c.body);
                    }
                    pending.push(subject);
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(right);
                    pending.push(left);
                }
                PseudoExpr::UnOp { operand, .. } => pending.push(operand),
                PseudoExpr::BuiltinCall { args, .. } => {
                    for a in args.iter().rev() {
                        pending.push(a);
                    }
                }
                PseudoExpr::FieldAccess { record, .. } => pending.push(record),
                PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
                PseudoExpr::Constr { fields, .. } => {
                    for f in fields.iter().rev() {
                        pending.push(f);
                    }
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail {
                        pending.push(t);
                    }
                    for e in elements.iter().rev() {
                        pending.push(e);
                    }
                }
                PseudoExpr::Tuple(elems) => {
                    for e in elems.iter().rev() {
                        pending.push(e);
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    pending.push(b);
                    pending.push(a);
                }
                PseudoExpr::Trace { message, value } => {
                    pending.push(value);
                    pending.push(message);
                }
                PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
                PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::Unit
                | PseudoExpr::Var { .. }
                | PseudoExpr::Error { .. }
                | PseudoExpr::Raw { .. }
                | PseudoExpr::Data(_)
                | PseudoExpr::HelperSymbol(_) => {}
            }
        }
    }

    fn binder_name_conflicts_with_generated(binder: &Binder, binder_names: &[Binder]) -> bool {
        binder_names
            .iter()
            .any(|generated| generated.as_str() == binder.as_str())
    }

    fn name_conflicts_with_generated(name: &str, binder_names: &[Binder]) -> bool {
        binder_names
            .iter()
            .any(|generated| generated.as_str() == name)
    }

    fn pattern_conflicts_with_generated(pattern: &WhenPattern, binder_names: &[Binder]) -> bool {
        match pattern {
            WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
            WhenPattern::Var(binder) => binder_name_conflicts_with_generated(binder, binder_names),
            WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => fields
                .iter()
                .any(|field| binder_name_conflicts_with_generated(field, binder_names)),
            WhenPattern::List { elements, tail } => {
                elements
                    .iter()
                    .any(|element| binder_name_conflicts_with_generated(element, binder_names))
                    || tail.as_ref().is_some_and(|tail| {
                        binder_name_conflicts_with_generated(tail, binder_names)
                    })
            }
            WhenPattern::Pair(a, b) => {
                binder_name_conflicts_with_generated(a, binder_names)
                    || binder_name_conflicts_with_generated(b, binder_names)
            }
        }
    }

    /// A job on [`replace_field_accesses_named`]'s stack. A subtree whose binder
    /// collides with a generated field binder is pushed onto `done` verbatim — "keep
    /// this child" early return — and that decision stays where the walk
    /// made it: between the node's other children.
    enum ReplaceStep {
        Visit(PseudoExpr),
        Post(ReplacePost),
    }

    enum ReplacePost {
        /// `body` is `Some` when the `let` name collides, so its body was kept
        /// verbatim and no `Visit` step was queued for it.
        Let {
            name: String,
            id: Option<VarId>,
            body: Option<PBox>,
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
            /// `None` when the subject name collides: every clause was kept.
            layout: Option<Vec<ReplaceClause>>,
            kept_clauses: Vec<WhenClause>,
        },
        /// Any other node: its rewritten children sit on `done`; put them back
        /// into the shell they were taken out of.
        Plain {
            shell: PseudoExpr,
            count: usize,
        },
    }

    /// One `when` clause awaiting reassembly: either kept whole (its pattern
    /// collides with a generated binder) or split into queued children.
    enum ReplaceClause {
        Kept(WhenClause),
        Split {
            pattern: WhenPattern,
            has_guard: bool,
        },
    }

    impl ReplaceClause {
        fn child_count(&self) -> usize {
            match self {
                Self::Kept(_) => 0,
                Self::Split { has_guard, .. } => usize::from(*has_guard) + 1,
            }
        }

        fn rebuild(self, parts: &mut impl Iterator<Item = PseudoExpr>) -> WhenClause {
            match self {
                Self::Kept(clause) => clause,
                Self::Split { pattern, has_guard } => WhenClause {
                    pattern,
                    guard: if has_guard {
                        Some(parts.next().expect("clause guard"))
                    } else {
                        None
                    },
                    body: parts.next().expect("clause body"),
                },
            }
        }
    }

    /// Split a node into a SHELL — every immediate child replaced by a `Unit`
    /// placeholder — plus those children in `map_children` order.
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

    fn replace_field_accesses_named(
        expr: PseudoExpr,
        subject_id: VarId,
        max_field: usize,
        binder_names: &[Binder],
    ) -> PseudoExpr {
        let mut steps: Vec<ReplaceStep> = vec![ReplaceStep::Visit(expr)];
        let mut done: Vec<PseudoExpr> = Vec::new();

        while let Some(step) = steps.pop() {
            match step {
                ReplaceStep::Visit(expr) => {
                    visit(
                        expr,
                        subject_id,
                        max_field,
                        binder_names,
                        &mut steps,
                        &mut done,
                    );
                }
                ReplaceStep::Post(post) => {
                    let rebuilt = match post {
                        ReplacePost::Let { name, id, body } => {
                            let body = match body {
                                Some(kept) => kept,
                                None => PBox::new(done.pop().expect("let body")),
                            };
                            let value = PBox::new(done.pop().expect("let value"));
                            PseudoExpr::Let {
                                name,
                                id,
                                value,
                                body,
                            }
                        }
                        ReplacePost::Lambda { params } => PseudoExpr::Lambda {
                            params,
                            body: PBox::new(done.pop().expect("lambda body")),
                        },
                        ReplacePost::RecFn { name, params } => PseudoExpr::RecFn {
                            name,
                            params,
                            body: PBox::new(done.pop().expect("recfn body")),
                        },
                        ReplacePost::When {
                            subject_name,
                            layout,
                            kept_clauses,
                        } => {
                            let children: usize = layout
                                .iter()
                                .flatten()
                                .map(ReplaceClause::child_count)
                                .sum::<usize>()
                                + 1;
                            let mut parts = take_done(&mut done, children).into_iter();
                            let subject = PBox::new(parts.next().expect("when subject"));
                            let clauses = match layout {
                                Some(layout) => {
                                    layout.into_iter().map(|c| c.rebuild(&mut parts)).collect()
                                }
                                None => kept_clauses,
                            };
                            PseudoExpr::When {
                                subject,
                                subject_name,
                                clauses,
                            }
                        }
                        ReplacePost::Plain { shell, count } => {
                            let kids = take_done(&mut done, count);
                            join_children(shell, kids)
                        }
                    };
                    done.push(rebuilt);
                }
            }
        }

        done.pop()
            .expect("replace_field_accesses_named leaves exactly one result")
    }

    /// One node of [`replace_field_accesses_named`]: emit it, or queue its
    /// children and the step that puts the node back together.
    fn visit(
        expr: PseudoExpr,
        subject_id: VarId,
        max_field: usize,
        binder_names: &[Binder],
        steps: &mut Vec<ReplaceStep>,
        done: &mut Vec<PseudoExpr>,
    ) {
        if let Some(idx) = extract_field_index(&expr, subject_id)
            && idx <= max_field
        {
            debug_assert_eq!(binder_names.len(), max_field + 1);
            let binder = binder_names
                .get(idx)
                .expect("field binder must exist for collected field index");
            done.push(PseudoExpr::Var {
                name: binder.to_string(),
                id: Some(binder.var_id()),
            });
            return;
        }
        match expr {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                let body_blocked = name_conflicts_with_generated(&name, binder_names);
                if body_blocked {
                    steps.push(ReplaceStep::Post(ReplacePost::Let {
                        name,
                        id,
                        body: Some(body),
                    }));
                } else {
                    steps.push(ReplaceStep::Post(ReplacePost::Let {
                        name,
                        id,
                        body: None,
                    }));
                    steps.push(ReplaceStep::Visit(body.into_inner()));
                }
                steps.push(ReplaceStep::Visit(value.into_inner()));
            }
            PseudoExpr::Apply { function, args } => {
                if let PseudoExpr::Var { ref name, .. } = *function
                    && name == "expect!"
                    && args.len() == 2
                    && is_expect_tag_check(&args[0], subject_id)
                {
                    steps.push(ReplaceStep::Visit(args.into_iter().nth(1).unwrap()));
                    return;
                }
                let (shell, kids) = split_children(PseudoExpr::Apply { function, args });
                steps.push(ReplaceStep::Post(ReplacePost::Plain {
                    shell,
                    count: kids.len(),
                }));
                for kid in kids.into_iter().rev() {
                    steps.push(ReplaceStep::Visit(kid));
                }
            }
            PseudoExpr::Lambda { params, body } => {
                let blocked = params
                    .iter()
                    .any(|param| binder_name_conflicts_with_generated(param, binder_names));
                if blocked {
                    done.push(PseudoExpr::Lambda { params, body });
                } else {
                    steps.push(ReplaceStep::Post(ReplacePost::Lambda { params }));
                    steps.push(ReplaceStep::Visit(body.into_inner()));
                }
            }
            PseudoExpr::RecFn { name, params, body } => {
                let blocked = binder_name_conflicts_with_generated(&name, binder_names)
                    || params
                        .iter()
                        .any(|param| binder_name_conflicts_with_generated(param, binder_names));
                if blocked {
                    done.push(PseudoExpr::RecFn { name, params, body });
                } else {
                    steps.push(ReplaceStep::Post(ReplacePost::RecFn { name, params }));
                    steps.push(ReplaceStep::Visit(body.into_inner()));
                }
            }
            PseudoExpr::When {
                subject,
                subject_name: sn,
                clauses,
            } => {
                let subject_blocks = sn.as_ref().is_some_and(|subject_name| {
                    binder_name_conflicts_with_generated(subject_name, binder_names)
                });
                // Built in source order, then drained onto `steps` in reverse
                // so the jobs pop in source order.
                let mut jobs: Vec<ReplaceStep> = Vec::new();
                let mut kept_clauses: Vec<WhenClause> = Vec::new();
                let layout = if subject_blocks {
                    kept_clauses = clauses;
                    None
                } else {
                    let mut layout: Vec<ReplaceClause> = Vec::with_capacity(clauses.len());
                    for c in clauses {
                        if pattern_conflicts_with_generated(&c.pattern, binder_names) {
                            layout.push(ReplaceClause::Kept(c));
                            continue;
                        }
                        let has_guard = c.guard.is_some();
                        if let Some(guard) = c.guard {
                            jobs.push(ReplaceStep::Visit(guard));
                        }
                        jobs.push(ReplaceStep::Visit(c.body));
                        layout.push(ReplaceClause::Split {
                            pattern: c.pattern,
                            has_guard,
                        });
                    }
                    Some(layout)
                };
                steps.push(ReplaceStep::Post(ReplacePost::When {
                    subject_name: sn,
                    layout,
                    kept_clauses,
                }));
                while let Some(job) = jobs.pop() {
                    steps.push(job);
                }
                steps.push(ReplaceStep::Visit(subject.into_inner()));
            }
            // The non-binding variants, in `map_children`'s order; leaves
            // (Int, ByteArray, String, Bool, Unit, Var, Error, Raw, Data,
            // HelperSymbol) split into zero children and rejoin unchanged.
            other => {
                let (shell, kids) = split_children(other);
                steps.push(ReplaceStep::Post(ReplacePost::Plain {
                    shell,
                    count: kids.len(),
                }));
                for kid in kids.into_iter().rev() {
                    steps.push(ReplaceStep::Visit(kid));
                }
            }
        }
    }

    fn is_expect_tag_check(expr: &PseudoExpr, subject_id: VarId) -> bool {
        if let PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left,
            right,
        } = expr
        {
            return is_unpack_fst_of(left, subject_id)
                && matches!(right.as_ref(), PseudoExpr::Int(_))
                || is_unpack_fst_of(right, subject_id)
                    && matches!(left.as_ref(), PseudoExpr::Int(_));
        }
        false
    }

    fn is_unpack_fst_of(expr: &PseudoExpr, subject_id: VarId) -> bool {
        if let PseudoExpr::FieldAccess {
            record, selector, ..
        } = expr
            && selector.is_pair_fst()
        {
            return is_unpack_of(record, subject_id);
        }
        if let PseudoExpr::IndexAccess {
            collection,
            index: 0,
        } = expr
        {
            return is_unpack_of(collection, subject_id);
        }
        false
    }

    fn try_extract_expect_tag(expr: &PseudoExpr, subject_id: VarId) -> Option<(usize, PseudoExpr)> {
        if let PseudoExpr::Apply { function, args } = expr
            && let PseudoExpr::Var { name, .. } = function.as_ref()
            && name == "expect!"
            && args.len() == 2
            && let PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left,
                right,
            } = &args[0]
        {
            if is_unpack_fst_of(left, subject_id)
                && let PseudoExpr::Int(n) = right.as_ref()
                && let Some(tag) = n.to_usize()
            {
                return Some((tag, args[1].clone()));
            }
            if is_unpack_fst_of(right, subject_id)
                && let PseudoExpr::Int(n) = left.as_ref()
                && let Some(tag) = n.to_usize()
            {
                return Some((tag, args[1].clone()));
            }
        }
        None
    }

    fn strip_expect_tag_checks(expr: PseudoExpr, subject_id: VarId) -> PseudoExpr {
        let mut current = expr;
        loop {
            let is_expect_tag = if let PseudoExpr::Apply {
                ref function,
                ref args,
            } = current
            {
                matches!(&**function, PseudoExpr::Var { name, .. } if name == "expect!")
                    && args.len() == 2
                    && is_expect_tag_check(&args[0], subject_id)
            } else {
                false
            };

            if !is_expect_tag {
                return current;
            }

            current = match current {
                PseudoExpr::Apply { mut args, .. } => args.remove(1),
                _ => unreachable!("is_expect_tag only true for PseudoExpr::Apply"),
            };
        }
    }

    impl<'a> ExprFolder for Destructurer<'a> {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            let subj_var_id = match &subject {
                PseudoExpr::Var {
                    id: Some(id_val), ..
                } => *id_val,
                _ => {
                    return PseudoExpr::When {
                        subject: PBox::new(subject),
                        subject_name,
                        clauses,
                    };
                }
            };

            let bp = self.blueprint_hints;
            let new_clauses: Vec<WhenClause> = clauses
                .into_iter()
                .map(|clause| {
                    let is_empty_constructor = matches!(
                        &clause.pattern,
                        WhenPattern::Constructor { fields, .. } if fields.is_empty()
                    );
                    let is_wildcard = matches!(&clause.pattern, WhenPattern::Wildcard);

                    if !is_empty_constructor && !is_wildcard {
                        return clause;
                    }

                    if is_wildcard {
                        if let Some((tag, stripped_body)) =
                            try_extract_expect_tag(&clause.body, subj_var_id)
                        {
                            let mut indices = std::collections::BTreeSet::new();
                            collect_field_indices(&stripped_body, subj_var_id, &mut indices);

                            if indices.is_empty() {
                                return WhenClause {
                                    pattern: WhenPattern::constructor(
                                        ConstructorShape::unknown_data(tag, 0),
                                        vec![],
                                    ),
                                    guard: clause.guard,
                                    body: stripped_body,
                                };
                            }

                            let max_field = *indices.iter().next_back().unwrap();
                            let avoid_names = generated_binder_avoid_names(
                                subject_name.as_ref(),
                                clause.guard.as_ref(),
                                &stripped_body,
                            );
                            let binder_names = allocate_binders_avoiding(
                                blueprint_field_names(bp, None, tag, max_field),
                                &avoid_names,
                            );
                            let new_body = replace_field_accesses_named(
                                stripped_body,
                                subj_var_id,
                                max_field,
                                &binder_names,
                            );

                            let arity = binder_names.len();
                            return WhenClause {
                                pattern: WhenPattern::constructor(
                                    ConstructorShape::unknown_data(tag, arity),
                                    binder_names,
                                ),
                                guard: clause.guard,
                                body: new_body,
                            };
                        }
                        let new_body = strip_expect_tag_checks(clause.body, subj_var_id);
                        return WhenClause {
                            pattern: clause.pattern,
                            guard: clause.guard,
                            body: new_body,
                        };
                    }

                    let mut indices = std::collections::BTreeSet::new();
                    collect_field_indices(&clause.body, subj_var_id, &mut indices);

                    if indices.is_empty() {
                        return clause;
                    }

                    let max_field = *indices.iter().next_back().unwrap();

                    // Blueprint lookup needs the arbitrary string name
                    // recorded alongside `shape`; see
                    // `blueprint_field_names` for why it stays stringly.
                    // The registry resolves user-defined ADTs keyed by
                    // `type_hint`; Known shape variants cover the rest.
                    let (ctor_name, ctor_tag): (Option<std::rc::Rc<str>>, usize) =
                        match &clause.pattern {
                            WhenPattern::Constructor {
                                shape, type_hint, ..
                            } => {
                                let name = self
                                    .registry
                                    .and_then(|r| r.resolve(*shape, type_hint.as_ref()))
                                    .or_else(|| shape.pretty_name().map(std::rc::Rc::from));
                                (name, shape.tag())
                            }
                            _ => (None, 0),
                        };
                    let avoid_names = generated_binder_avoid_names(
                        subject_name.as_ref(),
                        clause.guard.as_ref(),
                        &clause.body,
                    );
                    let binder_names = allocate_binders_avoiding(
                        blueprint_field_names(bp, ctor_name.as_deref(), ctor_tag, max_field),
                        &avoid_names,
                    );

                    let new_body = replace_field_accesses_named(
                        clause.body,
                        subj_var_id,
                        max_field,
                        &binder_names,
                    );

                    let new_pattern = match clause.pattern {
                        WhenPattern::Constructor {
                            type_hint,
                            tag,
                            fields,
                            shape,
                        } if fields.is_empty() => WhenPattern::Constructor {
                            type_hint,
                            tag,
                            fields: binder_names,
                            shape,
                        },
                        other => other,
                    };

                    WhenClause {
                        pattern: new_pattern,
                        guard: clause.guard,
                        body: new_body,
                    }
                })
                .collect();

            PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses: new_clauses,
            }
        }
    }

    Destructurer {
        blueprint_hints,
        registry,
    }
    .fold(expr)
}
