//! `inline_single_use` on [`NamelessExpr`].
//!
//! `VarId` is the identity here: every Var carries only a `VarId` and
//! every binder owns a unique one, so the name-keyed inline values and
//! shadow stack the PseudoExpr inliner needs are unnecessary.
//!
//! Inlined: a simple value (`Var`, `Int`, `String`, `Bool`, `Unit`, or
//! a nullary `BuiltinCall`) used at most once; a nullary `BuiltinCall`
//! at any use count, being a tiny constant; and a hot
//! projection-lambda at every call site.
//!
//! Callers reach this pass via the pseudo→nameless→inline→pseudo
//! bridge.

use std::collections::{HashMap, HashSet};

use crate::pseudo::nameless::{NamelessClause, NamelessExpr, NamelessPattern, VarTable};
use crate::pseudo::var_id::VarId;

/// Inline single-use let bindings on a [`NamelessExpr`], with no
/// preserved set.
#[cfg(test)]
pub(crate) fn inline_single_use_nameless(expr: NamelessExpr) -> NamelessExpr {
    inline_single_use_nameless_preserving(expr, &HashSet::new())
}

/// Variant of [`inline_single_use_nameless`] that refuses to inline
/// let bindings whose `VarId` is in `preserved`.
///
/// Without a [`VarTable`] there are no rendered names, so this
/// entry point cannot refuse alias capture; prefer
/// [`inline_single_use_nameless_preserving_with_table`].
pub(crate) fn inline_single_use_nameless_preserving(
    expr: NamelessExpr,
    preserved: &HashSet<VarId>,
) -> NamelessExpr {
    inline_single_use_nameless_preserving_with_table(expr, preserved, &VarTable::default())
}

/// Production entry point. When a single-use let value is `Var(id)`,
/// inlining is refused if any binder in the body shares the rendered
/// name of `id`: `VarId` keeps semantic identity, but downstream
/// stages assert that PseudoExpr-rendered output has no stale
/// same-name refs pointing across a lambda shadow.
pub(crate) fn inline_single_use_nameless_preserving_with_table(
    expr: NamelessExpr,
    preserved: &HashSet<VarId>,
    table: &VarTable,
) -> NamelessExpr {
    // Pass 1: count usages per VarId.
    let mut counts: HashMap<VarId, usize> = HashMap::new();
    count_uses(&expr, &mut counts);

    // Pass 2: walk and inline.
    let mut inliner = Inliner {
        usage_count: counts,
        inline_values: HashMap::new(),
        preserved: preserved.clone(),
        table,
    };
    inliner.fold(expr)
}

// =============================================================
// Pass 1 — usage counting
// =============================================================

fn count_uses(expr: &NamelessExpr, out: &mut HashMap<VarId, usize>) {
    use crate::pseudo::nameless::fold::NamelessVisitor;

    struct UseCounter<'a> {
        out: &'a mut HashMap<VarId, usize>,
    }

    impl NamelessVisitor for UseCounter<'_> {
        fn visit_var(&mut self, id: VarId) {
            *self.out.entry(id).or_insert(0) += 1;
        }
    }

    UseCounter { out }.walk(expr);
}

// =============================================================
// Pass 2 — inline
// =============================================================

struct Inliner<'t> {
    usage_count: HashMap<VarId, usize>,
    inline_values: HashMap<VarId, NamelessExpr>,
    preserved: HashSet<VarId>,
    table: &'t VarTable,
}

impl<'t> Inliner<'t> {
    fn is_simple_value(expr: &NamelessExpr) -> bool {
        matches!(
            expr,
            NamelessExpr::Var(_)
                | NamelessExpr::Int(_)
                | NamelessExpr::String(_)
                | NamelessExpr::Bool(_)
                | NamelessExpr::Unit
        ) || matches!(expr, NamelessExpr::BuiltinCall { args, .. } if args.is_empty())
    }

    fn count_for(&self, id: VarId) -> usize {
        self.usage_count.get(&id).copied().unwrap_or(0)
    }

    // `Let` additionally reproduces `fold_let`'s "inline and keep going
    // without emitting a node" tail call: `Frame::LetDecide` folds only the
    // value, then — if the binding is inlined — schedules the body with NO
    // enclosing `Exit` frame, so the body's own eventual result stands in
    // directly for the whole `Let`, exactly as `return self.fold(body)` did.
    fn fold(&mut self, expr: NamelessExpr) -> NamelessExpr {
        enum Task {
            Enter(NamelessExpr),
            Exit(Frame),
        }

        enum Frame {
            Lambda {
                params: Vec<VarId>,
            },
            RecFn {
                name: VarId,
                params: Vec<VarId>,
            },
            Apply {
                n_args: usize,
            },
            If,
            When {
                subject_name: Option<VarId>,
                clause_shapes: Vec<(NamelessPattern, bool)>,
            },
            List {
                n_elements: usize,
                has_tail: bool,
            },
            Tuple {
                n: usize,
            },
            Pair,
            Constr {
                type_hint: Option<crate::pseudo::type_hint::TypeHintId>,
                tag: usize,
                shape: crate::pseudo::constructor::ConstructorShape,
                n_fields: usize,
            },
            FieldAccess {
                selector: crate::pseudo::field_selector::FieldSelector,
            },
            IndexAccess {
                index: usize,
            },
            BinOp {
                op: crate::pseudo::ast::BinaryOp,
            },
            UnOp {
                op: crate::pseudo::ast::UnaryOp,
            },
            BuiltinCall {
                name: crate::BuiltinId,
                n_args: usize,
            },
            Delay,
            Force,
            Trace,
            /// Let's value has been folded; decide whether to inline.
            LetDecide {
                binder: VarId,
                body: NamelessExpr,
            },
            /// Alias-capture refused the inline: rebuild the `Let` once the
            /// body (folded with the ORIGINAL value, not the inlined one) is
            /// also done.
            LetBuildRejected {
                binder: VarId,
                folded_value: NamelessExpr,
            },
            /// Not inlined (dead, or the value isn't simple): both children
            /// fold normally.
            LetBuild {
                binder: VarId,
            },
        }

        fn take(results: &mut Vec<NamelessExpr>, n: usize) -> Vec<NamelessExpr> {
            let at = results.len() - n;
            results.split_off(at)
        }

        let mut tasks = vec![Task::Enter(expr)];
        let mut results: Vec<NamelessExpr> = Vec::new();

        while let Some(task) = tasks.pop() {
            match task {
                Task::Enter(node) => match node {
                    // Leaves: nothing to recurse into.
                    NamelessExpr::Int(_)
                    | NamelessExpr::ByteArray(_)
                    | NamelessExpr::String(_)
                    | NamelessExpr::Bool(_)
                    | NamelessExpr::Unit
                    | NamelessExpr::Error { .. }
                    | NamelessExpr::Raw { .. }
                    | NamelessExpr::Data(_)
                    | NamelessExpr::HelperSymbol(_) => results.push(node),
                    NamelessExpr::Var(id) => results.push(
                        self.inline_values
                            .get(&id)
                            .cloned()
                            .unwrap_or(NamelessExpr::Var(id)),
                    ),
                    NamelessExpr::Lambda { params, body } => {
                        tasks.push(Task::Exit(Frame::Lambda { params }));
                        tasks.push(Task::Enter(*body));
                    }
                    NamelessExpr::RecFn { name, params, body } => {
                        tasks.push(Task::Exit(Frame::RecFn { name, params }));
                        tasks.push(Task::Enter(*body));
                    }
                    NamelessExpr::Apply { function, args } => {
                        tasks.push(Task::Exit(Frame::Apply { n_args: args.len() }));
                        for a in args.into_iter().rev() {
                            tasks.push(Task::Enter(a));
                        }
                        tasks.push(Task::Enter(*function));
                    }
                    NamelessExpr::Let {
                        binder,
                        value,
                        body,
                    } => {
                        let count = self.count_for(binder);
                        let is_preserved = self.preserved.contains(&binder);

                        // A Lambda whose body is a small projection chain
                        // ending in the param (e.g. `λx. tail(x.fields)`) is
                        // tiny enough that inlining at every call site reads
                        // better, however many uses it has.
                        let is_hot_projection_lambda = !is_preserved
                            && count > 0
                            && matches!(
                                value.as_ref(),
                                NamelessExpr::Lambda { params, body }
                                    if is_single_param_projection_accessor_nameless(params, body)
                            );

                        let should_inline = !is_preserved
                            && ((count <= 1 && Self::is_simple_value(value.as_ref()))
                                || (count > 0 && Self::is_nullary_builtin(value.as_ref()))
                                || is_hot_projection_lambda);

                        if should_inline && count > 0 {
                            // Re-fold the value with current inline state to
                            // enable cascading inlines (e.g. `let a = 1; let
                            // b = a; b` → `let b = 1; b` after `a` step → `1`
                            // after `b` step).
                            tasks.push(Task::Exit(Frame::LetDecide {
                                binder,
                                body: *body,
                            }));
                            tasks.push(Task::Enter(*value));
                        } else {
                            // Either count == 0 (a dead let is left for the
                            // dead_let pass to drop) or the value isn't
                            // simple.
                            tasks.push(Task::Exit(Frame::LetBuild { binder }));
                            tasks.push(Task::Enter(*body));
                            tasks.push(Task::Enter(*value));
                        }
                    }
                    NamelessExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        tasks.push(Task::Exit(Frame::If));
                        tasks.push(Task::Enter(*else_branch));
                        tasks.push(Task::Enter(*then_branch));
                        tasks.push(Task::Enter(*condition));
                    }
                    NamelessExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        let clause_shapes = clauses
                            .iter()
                            .map(|c| (c.pattern.clone(), c.guard.is_some()))
                            .collect();
                        tasks.push(Task::Exit(Frame::When {
                            subject_name,
                            clause_shapes,
                        }));
                        for c in clauses.into_iter().rev() {
                            tasks.push(Task::Enter(c.body));
                            if let Some(g) = c.guard {
                                tasks.push(Task::Enter(g));
                            }
                        }
                        tasks.push(Task::Enter(*subject));
                    }
                    NamelessExpr::List { elements, tail } => {
                        let has_tail = tail.is_some();
                        tasks.push(Task::Exit(Frame::List {
                            n_elements: elements.len(),
                            has_tail,
                        }));
                        if let Some(t) = tail {
                            tasks.push(Task::Enter(*t));
                        }
                        for e in elements.into_iter().rev() {
                            tasks.push(Task::Enter(e));
                        }
                    }
                    NamelessExpr::Tuple(items) => {
                        tasks.push(Task::Exit(Frame::Tuple { n: items.len() }));
                        for i in items.into_iter().rev() {
                            tasks.push(Task::Enter(i));
                        }
                    }
                    NamelessExpr::Pair(a, b) => {
                        tasks.push(Task::Exit(Frame::Pair));
                        tasks.push(Task::Enter(*b));
                        tasks.push(Task::Enter(*a));
                    }
                    NamelessExpr::Constr {
                        type_hint,
                        tag,
                        fields,
                        shape,
                    } => {
                        tasks.push(Task::Exit(Frame::Constr {
                            type_hint,
                            tag,
                            shape,
                            n_fields: fields.len(),
                        }));
                        for f in fields.into_iter().rev() {
                            tasks.push(Task::Enter(f));
                        }
                    }
                    NamelessExpr::FieldAccess { record, selector } => {
                        tasks.push(Task::Exit(Frame::FieldAccess { selector }));
                        tasks.push(Task::Enter(*record));
                    }
                    NamelessExpr::IndexAccess { collection, index } => {
                        tasks.push(Task::Exit(Frame::IndexAccess { index }));
                        tasks.push(Task::Enter(*collection));
                    }
                    NamelessExpr::BinOp { op, left, right } => {
                        tasks.push(Task::Exit(Frame::BinOp { op }));
                        tasks.push(Task::Enter(*right));
                        tasks.push(Task::Enter(*left));
                    }
                    NamelessExpr::UnOp { op, operand } => {
                        tasks.push(Task::Exit(Frame::UnOp { op }));
                        tasks.push(Task::Enter(*operand));
                    }
                    NamelessExpr::BuiltinCall { name, args } => {
                        tasks.push(Task::Exit(Frame::BuiltinCall {
                            name,
                            n_args: args.len(),
                        }));
                        for a in args.into_iter().rev() {
                            tasks.push(Task::Enter(a));
                        }
                    }
                    NamelessExpr::Delay(inner) => {
                        tasks.push(Task::Exit(Frame::Delay));
                        tasks.push(Task::Enter(*inner));
                    }
                    NamelessExpr::Force(inner) => {
                        tasks.push(Task::Exit(Frame::Force));
                        tasks.push(Task::Enter(*inner));
                    }
                    NamelessExpr::Trace { message, value } => {
                        tasks.push(Task::Exit(Frame::Trace));
                        tasks.push(Task::Enter(*value));
                        tasks.push(Task::Enter(*message));
                    }
                },
                Task::Exit(frame) => match frame {
                    Frame::Lambda { params } => {
                        let body = results.pop().expect("lambda body");
                        results.push(NamelessExpr::Lambda {
                            params,
                            body: Box::new(body),
                        });
                    }
                    Frame::RecFn { name, params } => {
                        let body = results.pop().expect("recfn body");
                        results.push(NamelessExpr::RecFn {
                            name,
                            params,
                            body: Box::new(body),
                        });
                    }
                    Frame::Apply { n_args } => {
                        let mut items = take(&mut results, 1 + n_args).into_iter();
                        let function = items.next().expect("apply function");
                        results.push(NamelessExpr::Apply {
                            function: Box::new(function),
                            args: items.collect(),
                        });
                    }
                    Frame::If => {
                        let mut items = take(&mut results, 3).into_iter();
                        let condition = items.next().expect("if condition");
                        let then_branch = items.next().expect("if then");
                        let else_branch = items.next().expect("if else");
                        results.push(NamelessExpr::If {
                            condition: Box::new(condition),
                            then_branch: Box::new(then_branch),
                            else_branch: Box::new(else_branch),
                        });
                    }
                    Frame::When {
                        subject_name,
                        clause_shapes,
                    } => {
                        let n_items: usize = 1 + clause_shapes
                            .iter()
                            .map(|(_, has_guard)| if *has_guard { 2 } else { 1 })
                            .sum::<usize>();
                        let mut items = take(&mut results, n_items).into_iter();
                        let subject = items.next().expect("when subject");
                        let mut clauses = Vec::with_capacity(clause_shapes.len());
                        for (pattern, has_guard) in clause_shapes {
                            let guard = if has_guard {
                                Some(items.next().expect("when clause guard"))
                            } else {
                                None
                            };
                            let body = items.next().expect("when clause body");
                            clauses.push(NamelessClause {
                                pattern,
                                guard,
                                body,
                            });
                        }
                        results.push(NamelessExpr::When {
                            subject: Box::new(subject),
                            subject_name,
                            clauses,
                        });
                    }
                    Frame::List {
                        n_elements,
                        has_tail,
                    } => {
                        let mut items =
                            take(&mut results, n_elements + has_tail as usize).into_iter();
                        let elements: Vec<_> = (&mut items).take(n_elements).collect();
                        let tail = items.next().map(Box::new);
                        results.push(NamelessExpr::List { elements, tail });
                    }
                    Frame::Tuple { n } => {
                        let items = take(&mut results, n);
                        results.push(NamelessExpr::Tuple(items));
                    }
                    Frame::Pair => {
                        let mut items = take(&mut results, 2).into_iter();
                        let a = items.next().expect("pair first");
                        let b = items.next().expect("pair second");
                        results.push(NamelessExpr::Pair(Box::new(a), Box::new(b)));
                    }
                    Frame::Constr {
                        type_hint,
                        tag,
                        shape,
                        n_fields,
                    } => {
                        let fields = take(&mut results, n_fields);
                        results.push(NamelessExpr::Constr {
                            type_hint,
                            tag,
                            fields,
                            shape,
                        });
                    }
                    Frame::FieldAccess { selector } => {
                        let record = results.pop().expect("field access record");
                        results.push(NamelessExpr::FieldAccess {
                            record: Box::new(record),
                            selector,
                        });
                    }
                    Frame::IndexAccess { index } => {
                        let collection = results.pop().expect("index access collection");
                        results.push(NamelessExpr::IndexAccess {
                            collection: Box::new(collection),
                            index,
                        });
                    }
                    Frame::BinOp { op } => {
                        let mut items = take(&mut results, 2).into_iter();
                        let left = items.next().expect("binop left");
                        let right = items.next().expect("binop right");
                        results.push(NamelessExpr::BinOp {
                            op,
                            left: Box::new(left),
                            right: Box::new(right),
                        });
                    }
                    Frame::UnOp { op } => {
                        let operand = results.pop().expect("unop operand");
                        results.push(NamelessExpr::UnOp {
                            op,
                            operand: Box::new(operand),
                        });
                    }
                    Frame::BuiltinCall { name, n_args } => {
                        let args = take(&mut results, n_args);
                        results.push(NamelessExpr::BuiltinCall { name, args });
                    }
                    Frame::Delay => {
                        let inner = results.pop().expect("delay inner");
                        results.push(NamelessExpr::Delay(Box::new(inner)));
                    }
                    Frame::Force => {
                        let inner = results.pop().expect("force inner");
                        results.push(NamelessExpr::Force(Box::new(inner)));
                    }
                    Frame::Trace => {
                        let mut items = take(&mut results, 2).into_iter();
                        let message = items.next().expect("trace message");
                        let value = items.next().expect("trace value");
                        results.push(NamelessExpr::Trace {
                            message: Box::new(message),
                            value: Box::new(value),
                        });
                    }
                    Frame::LetDecide { binder, body } => {
                        let folded_value = results.pop().expect("let value");
                        // Alias-capture refusal: stops `nameless_to_pseudo`
                        // from raising a same-name-different-VarId
                        // ambiguity. Only a Var value can collide — a
                        // literal or builtin has no rendered name.
                        // Conservative: refuses if ANY binder in the body
                        // shares the name, not just those on the path to the
                        // use site.
                        if let NamelessExpr::Var(target_id) = &folded_value
                            && let Some(target_name) = self.render_name_of(*target_id)
                            && body_binds_name(&body, target_name, self.table)
                        {
                            tasks.push(Task::Exit(Frame::LetBuildRejected {
                                binder,
                                folded_value,
                            }));
                            tasks.push(Task::Enter(body));
                        } else {
                            self.inline_values.insert(binder, folded_value);
                            // No Exit frame: the body's folded result stands
                            // in for this whole `Let` node.
                            tasks.push(Task::Enter(body));
                        }
                    }
                    Frame::LetBuildRejected {
                        binder,
                        folded_value,
                    } => {
                        let body = results.pop().expect("let body (rejected inline)");
                        results.push(NamelessExpr::Let {
                            binder,
                            value: Box::new(folded_value),
                            body: Box::new(body),
                        });
                    }
                    Frame::LetBuild { binder } => {
                        let mut items = take(&mut results, 2).into_iter();
                        let value = items.next().expect("let value");
                        let body = items.next().expect("let body");
                        results.push(NamelessExpr::Let {
                            binder,
                            value: Box::new(value),
                            body: Box::new(body),
                        });
                    }
                },
            }
        }

        debug_assert_eq!(results.len(), 1, "the fold machine must leave one result");
        results.pop().expect("fold result")
    }

    fn render_name_of(&self, id: VarId) -> Option<&'t str> {
        self.table.get(id).and_then(|m| m.render_name_hint())
    }

    fn is_nullary_builtin(expr: &NamelessExpr) -> bool {
        matches!(expr, NamelessExpr::BuiltinCall { args, .. } if args.is_empty())
    }
}

/// Mirror of `Simplifier::is_single_param_projection_accessor`
/// for [`NamelessExpr`]. A 1-arg lambda `λparam. <projection-chain
/// ending in param>` is "hot": tiny, uses the param once, and pure
/// (no control flow), so it is inlined at every call site.
fn is_single_param_projection_accessor_nameless(params: &[VarId], body: &NamelessExpr) -> bool {
    if params.len() != 1 {
        return false;
    }
    let param = params[0];
    count_var_uses_nameless(body, param) == 1
        && !contains_control_flow_expr_nameless(body)
        && is_projection_accessor_expr_nameless(body, param, false)
}

fn is_projection_accessor_expr_nameless(
    expr: &NamelessExpr,
    param: VarId,
    saw_projection: bool,
) -> bool {
    let mut current = expr;
    let mut saw_projection = saw_projection;
    loop {
        match current {
            NamelessExpr::Var(id) => return saw_projection && *id == param,
            NamelessExpr::FieldAccess { record, .. } => {
                saw_projection = true;
                current = record;
            }
            NamelessExpr::IndexAccess { collection, .. } => {
                saw_projection = true;
                current = collection;
            }
            NamelessExpr::BuiltinCall { name, args } if args.len() == 1 => {
                if !name.is_projection_wrapper() {
                    return false;
                }
                saw_projection = saw_projection || name.starts_projection_chain();
                current = &args[0];
            }
            NamelessExpr::Apply { function, args } if args.len() == 1 => match function.as_ref() {
                NamelessExpr::BuiltinCall {
                    name,
                    args: builtin_args,
                } if builtin_args.is_empty() => {
                    if !name.is_projection_wrapper() {
                        return false;
                    }
                    saw_projection = saw_projection || name.starts_projection_chain();
                    current = &args[0];
                }
                _ => return false,
            },
            _ => return false,
        }
    }
}

use crate::pseudo::nameless::fold::count_var_uses as count_var_uses_nameless;

fn contains_control_flow_expr_nameless(expr: &NamelessExpr) -> bool {
    use crate::pseudo::nameless::fold::{NamelessVisitor, VisitAction};

    struct ControlFlowScanner {
        found: bool,
    }
    impl NamelessVisitor for ControlFlowScanner {
        fn visit_expr(&mut self, expr: &NamelessExpr) -> VisitAction {
            if self.found {
                return VisitAction::Skip;
            }
            match expr {
                NamelessExpr::If { .. } | NamelessExpr::When { .. } | NamelessExpr::Let { .. } => {
                    self.found = true;
                    VisitAction::Skip
                }
                // Only these variants propagate the search;
                // everything else stops it — same scope as
                // `Simplifier::contains_control_flow_expr`.
                NamelessExpr::UnOp { .. }
                | NamelessExpr::BinOp { .. }
                | NamelessExpr::Apply { .. }
                | NamelessExpr::BuiltinCall { .. } => VisitAction::Walk,
                _ => VisitAction::Skip,
            }
        }
    }

    let mut scanner = ControlFlowScanner { found: false };
    scanner.walk(expr);
    scanner.found
}

/// Returns true iff `expr` contains any binder VarId whose
/// rendered name (per `table`) equals `target`. Drives the
/// alias-capture refusal in `fold`'s `Frame::LetDecide` step.
///
/// `VisitAction::Skip` short-circuits once a match is found:
/// that step calls this per substitution candidate, so a full
/// walk per call would compound to O(n²) on large ASTs.
fn body_binds_name(expr: &NamelessExpr, target: &str, table: &VarTable) -> bool {
    use crate::pseudo::nameless::fold::{NamelessVisitor, VisitAction};

    struct BinderNameScanner<'a> {
        target: &'a str,
        table: &'a VarTable,
        found: bool,
    }
    impl BinderNameScanner<'_> {
        fn check(&mut self, id: VarId) {
            if self.found {
                return;
            }
            if self
                .table
                .get(id)
                .and_then(|m| m.render_name_hint())
                .is_some_and(|n| n == self.target)
            {
                self.found = true;
            }
        }
    }
    impl NamelessVisitor for BinderNameScanner<'_> {
        fn visit_expr(&mut self, _: &NamelessExpr) -> VisitAction {
            if self.found {
                VisitAction::Skip
            } else {
                VisitAction::Walk
            }
        }
        fn enter_lambda(&mut self, params: &[VarId]) {
            for p in params {
                self.check(*p);
            }
        }
        fn enter_recfn(&mut self, name: VarId, params: &[VarId]) {
            self.check(name);
            for p in params {
                self.check(*p);
            }
        }
        fn enter_let(&mut self, binder: VarId, _: &NamelessExpr) {
            self.check(binder);
        }
        fn enter_when(&mut self, _: &NamelessExpr, subject_name: Option<VarId>) {
            if let Some(id) = subject_name {
                self.check(id);
            }
        }
        fn enter_clause(&mut self, pattern: &NamelessPattern) {
            for id in pattern_binders(pattern) {
                self.check(id);
            }
        }
    }

    let mut scanner = BinderNameScanner {
        target,
        table,
        found: false,
    };
    scanner.walk(expr);
    scanner.found
}

fn pattern_binders(pattern: &NamelessPattern) -> Vec<VarId> {
    match pattern {
        NamelessPattern::Wildcard | NamelessPattern::Literal(_) => Vec::new(),
        NamelessPattern::Var(id) => vec![*id],
        NamelessPattern::Constructor { fields, .. } | NamelessPattern::Tuple(fields) => {
            fields.clone()
        }
        NamelessPattern::List { elements, tail } => {
            let mut out = elements.clone();
            if let Some(t) = tail {
                out.push(*t);
            }
            out
        }
        NamelessPattern::Pair(a, b) => vec![*a, *b],
    }
}

// =============================================================
// Tests
// =============================================================

#[cfg(test)]
mod tests;
