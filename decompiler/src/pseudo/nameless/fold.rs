//! Generic folder trait for [`NamelessExpr`] transformations.
//!
//! Mirrors `pseudo::fold::ExprFolder` but for the nameless IR.
//! Identity-default `post_*` hooks let a pass override only the
//! variants it cares about; the `fold` driver folds a node's
//! children before invoking the hook.

use super::{NBox, NClauses, NamelessClause, NamelessExpr, NamelessPattern};
use crate::pseudo::ast::{BinaryOp, UnaryOp};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

/// Controls whether [`NamelessFolder::fold`] recurses into children
/// or replaces the node with an early result.
///
/// Mirrors `pseudo::fold::FoldAction` but for [`NamelessExpr`].
pub(crate) enum NamelessFoldAction {
    /// Recurse into children, then call the appropriate `post_*` hook.
    Walk,
    /// Replace the node with this expression (skip recursion).
    Replace(NamelessExpr),
}

pub(crate) trait NamelessFolder {
    // Pre-visit hook (called before recursion) --------

    /// Called before recursing into any node. Return `Walk` to continue
    /// into children, or `Replace(expr)` to substitute without recursing.
    ///
    /// Default: walk into children.
    fn pre_expr(&mut self, _expr: &NamelessExpr) -> NamelessFoldAction {
        NamelessFoldAction::Walk
    }

    /// Called after the node has been reconstructed through the appropriate
    /// `post_*` hook. Useful for root-level rewrites without re-implementing
    /// the walker.
    ///
    /// Default: identity.
    fn post_expr(&mut self, expr: NamelessExpr) -> NamelessExpr {
        expr
    }

    // Scope-tracking lifecycle hooks --------
    //
    // Called by the fold driver around each binder-introducing
    // node so passes can maintain a scope stack without overriding
    // the variant-specific fold logic.

    /// Called before recursing into a Lambda body. The slice holds
    /// the Lambda's binder VarIds.
    fn enter_lambda(&mut self, _params: &[VarId]) {}

    /// Called after the Lambda body has been folded.
    fn exit_lambda(&mut self, _params: &[VarId]) {}

    /// Called before recursing into a RecFn body. `name` is the
    /// recursive self-binder; `params` are the function arguments.
    fn enter_recfn(&mut self, _name: VarId, _params: &[VarId]) {}

    /// Called after the RecFn body has been folded.
    fn exit_recfn(&mut self, _name: VarId, _params: &[VarId]) {}

    /// Called before recursing into the Let body, AFTER the value
    /// has been folded (so the value subtree's own enters/exits have
    /// completed). Pass the original `binder` and the FOLDED value
    /// so the implementer can register an alias-tracking entry.
    fn enter_let(&mut self, _binder: VarId, _value: &NamelessExpr) {}

    /// Called after the Let body has been folded.
    fn exit_let(&mut self, _binder: VarId) {}

    /// Called before recursing into the When clauses, AFTER the
    /// subject is folded. `subject_name` is the optional subject
    /// alias VarId for the subject's own scope.
    fn enter_when(&mut self, _subject: &NamelessExpr, _subject_name: Option<VarId>) {}

    /// Called after the When clauses have been folded.
    fn exit_when(&mut self, _subject_name: Option<VarId>) {}

    /// Called before recursing into a clause body / guard. Pass
    /// the pattern so the implementer can register pattern binders.
    fn enter_clause(&mut self, _pattern: &NamelessPattern) {}

    /// Called after the clause has been folded.
    fn exit_clause(&mut self, _pattern: &NamelessPattern) {}

    // Identity post-hooks (one per variant) --------

    fn post_int(&mut self, n: num_bigint::BigInt) -> NamelessExpr {
        NamelessExpr::Int(n)
    }
    fn post_byte_array(&mut self, bytes: Vec<u8>) -> NamelessExpr {
        NamelessExpr::ByteArray(bytes)
    }
    fn post_string(&mut self, s: String) -> NamelessExpr {
        NamelessExpr::String(s)
    }
    fn post_bool(&mut self, b: bool) -> NamelessExpr {
        NamelessExpr::Bool(b)
    }
    fn post_unit(&mut self) -> NamelessExpr {
        NamelessExpr::Unit
    }
    fn post_var(&mut self, id: VarId) -> NamelessExpr {
        NamelessExpr::Var(id)
    }
    fn post_lambda(&mut self, params: Vec<VarId>, body: NamelessExpr) -> NamelessExpr {
        NamelessExpr::Lambda {
            params,
            body: NBox::new(body),
        }
    }
    fn post_recfn(&mut self, name: VarId, params: Vec<VarId>, body: NamelessExpr) -> NamelessExpr {
        NamelessExpr::RecFn {
            name,
            params,
            body: NBox::new(body),
        }
    }
    fn post_apply(&mut self, function: NamelessExpr, args: Vec<NamelessExpr>) -> NamelessExpr {
        NamelessExpr::Apply {
            function: NBox::new(function),
            args: args.into(),
        }
    }
    fn post_let(&mut self, binder: VarId, value: NamelessExpr, body: NamelessExpr) -> NamelessExpr {
        NamelessExpr::Let {
            binder,
            value: NBox::new(value),
            body: NBox::new(body),
        }
    }
    fn post_if(
        &mut self,
        condition: NamelessExpr,
        then_branch: NamelessExpr,
        else_branch: NamelessExpr,
    ) -> NamelessExpr {
        NamelessExpr::If {
            condition: NBox::new(condition),
            then_branch: NBox::new(then_branch),
            else_branch: NBox::new(else_branch),
        }
    }
    fn post_when(
        &mut self,
        subject: NamelessExpr,
        subject_name: Option<VarId>,
        clauses: Vec<NamelessClause>,
    ) -> NamelessExpr {
        NamelessExpr::When {
            subject: NBox::new(subject),
            subject_name,
            clauses: clauses.into(),
        }
    }
    fn post_list(
        &mut self,
        elements: Vec<NamelessExpr>,
        tail: Option<NamelessExpr>,
    ) -> NamelessExpr {
        NamelessExpr::List {
            elements: elements.into(),
            tail: tail.map(NBox::new),
        }
    }
    fn post_tuple(&mut self, items: Vec<NamelessExpr>) -> NamelessExpr {
        NamelessExpr::Tuple(items.into())
    }
    fn post_pair(&mut self, first: NamelessExpr, second: NamelessExpr) -> NamelessExpr {
        NamelessExpr::Pair(NBox::new(first), NBox::new(second))
    }
    fn post_constr(
        &mut self,
        type_hint: Option<crate::pseudo::type_hint::TypeHintId>,
        tag: usize,
        fields: Vec<NamelessExpr>,
        shape: crate::pseudo::constructor::ConstructorShape,
    ) -> NamelessExpr {
        NamelessExpr::Constr {
            type_hint,
            tag,
            fields: fields.into(),
            shape,
        }
    }
    fn post_field_access(&mut self, record: NamelessExpr, selector: FieldSelector) -> NamelessExpr {
        NamelessExpr::FieldAccess {
            record: NBox::new(record),
            selector,
        }
    }
    fn post_index_access(&mut self, collection: NamelessExpr, index: usize) -> NamelessExpr {
        NamelessExpr::IndexAccess {
            collection: NBox::new(collection),
            index,
        }
    }
    fn post_binop(
        &mut self,
        op: BinaryOp,
        left: NamelessExpr,
        right: NamelessExpr,
    ) -> NamelessExpr {
        NamelessExpr::BinOp {
            op,
            left: NBox::new(left),
            right: NBox::new(right),
        }
    }
    fn post_unop(&mut self, op: UnaryOp, operand: NamelessExpr) -> NamelessExpr {
        NamelessExpr::UnOp {
            op,
            operand: NBox::new(operand),
        }
    }
    fn post_builtin_call(
        &mut self,
        name: crate::BuiltinId,
        args: Vec<NamelessExpr>,
    ) -> NamelessExpr {
        NamelessExpr::BuiltinCall {
            name,
            args: args.into(),
        }
    }
    fn post_error(&mut self, message: Option<String>) -> NamelessExpr {
        NamelessExpr::Error { message }
    }
    fn post_delay(&mut self, inner: NamelessExpr) -> NamelessExpr {
        NamelessExpr::Delay(NBox::new(inner))
    }
    fn post_force(&mut self, inner: NamelessExpr) -> NamelessExpr {
        NamelessExpr::Force(NBox::new(inner))
    }
    fn post_trace(&mut self, message: NamelessExpr, value: NamelessExpr) -> NamelessExpr {
        NamelessExpr::Trace {
            message: NBox::new(message),
            value: NBox::new(value),
        }
    }
    fn post_raw(&mut self, uplc: String, reason: String) -> NamelessExpr {
        NamelessExpr::Raw { uplc, reason }
    }
    fn post_data(&mut self, data: Box<crate::pseudo::ast::PseudoData>) -> NamelessExpr {
        NamelessExpr::Data(data)
    }
    fn post_helper_symbol(
        &mut self,
        intrinsic: crate::pseudo::ast::HelperIntrinsic,
    ) -> NamelessExpr {
        NamelessExpr::HelperSymbol(intrinsic)
    }

    // Driver --------

    /// Fold `expr` bottom-up: `pre_expr`, the node's enter hook, its
    /// children in source order, its exit hook, its `post_*` hook, then
    /// `post_expr` — the order a recursive descent fires them in.
    ///
    /// The descent runs on a heap stack ([`fold_machine`]): nesting depth is
    /// script-controlled, and on `wasm32` the engine's call stack cannot be
    /// grown to match. No implementation may override `fold` — that would
    /// put the whole subtree back on the call stack. Intercept with
    /// `pre_expr` or the hooks instead.
    fn fold(&mut self, expr: NamelessExpr) -> NamelessExpr {
        fold_machine(self, expr)
    }
}

/// One pending step of [`fold_machine`].
enum FoldStep {
    /// Fold this subtree.
    Visit(NamelessExpr),
    /// A `let` value is folded and on top of `done`: open the binding, then
    /// fold the body under it.
    LetBody { binder: VarId, body: NamelessExpr },
    /// A `when` subject is folded and on top of `done`: open the `when`,
    /// then fold the clauses in order.
    WhenClauses {
        subject_name: Option<VarId>,
        clauses: NClauses,
    },
    /// Open a clause, then fold its guard and body.
    Clause(NamelessClause),
    /// A clause's guard and body are on `done`: close and reassemble it.
    ClauseDone {
        pattern: NamelessPattern,
        has_guard: bool,
    },
    /// All of a node's children are on `done`: reassemble it.
    Build(FoldBuild),
}

/// The node a [`FoldStep::Build`] reassembles, carrying the parts that are
/// not children.
enum FoldBuild {
    Lambda {
        params: Vec<VarId>,
    },
    RecFn {
        name: VarId,
        params: Vec<VarId>,
    },
    Apply {
        argc: usize,
    },
    Let {
        binder: VarId,
    },
    If,
    When {
        subject_name: Option<VarId>,
        clause_count: usize,
    },
    List {
        count: usize,
        has_tail: bool,
    },
    Tuple {
        count: usize,
    },
    Pair,
    Constr {
        type_hint: Option<crate::pseudo::type_hint::TypeHintId>,
        tag: usize,
        count: usize,
        shape: crate::pseudo::constructor::ConstructorShape,
    },
    FieldAccess {
        selector: FieldSelector,
    },
    IndexAccess {
        index: usize,
    },
    BinOp {
        op: BinaryOp,
    },
    UnOp {
        op: UnaryOp,
    },
    BuiltinCall {
        name: crate::BuiltinId,
        argc: usize,
    },
    Delay,
    Force,
    Trace,
}

/// [`NamelessFolder::fold`]'s machine: an explicit step stack in place of the
/// call stack, since the tree depth is script-controlled.
///
/// Children are pushed in reverse so they pop — and so land on `done` — in
/// source order. Clauses collect on their own stack, LIFO like `done`: a
/// clause's subtree (and any `when` nested in it) completes before the next
/// clause step runs.
fn fold_machine<F: NamelessFolder + ?Sized>(folder: &mut F, expr: NamelessExpr) -> NamelessExpr {
    fn take(done: &mut Vec<NamelessExpr>, n: usize) -> Vec<NamelessExpr> {
        let at = done.len() - n;
        done.split_off(at)
    }

    let mut steps: Vec<FoldStep> = vec![FoldStep::Visit(expr)];
    let mut done: Vec<NamelessExpr> = Vec::new();
    let mut clauses_done: Vec<NamelessClause> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            FoldStep::Visit(expr) => {
                if let NamelessFoldAction::Replace(replacement) = folder.pre_expr(&expr) {
                    done.push(replacement);
                    continue;
                }
                let leaf = match expr {
                    NamelessExpr::Int(n) => folder.post_int(n),
                    NamelessExpr::ByteArray(bytes) => folder.post_byte_array(bytes),
                    NamelessExpr::String(s) => folder.post_string(s),
                    NamelessExpr::Bool(b) => folder.post_bool(b),
                    NamelessExpr::Unit => folder.post_unit(),
                    NamelessExpr::Var(id) => folder.post_var(id),
                    NamelessExpr::Error { message } => folder.post_error(message),
                    NamelessExpr::Raw { uplc, reason } => folder.post_raw(uplc, reason),
                    NamelessExpr::Data(data) => folder.post_data(data),
                    NamelessExpr::HelperSymbol(intrinsic) => folder.post_helper_symbol(intrinsic),
                    NamelessExpr::Lambda { params, body } => {
                        folder.enter_lambda(&params);
                        steps.push(FoldStep::Build(FoldBuild::Lambda { params }));
                        steps.push(FoldStep::Visit(body.into_inner()));
                        continue;
                    }
                    NamelessExpr::RecFn { name, params, body } => {
                        folder.enter_recfn(name, &params);
                        steps.push(FoldStep::Build(FoldBuild::RecFn { name, params }));
                        steps.push(FoldStep::Visit(body.into_inner()));
                        continue;
                    }
                    NamelessExpr::Apply { function, args } => {
                        steps.push(FoldStep::Build(FoldBuild::Apply { argc: args.len() }));
                        for a in args.into_iter().rev() {
                            steps.push(FoldStep::Visit(a));
                        }
                        steps.push(FoldStep::Visit(function.into_inner()));
                        continue;
                    }
                    NamelessExpr::Let {
                        binder,
                        value,
                        body,
                    } => {
                        // The binding comes into scope BETWEEN the value and
                        // the body, so opening it is a step of its own.
                        steps.push(FoldStep::LetBody {
                            binder,
                            body: body.into_inner(),
                        });
                        steps.push(FoldStep::Visit(value.into_inner()));
                        continue;
                    }
                    NamelessExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        steps.push(FoldStep::Build(FoldBuild::If));
                        steps.push(FoldStep::Visit(else_branch.into_inner()));
                        steps.push(FoldStep::Visit(then_branch.into_inner()));
                        steps.push(FoldStep::Visit(condition.into_inner()));
                        continue;
                    }
                    NamelessExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        steps.push(FoldStep::WhenClauses {
                            subject_name,
                            clauses,
                        });
                        steps.push(FoldStep::Visit(subject.into_inner()));
                        continue;
                    }
                    NamelessExpr::List { elements, tail } => {
                        steps.push(FoldStep::Build(FoldBuild::List {
                            count: elements.len(),
                            has_tail: tail.is_some(),
                        }));
                        if let Some(t) = tail {
                            steps.push(FoldStep::Visit(t.into_inner()));
                        }
                        for e in elements.into_iter().rev() {
                            steps.push(FoldStep::Visit(e));
                        }
                        continue;
                    }
                    NamelessExpr::Tuple(items) => {
                        steps.push(FoldStep::Build(FoldBuild::Tuple { count: items.len() }));
                        for i in items.into_iter().rev() {
                            steps.push(FoldStep::Visit(i));
                        }
                        continue;
                    }
                    NamelessExpr::Pair(first, second) => {
                        steps.push(FoldStep::Build(FoldBuild::Pair));
                        steps.push(FoldStep::Visit(second.into_inner()));
                        steps.push(FoldStep::Visit(first.into_inner()));
                        continue;
                    }
                    NamelessExpr::Constr {
                        type_hint,
                        tag,
                        fields,
                        shape,
                    } => {
                        steps.push(FoldStep::Build(FoldBuild::Constr {
                            type_hint,
                            tag,
                            count: fields.len(),
                            shape,
                        }));
                        for f in fields.into_iter().rev() {
                            steps.push(FoldStep::Visit(f));
                        }
                        continue;
                    }
                    NamelessExpr::FieldAccess { record, selector } => {
                        steps.push(FoldStep::Build(FoldBuild::FieldAccess { selector }));
                        steps.push(FoldStep::Visit(record.into_inner()));
                        continue;
                    }
                    NamelessExpr::IndexAccess { collection, index } => {
                        steps.push(FoldStep::Build(FoldBuild::IndexAccess { index }));
                        steps.push(FoldStep::Visit(collection.into_inner()));
                        continue;
                    }
                    NamelessExpr::BinOp { op, left, right } => {
                        steps.push(FoldStep::Build(FoldBuild::BinOp { op }));
                        steps.push(FoldStep::Visit(right.into_inner()));
                        steps.push(FoldStep::Visit(left.into_inner()));
                        continue;
                    }
                    NamelessExpr::UnOp { op, operand } => {
                        steps.push(FoldStep::Build(FoldBuild::UnOp { op }));
                        steps.push(FoldStep::Visit(operand.into_inner()));
                        continue;
                    }
                    NamelessExpr::BuiltinCall { name, args } => {
                        steps.push(FoldStep::Build(FoldBuild::BuiltinCall {
                            name,
                            argc: args.len(),
                        }));
                        for a in args.into_iter().rev() {
                            steps.push(FoldStep::Visit(a));
                        }
                        continue;
                    }
                    NamelessExpr::Delay(inner) => {
                        steps.push(FoldStep::Build(FoldBuild::Delay));
                        steps.push(FoldStep::Visit(inner.into_inner()));
                        continue;
                    }
                    NamelessExpr::Force(inner) => {
                        steps.push(FoldStep::Build(FoldBuild::Force));
                        steps.push(FoldStep::Visit(inner.into_inner()));
                        continue;
                    }
                    NamelessExpr::Trace { message, value } => {
                        steps.push(FoldStep::Build(FoldBuild::Trace));
                        steps.push(FoldStep::Visit(value.into_inner()));
                        steps.push(FoldStep::Visit(message.into_inner()));
                        continue;
                    }
                };
                let finished = folder.post_expr(leaf);
                done.push(finished);
            }
            FoldStep::LetBody { binder, body } => {
                folder.enter_let(binder, done.last().expect("let value"));
                steps.push(FoldStep::Build(FoldBuild::Let { binder }));
                steps.push(FoldStep::Visit(body));
            }
            FoldStep::WhenClauses {
                subject_name,
                clauses,
            } => {
                folder.enter_when(done.last().expect("when subject"), subject_name);
                steps.push(FoldStep::Build(FoldBuild::When {
                    subject_name,
                    clause_count: clauses.len(),
                }));
                for clause in clauses.into_iter().rev() {
                    steps.push(FoldStep::Clause(clause));
                }
            }
            FoldStep::Clause(clause) => {
                folder.enter_clause(&clause.pattern);
                let NamelessClause {
                    pattern,
                    guard,
                    body,
                } = clause;
                steps.push(FoldStep::ClauseDone {
                    pattern,
                    has_guard: guard.is_some(),
                });
                steps.push(FoldStep::Visit(body));
                if let Some(guard) = guard {
                    steps.push(FoldStep::Visit(guard));
                }
            }
            FoldStep::ClauseDone { pattern, has_guard } => {
                let body = done.pop().expect("clause body");
                let guard = has_guard.then(|| done.pop().expect("clause guard"));
                let clause = NamelessClause {
                    pattern,
                    guard,
                    body,
                };
                folder.exit_clause(&clause.pattern);
                clauses_done.push(clause);
            }
            FoldStep::Build(build) => {
                let rebuilt = match build {
                    FoldBuild::Lambda { params } => {
                        let body = done.pop().expect("lambda body");
                        folder.exit_lambda(&params);
                        folder.post_lambda(params, body)
                    }
                    FoldBuild::RecFn { name, params } => {
                        let body = done.pop().expect("recfn body");
                        folder.exit_recfn(name, &params);
                        folder.post_recfn(name, params, body)
                    }
                    FoldBuild::Apply { argc } => {
                        let args = take(&mut done, argc);
                        let function = done.pop().expect("apply function");
                        folder.post_apply(function, args)
                    }
                    FoldBuild::Let { binder } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        folder.exit_let(binder);
                        folder.post_let(binder, value, body)
                    }
                    FoldBuild::If => {
                        let else_branch = done.pop().expect("if else");
                        let then_branch = done.pop().expect("if then");
                        let condition = done.pop().expect("if condition");
                        folder.post_if(condition, then_branch, else_branch)
                    }
                    FoldBuild::When {
                        subject_name,
                        clause_count,
                    } => {
                        let at = clauses_done.len() - clause_count;
                        let clauses = clauses_done.split_off(at);
                        let subject = done.pop().expect("when subject");
                        folder.exit_when(subject_name);
                        folder.post_when(subject, subject_name, clauses)
                    }
                    FoldBuild::List { count, has_tail } => {
                        let tail = has_tail.then(|| done.pop().expect("list tail"));
                        let elements = take(&mut done, count);
                        folder.post_list(elements, tail)
                    }
                    FoldBuild::Tuple { count } => {
                        let items = take(&mut done, count);
                        folder.post_tuple(items)
                    }
                    FoldBuild::Pair => {
                        let second = done.pop().expect("pair second");
                        let first = done.pop().expect("pair first");
                        folder.post_pair(first, second)
                    }
                    FoldBuild::Constr {
                        type_hint,
                        tag,
                        count,
                        shape,
                    } => {
                        let fields = take(&mut done, count);
                        folder.post_constr(type_hint, tag, fields, shape)
                    }
                    FoldBuild::FieldAccess { selector } => {
                        let record = done.pop().expect("field access record");
                        folder.post_field_access(record, selector)
                    }
                    FoldBuild::IndexAccess { index } => {
                        let collection = done.pop().expect("index access collection");
                        folder.post_index_access(collection, index)
                    }
                    FoldBuild::BinOp { op } => {
                        let right = done.pop().expect("binop right");
                        let left = done.pop().expect("binop left");
                        folder.post_binop(op, left, right)
                    }
                    FoldBuild::UnOp { op } => {
                        let operand = done.pop().expect("unop operand");
                        folder.post_unop(op, operand)
                    }
                    FoldBuild::BuiltinCall { name, argc } => {
                        let args = take(&mut done, argc);
                        folder.post_builtin_call(name, args)
                    }
                    FoldBuild::Delay => {
                        let inner = done.pop().expect("delay inner");
                        folder.post_delay(inner)
                    }
                    FoldBuild::Force => {
                        let inner = done.pop().expect("force inner");
                        folder.post_force(inner)
                    }
                    FoldBuild::Trace => {
                        let value = done.pop().expect("trace value");
                        let message = done.pop().expect("trace message");
                        folder.post_trace(message, value)
                    }
                };
                let finished = folder.post_expr(rebuilt);
                done.push(finished);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "the fold machine must leave one result");
    debug_assert!(clauses_done.is_empty(), "all clauses must be consumed");
    done.pop().expect("fold result")
}

/// Count `Var(target)` references reachable in `expr`, so passes
/// needing this analysis don't duplicate the [`NamelessVisitor`]
/// wrapper.
pub(crate) fn count_var_uses(expr: &NamelessExpr, target: VarId) -> usize {
    struct Counter {
        target: VarId,
        count: usize,
    }
    impl NamelessVisitor for Counter {
        fn visit_var(&mut self, id: VarId) {
            if id == self.target {
                self.count += 1;
            }
        }
    }
    let mut counter = Counter { target, count: 0 };
    counter.walk(expr);
    counter.count
}

/// Controls whether [`NamelessVisitor::walk`] recurses into a node's
/// children after the pre-visit hook fires.
///
/// Mirrors `NamelessFoldAction` but for read-only walks: `Skip` lets a
/// pass opt out of recursing into deferred subtrees (Lambda / RecFn /
/// Delay) when its analysis only cares about the eager evaluation
/// path.
pub(crate) enum VisitAction {
    /// Recurse into children.
    Walk,
    /// Skip this subtree's children. Lifecycle exit_* hooks for the
    /// current node still fire.
    Skip,
}

/// Read-only walker for [`NamelessExpr`].
///
/// Mirrors `pseudo::fold::ExprVisitor` for the nameless IR: no-op
/// default hooks let a pass override only what it cares about, and
/// lifecycle hooks fire around each binder-introducing node.
///
/// Use it for analysis passes — counting uses, collecting binders,
/// detecting markers — that don't transform the AST; unlike a
/// hand-rolled match-and-recurse it covers every variant. Override
/// `visit_expr` to return `VisitAction::Skip` to opt out of a
/// subtree's children, as `contains_explicit_error` does for
/// deferred subtrees.
pub(crate) trait NamelessVisitor {
    /// Pre-visit hook. Default returns `Walk`; override to `Skip` to
    /// opt out of recursing into the children of `expr`.
    fn visit_expr(&mut self, _expr: &NamelessExpr) -> VisitAction {
        VisitAction::Walk
    }

    // Variable / leaf hooks --------

    fn visit_var(&mut self, _id: VarId) {}

    // Lifecycle hooks --------

    fn enter_lambda(&mut self, _params: &[VarId]) {}
    fn exit_lambda(&mut self, _params: &[VarId]) {}
    fn enter_recfn(&mut self, _name: VarId, _params: &[VarId]) {}
    fn exit_recfn(&mut self, _name: VarId, _params: &[VarId]) {}
    fn enter_let(&mut self, _binder: VarId, _value: &NamelessExpr) {}
    fn exit_let(&mut self, _binder: VarId) {}
    fn enter_when(&mut self, _subject: &NamelessExpr, _subject_name: Option<VarId>) {}
    fn exit_when(&mut self, _subject_name: Option<VarId>) {}
    fn enter_clause(&mut self, _pattern: &NamelessPattern) {}
    fn exit_clause(&mut self, _pattern: &NamelessPattern) {}

    // Driver --------

    fn walk(&mut self, expr: &NamelessExpr) {
        enum Step<'e> {
            Visit(&'e NamelessExpr),
            ExitLambda(&'e [VarId]),
            ExitRecfn(VarId, &'e [VarId]),
            EnterLetBody {
                binder: VarId,
                value: &'e NamelessExpr,
                body: &'e NamelessExpr,
            },
            ExitLet(VarId),
            AfterWhenSubject {
                subject: &'e NamelessExpr,
                subject_name: Option<VarId>,
                clauses: &'e [NamelessClause],
            },
            ExitWhen(Option<VarId>),
            EnterClauseBody {
                pattern: &'e NamelessPattern,
                guard: Option<&'e NamelessExpr>,
                body: &'e NamelessExpr,
            },
            ExitClause(&'e NamelessPattern),
        }

        let mut steps: Vec<Step<'_>> = vec![Step::Visit(expr)];
        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(expr) => {
                    if matches!(self.visit_expr(expr), VisitAction::Skip) {
                        continue;
                    }
                    match expr {
                        NamelessExpr::Var(id) => self.visit_var(*id),
                        NamelessExpr::Lambda { params, body } => {
                            self.enter_lambda(params);
                            steps.push(Step::ExitLambda(params));
                            steps.push(Step::Visit(body));
                        }
                        NamelessExpr::RecFn { name, params, body } => {
                            self.enter_recfn(*name, params);
                            steps.push(Step::ExitRecfn(*name, params));
                            steps.push(Step::Visit(body));
                        }
                        NamelessExpr::Apply { function, args } => {
                            for a in args.iter().rev() {
                                steps.push(Step::Visit(a));
                            }
                            steps.push(Step::Visit(function));
                        }
                        NamelessExpr::Let {
                            binder,
                            value,
                            body,
                        } => {
                            steps.push(Step::EnterLetBody {
                                binder: *binder,
                                value,
                                body,
                            });
                            steps.push(Step::Visit(value));
                        }
                        NamelessExpr::If {
                            condition,
                            then_branch,
                            else_branch,
                        } => {
                            steps.push(Step::Visit(else_branch));
                            steps.push(Step::Visit(then_branch));
                            steps.push(Step::Visit(condition));
                        }
                        NamelessExpr::When {
                            subject,
                            subject_name,
                            clauses,
                        } => {
                            steps.push(Step::AfterWhenSubject {
                                subject,
                                subject_name: *subject_name,
                                clauses,
                            });
                            steps.push(Step::Visit(subject));
                        }
                        NamelessExpr::List { elements, tail } => {
                            if let Some(t) = tail {
                                steps.push(Step::Visit(t));
                            }
                            for e in elements.iter().rev() {
                                steps.push(Step::Visit(e));
                            }
                        }
                        NamelessExpr::Tuple(items) => {
                            for i in items.iter().rev() {
                                steps.push(Step::Visit(i));
                            }
                        }
                        NamelessExpr::Pair(a, b) => {
                            steps.push(Step::Visit(b));
                            steps.push(Step::Visit(a));
                        }
                        NamelessExpr::Constr { fields, .. } => {
                            for f in fields.iter().rev() {
                                steps.push(Step::Visit(f));
                            }
                        }
                        NamelessExpr::FieldAccess { record, .. } => {
                            steps.push(Step::Visit(record));
                        }
                        NamelessExpr::IndexAccess { collection, .. } => {
                            steps.push(Step::Visit(collection));
                        }
                        NamelessExpr::BinOp { left, right, .. } => {
                            steps.push(Step::Visit(right));
                            steps.push(Step::Visit(left));
                        }
                        NamelessExpr::UnOp { operand, .. } => {
                            steps.push(Step::Visit(operand));
                        }
                        NamelessExpr::BuiltinCall { args, .. } => {
                            for a in args.iter().rev() {
                                steps.push(Step::Visit(a));
                            }
                        }
                        NamelessExpr::Delay(inner) | NamelessExpr::Force(inner) => {
                            steps.push(Step::Visit(inner));
                        }
                        NamelessExpr::Trace { message, value } => {
                            steps.push(Step::Visit(value));
                            steps.push(Step::Visit(message));
                        }
                        // Leaves with no children.
                        NamelessExpr::Int(_)
                        | NamelessExpr::ByteArray(_)
                        | NamelessExpr::String(_)
                        | NamelessExpr::Bool(_)
                        | NamelessExpr::Unit
                        | NamelessExpr::Error { .. }
                        | NamelessExpr::Raw { .. }
                        | NamelessExpr::Data(_)
                        | NamelessExpr::HelperSymbol(_) => {}
                    }
                }
                Step::ExitLambda(params) => self.exit_lambda(params),
                Step::ExitRecfn(name, params) => self.exit_recfn(name, params),
                Step::EnterLetBody {
                    binder,
                    value,
                    body,
                } => {
                    self.enter_let(binder, value);
                    steps.push(Step::ExitLet(binder));
                    steps.push(Step::Visit(body));
                }
                Step::ExitLet(binder) => self.exit_let(binder),
                Step::AfterWhenSubject {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    self.enter_when(subject, subject_name);
                    steps.push(Step::ExitWhen(subject_name));
                    for c in clauses.iter().rev() {
                        steps.push(Step::EnterClauseBody {
                            pattern: &c.pattern,
                            guard: c.guard.as_ref(),
                            body: &c.body,
                        });
                    }
                }
                Step::ExitWhen(subject_name) => self.exit_when(subject_name),
                Step::EnterClauseBody {
                    pattern,
                    guard,
                    body,
                } => {
                    self.enter_clause(pattern);
                    steps.push(Step::ExitClause(pattern));
                    steps.push(Step::Visit(body));
                    if let Some(g) = guard {
                        steps.push(Step::Visit(g));
                    }
                }
                Step::ExitClause(pattern) => self.exit_clause(pattern),
            }
        }
    }
}

#[cfg(test)]
mod tests;
