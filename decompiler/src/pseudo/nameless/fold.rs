//! Generic folder trait for [`NamelessExpr`] transformations.
//!
//! Mirrors `pseudo::fold::ExprFolder` but for the nameless IR.
//! Identity-default `post_*` hooks let a pass override only the
//! variants it cares about; the `fold` driver recurses into
//! children before invoking the hook.

use super::{NamelessClause, NamelessExpr, NamelessPattern};
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
            body: Box::new(body),
        }
    }
    fn post_recfn(&mut self, name: VarId, params: Vec<VarId>, body: NamelessExpr) -> NamelessExpr {
        NamelessExpr::RecFn {
            name,
            params,
            body: Box::new(body),
        }
    }
    fn post_apply(&mut self, function: NamelessExpr, args: Vec<NamelessExpr>) -> NamelessExpr {
        NamelessExpr::Apply {
            function: Box::new(function),
            args,
        }
    }
    fn post_let(&mut self, binder: VarId, value: NamelessExpr, body: NamelessExpr) -> NamelessExpr {
        NamelessExpr::Let {
            binder,
            value: Box::new(value),
            body: Box::new(body),
        }
    }
    fn post_if(
        &mut self,
        condition: NamelessExpr,
        then_branch: NamelessExpr,
        else_branch: NamelessExpr,
    ) -> NamelessExpr {
        NamelessExpr::If {
            condition: Box::new(condition),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        }
    }
    fn post_when(
        &mut self,
        subject: NamelessExpr,
        subject_name: Option<VarId>,
        clauses: Vec<NamelessClause>,
    ) -> NamelessExpr {
        NamelessExpr::When {
            subject: Box::new(subject),
            subject_name,
            clauses,
        }
    }
    fn post_list(
        &mut self,
        elements: Vec<NamelessExpr>,
        tail: Option<NamelessExpr>,
    ) -> NamelessExpr {
        NamelessExpr::List {
            elements,
            tail: tail.map(Box::new),
        }
    }
    fn post_tuple(&mut self, items: Vec<NamelessExpr>) -> NamelessExpr {
        NamelessExpr::Tuple(items)
    }
    fn post_pair(&mut self, first: NamelessExpr, second: NamelessExpr) -> NamelessExpr {
        NamelessExpr::Pair(Box::new(first), Box::new(second))
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
            fields,
            shape,
        }
    }
    fn post_field_access(&mut self, record: NamelessExpr, selector: FieldSelector) -> NamelessExpr {
        NamelessExpr::FieldAccess {
            record: Box::new(record),
            selector,
        }
    }
    fn post_index_access(&mut self, collection: NamelessExpr, index: usize) -> NamelessExpr {
        NamelessExpr::IndexAccess {
            collection: Box::new(collection),
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
            left: Box::new(left),
            right: Box::new(right),
        }
    }
    fn post_unop(&mut self, op: UnaryOp, operand: NamelessExpr) -> NamelessExpr {
        NamelessExpr::UnOp {
            op,
            operand: Box::new(operand),
        }
    }
    fn post_builtin_call(
        &mut self,
        name: crate::BuiltinId,
        args: Vec<NamelessExpr>,
    ) -> NamelessExpr {
        NamelessExpr::BuiltinCall { name, args }
    }
    fn post_error(&mut self, message: Option<String>) -> NamelessExpr {
        NamelessExpr::Error { message }
    }
    fn post_delay(&mut self, inner: NamelessExpr) -> NamelessExpr {
        NamelessExpr::Delay(Box::new(inner))
    }
    fn post_force(&mut self, inner: NamelessExpr) -> NamelessExpr {
        NamelessExpr::Force(Box::new(inner))
    }
    fn post_trace(&mut self, message: NamelessExpr, value: NamelessExpr) -> NamelessExpr {
        NamelessExpr::Trace {
            message: Box::new(message),
            value: Box::new(value),
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

    fn fold(&mut self, expr: NamelessExpr) -> NamelessExpr {
        match self.pre_expr(&expr) {
            NamelessFoldAction::Replace(replacement) => return replacement,
            NamelessFoldAction::Walk => {}
        }
        let folded = self.fold_inner(expr);
        self.post_expr(folded)
    }

    fn fold_inner(&mut self, expr: NamelessExpr) -> NamelessExpr {
        match expr {
            NamelessExpr::Int(n) => self.post_int(n),
            NamelessExpr::ByteArray(bytes) => self.post_byte_array(bytes),
            NamelessExpr::String(s) => self.post_string(s),
            NamelessExpr::Bool(b) => self.post_bool(b),
            NamelessExpr::Unit => self.post_unit(),
            NamelessExpr::Var(id) => self.post_var(id),
            NamelessExpr::Lambda { params, body } => {
                self.enter_lambda(&params);
                let body = self.fold(*body);
                self.exit_lambda(&params);
                self.post_lambda(params, body)
            }
            NamelessExpr::RecFn { name, params, body } => {
                self.enter_recfn(name, &params);
                let body = self.fold(*body);
                self.exit_recfn(name, &params);
                self.post_recfn(name, params, body)
            }
            NamelessExpr::Apply { function, args } => {
                let function = self.fold(*function);
                let args = args.into_iter().map(|a| self.fold(a)).collect();
                self.post_apply(function, args)
            }
            NamelessExpr::Let {
                binder,
                value,
                body,
            } => {
                let value = self.fold(*value);
                self.enter_let(binder, &value);
                let body = self.fold(*body);
                self.exit_let(binder);
                self.post_let(binder, value, body)
            }
            NamelessExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition = self.fold(*condition);
                let then_branch = self.fold(*then_branch);
                let else_branch = self.fold(*else_branch);
                self.post_if(condition, then_branch, else_branch)
            }
            NamelessExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                let subject = self.fold(*subject);
                self.enter_when(&subject, subject_name);
                let clauses = clauses.into_iter().map(|c| self.fold_clause(c)).collect();
                self.exit_when(subject_name);
                self.post_when(subject, subject_name, clauses)
            }
            NamelessExpr::List { elements, tail } => {
                let elements = elements.into_iter().map(|e| self.fold(e)).collect();
                let tail = tail.map(|t| self.fold(*t));
                self.post_list(elements, tail)
            }
            NamelessExpr::Tuple(items) => {
                let items = items.into_iter().map(|i| self.fold(i)).collect();
                self.post_tuple(items)
            }
            NamelessExpr::Pair(first, second) => {
                let first = self.fold(*first);
                let second = self.fold(*second);
                self.post_pair(first, second)
            }
            NamelessExpr::Constr {
                type_hint,
                tag,
                fields,
                shape,
            } => {
                let fields = fields.into_iter().map(|f| self.fold(f)).collect();
                self.post_constr(type_hint, tag, fields, shape)
            }
            NamelessExpr::FieldAccess { record, selector } => {
                let record = self.fold(*record);
                self.post_field_access(record, selector)
            }
            NamelessExpr::IndexAccess { collection, index } => {
                let collection = self.fold(*collection);
                self.post_index_access(collection, index)
            }
            NamelessExpr::BinOp { op, left, right } => {
                let left = self.fold(*left);
                let right = self.fold(*right);
                self.post_binop(op, left, right)
            }
            NamelessExpr::UnOp { op, operand } => {
                let operand = self.fold(*operand);
                self.post_unop(op, operand)
            }
            NamelessExpr::BuiltinCall { name, args } => {
                let args = args.into_iter().map(|a| self.fold(a)).collect();
                self.post_builtin_call(name, args)
            }
            NamelessExpr::Error { message } => self.post_error(message),
            NamelessExpr::Delay(inner) => {
                let inner = self.fold(*inner);
                self.post_delay(inner)
            }
            NamelessExpr::Force(inner) => {
                let inner = self.fold(*inner);
                self.post_force(inner)
            }
            NamelessExpr::Trace { message, value } => {
                let message = self.fold(*message);
                let value = self.fold(*value);
                self.post_trace(message, value)
            }
            NamelessExpr::Raw { uplc, reason } => self.post_raw(uplc, reason),
            NamelessExpr::Data(data) => self.post_data(data),
            NamelessExpr::HelperSymbol(intrinsic) => self.post_helper_symbol(intrinsic),
        }
    }

    fn fold_clause(&mut self, clause: NamelessClause) -> NamelessClause {
        self.enter_clause(&clause.pattern);
        let result = NamelessClause {
            guard: clause.guard.map(|g| self.fold(g)),
            body: self.fold(clause.body),
            pattern: clause.pattern,
        };
        self.exit_clause(&result.pattern);
        result
    }
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
