//! Generic AST traversal traits for PseudoExpr.
//!
//! Provides `ExprFolder` for bottom-up transformations and `ExprVisitor`
//! for read-only walks, eliminating manual traversal boilerplate.

use crate::builtins::BuiltinId;
use crate::pseudo::ast::PBox;

use super::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use super::constructor::ConstructorShape;
use super::field_selector::FieldSelector;
use super::var_id::VarId;

/// Controls whether the folder recurses into children or replaces the node.
pub(crate) enum FoldAction {
    /// Recurse into children, then call the appropriate `post_*` hook.
    Walk,
    /// Replace the node with this expression (skip recursion).
    Replace(PseudoExpr),
}

/// One pending step of [`ExprFolder::fold_inner`].
pub(crate) enum FoldStep {
    /// Fold this subtree.
    Enter(PseudoExpr),
    /// Its children are done: reassemble the node.
    Post(PostKind),
}

/// The node a [`FoldStep::Post`] reassembles, carrying the parts that are not
/// children.
pub(crate) enum PostKind {
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    Apply {
        argc: usize,
    },
    /// The value is folded; open the binding and fold the body under it.
    LetBody {
        name: String,
        id: Option<VarId>,
        body: PBox,
    },
    LetPost {
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
    },
    If,
    /// Rebuild a `when` from the children on `done`.
    ///
    /// `clause_meta` holds each clause's non-expression parts: the pattern
    /// unless it is a `Literal` (whose payload is a child and comes back off
    /// `done`), and whether the clause had a guard.
    When {
        subject_name: Option<Binder>,
        clause_meta: Vec<(Option<WhenPattern>, bool)>,
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
        name: BuiltinId,
        argc: usize,
    },
    Delay,
    Force,
    Trace,
}

/// Trait for bottom-up AST transformations.
///
/// Override `pre_expr` to intercept before recursion.
/// Override `post_*` methods to transform after children are folded.
/// Default implementations reconstruct the same node.
pub(crate) trait ExprFolder {
    /// Called before recursing into any node. Return `Walk` to continue
    /// into children, or `Replace(expr)` to substitute without recursing.
    fn pre_expr(&mut self, _expr: &PseudoExpr) -> FoldAction {
        FoldAction::Walk
    }

    /// Called before recursing into a `Let`'s value — after `pre_expr`
    /// returns `Walk`, before `value` is folded. `Walk` continues the
    /// standard value → `enter_let` → body → `exit_let` → `post_let`
    /// flow; `Replace(expr)` substitutes the whole `Let` subtree
    /// without recursing into either child.
    ///
    /// Pairs with `post_let` for scope-aware passes that must register
    /// state before value simplification begins.
    fn pre_let(
        &mut self,
        _name: &str,
        _id: &Option<VarId>,
        _value: &PseudoExpr,
        _body: &PseudoExpr,
    ) -> FoldAction {
        FoldAction::Walk
    }

    /// Called after the node has been reconstructed through its `post_*`
    /// hook, so bottom-up root rewrites need no separate recursive walker.
    fn post_expr(&mut self, expr: PseudoExpr) -> PseudoExpr {
        expr
    }

    // Post-visit hooks (called after children are folded) ----

    fn post_int(&mut self, n: num_bigint::BigInt) -> PseudoExpr {
        PseudoExpr::Int(n)
    }

    fn post_byte_array(&mut self, bytes: Vec<u8>) -> PseudoExpr {
        PseudoExpr::ByteArray(bytes)
    }

    fn post_string(&mut self, s: String) -> PseudoExpr {
        PseudoExpr::String(s)
    }

    fn post_bool(&mut self, b: bool) -> PseudoExpr {
        PseudoExpr::Bool(b)
    }

    fn post_unit(&mut self) -> PseudoExpr {
        PseudoExpr::Unit
    }

    fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
        PseudoExpr::Var { name, id }
    }

    fn post_lambda(&mut self, params: Vec<Binder>, body: PseudoExpr) -> PseudoExpr {
        PseudoExpr::Lambda {
            params,
            body: PBox::new(body),
        }
    }

    fn post_recfn(
        &mut self,
        name: crate::pseudo::ast::Binder,
        params: Vec<crate::pseudo::ast::Binder>,
        body: PseudoExpr,
    ) -> PseudoExpr {
        PseudoExpr::RecFn {
            name,
            params,
            body: PBox::new(body),
        }
    }

    fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
        PseudoExpr::Apply {
            function: PBox::new(function),
            args: args.into(),
        }
    }

    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }

    fn post_if(
        &mut self,
        condition: PseudoExpr,
        then_branch: PseudoExpr,
        else_branch: PseudoExpr,
    ) -> PseudoExpr {
        PseudoExpr::If {
            condition: PBox::new(condition),
            then_branch: PBox::new(then_branch),
            else_branch: PBox::new(else_branch),
        }
    }

    fn post_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name,
            clauses,
        }
    }

    fn post_list(&mut self, elements: Vec<PseudoExpr>, tail: Option<PseudoExpr>) -> PseudoExpr {
        PseudoExpr::List {
            elements: elements.into(),
            tail: tail.map(PBox::new),
        }
    }

    fn post_tuple(&mut self, elements: Vec<PseudoExpr>) -> PseudoExpr {
        PseudoExpr::Tuple(elements.into())
    }

    fn post_pair(&mut self, first: PseudoExpr, second: PseudoExpr) -> PseudoExpr {
        PseudoExpr::Pair(PBox::new(first), PBox::new(second))
    }

    fn post_constr(
        &mut self,
        type_hint: Option<crate::pseudo::type_hint::TypeHintId>,
        tag: usize,
        fields: Vec<PseudoExpr>,
        shape: ConstructorShape,
    ) -> PseudoExpr {
        PseudoExpr::Constr {
            type_hint,
            tag,
            fields: fields.into(),
            shape,
        }
    }

    fn post_field_access(&mut self, record: PseudoExpr, selector: FieldSelector) -> PseudoExpr {
        PseudoExpr::field_access_typed(record, selector)
    }

    fn post_index_access(&mut self, collection: PseudoExpr, index: usize) -> PseudoExpr {
        PseudoExpr::IndexAccess {
            collection: PBox::new(collection),
            index,
        }
    }

    fn post_binop(&mut self, op: BinaryOp, left: PseudoExpr, right: PseudoExpr) -> PseudoExpr {
        PseudoExpr::BinOp {
            op,
            left: PBox::new(left),
            right: PBox::new(right),
        }
    }

    fn post_unop(&mut self, op: UnaryOp, operand: PseudoExpr) -> PseudoExpr {
        PseudoExpr::UnOp {
            op,
            operand: PBox::new(operand),
        }
    }

    fn post_builtin_call(&mut self, name: BuiltinId, args: Vec<PseudoExpr>) -> PseudoExpr {
        PseudoExpr::BuiltinCall {
            name,
            args: args.into(),
        }
    }

    fn post_error(&mut self, message: Option<String>) -> PseudoExpr {
        PseudoExpr::Error { message }
    }

    fn post_delay(&mut self, inner: PseudoExpr) -> PseudoExpr {
        PseudoExpr::Delay(PBox::new(inner))
    }

    fn post_force(&mut self, inner: PseudoExpr) -> PseudoExpr {
        PseudoExpr::Force(PBox::new(inner))
    }

    fn post_trace(&mut self, message: PseudoExpr, value: PseudoExpr) -> PseudoExpr {
        PseudoExpr::Trace {
            message: PBox::new(message),
            value: PBox::new(value),
        }
    }

    fn post_raw(&mut self, uplc: String, reason: String) -> PseudoExpr {
        PseudoExpr::Raw { uplc, reason }
    }

    fn post_data(&mut self, data: Box<super::ast::PseudoData>) -> PseudoExpr {
        PseudoExpr::Data(data)
    }

    /// Opaque leaf, default = rebuild.
    fn post_helper_symbol(&mut self, intrinsic: super::ast::HelperIntrinsic) -> PseudoExpr {
        PseudoExpr::HelperSymbol(intrinsic)
    }

    // Scope hooks (called before recursing into binding bodies) ----
    // Override these for scope-tracking passes (rename, uniquify).

    /// Called before folding a Lambda body. Return new param names.
    fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
        params.to_vec()
    }

    /// Called after folding a Lambda body.
    fn exit_lambda(&mut self, _params: &[Binder]) {}

    /// Called before folding a RecFn body. Return (new_name, new_params).
    fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
        (name.clone(), params.to_vec())
    }

    /// Called after folding a RecFn body.
    fn exit_recfn(&mut self, _name: &Binder, _params: &[Binder]) {}

    /// Called after the value is folded, before the body. Return new name.
    fn enter_let(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) -> String {
        name.to_string()
    }

    /// Called after folding a Let body.
    fn exit_let(&mut self, _name: &str) {}

    /// Entry point. Folds an expression bottom-up with stack safety.
    fn fold(&mut self, expr: PseudoExpr) -> PseudoExpr {
        crate::stack::grow_deep(|| self.fold_inner(expr))
    }

    /// Inner fold — an iterative machine over an explicit step stack.
    ///
    /// The tree depth is script-controlled (a spine tens of thousands of nodes
    /// deep fits inside the Plutus size limit), and on `wasm32` the engine's
    /// call stack cannot be grown to match, so the descent must not sit on it.
    ///
    /// This is why no implementation may override `fold`: doing so takes the
    /// node away from this driver and puts its whole subtree back on the call
    /// stack. Intercept with [`Self::pre_expr`] or [`Self::fold_when`] instead.
    ///
    /// A kind is handled either here or by its arm in
    /// [`Self::fold_legacy_arm`] — never both, so the two cannot drift.
    fn fold_inner(&mut self, expr: PseudoExpr) -> PseudoExpr {
        let mut steps: Vec<FoldStep> = vec![FoldStep::Enter(expr)];
        let mut done: Vec<PseudoExpr> = Vec::new();

        while let Some(step) = steps.pop() {
            match step {
                FoldStep::Enter(expr) => {
                    if let FoldAction::Replace(e) = self.pre_expr(&expr) {
                        done.push(e);
                        continue;
                    }
                    self.enter_node(expr, &mut steps, &mut done);
                }
                FoldStep::Post(kind) => {
                    if let Some(rebuilt) = self.rebuild(kind, &mut done, &mut steps) {
                        let finished = self.post_expr(rebuilt);
                        done.push(finished);
                    }
                }
            }
        }

        debug_assert_eq!(done.len(), 1, "the fold machine must leave one result");
        done.pop().expect("fold result")
    }

    /// Queue a node's children, or emit it outright when it has none.
    ///
    /// Children are pushed in reverse so they pop — and so land on `done` — in
    /// source order.
    fn enter_node(
        &mut self,
        expr: PseudoExpr,
        steps: &mut Vec<FoldStep>,
        done: &mut Vec<PseudoExpr>,
    ) {
        match expr {
            PseudoExpr::Lambda { params, body } => {
                let params = self.enter_lambda(&params);
                steps.push(FoldStep::Post(PostKind::Lambda { params }));
                steps.push(FoldStep::Enter(body.into_inner()));
            }
            PseudoExpr::RecFn { name, params, body } => {
                let (name, params) = self.enter_recfn(&name, &params);
                steps.push(FoldStep::Post(PostKind::RecFn { name, params }));
                steps.push(FoldStep::Enter(body.into_inner()));
            }
            PseudoExpr::Apply { function, args } => {
                steps.push(FoldStep::Post(PostKind::Apply { argc: args.len() }));
                for arg in args.into_iter().rev() {
                    steps.push(FoldStep::Enter(arg));
                }
                steps.push(FoldStep::Enter(function.into_inner()));
            }
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                if let FoldAction::Replace(e) = self.pre_let(&name, &id, &value, &body) {
                    done.push(e);
                    return;
                }
                // The binding comes into scope BETWEEN the value and the body,
                // so opening it is a step of its own.
                steps.push(FoldStep::Post(PostKind::LetBody { name, id, body }));
                steps.push(FoldStep::Enter(value.into_inner()));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                steps.push(FoldStep::Post(PostKind::If));
                steps.push(FoldStep::Enter(else_branch.into_inner()));
                steps.push(FoldStep::Enter(then_branch.into_inner()));
                steps.push(FoldStep::Enter(condition.into_inner()));
            }
            PseudoExpr::List { elements, tail } => {
                steps.push(FoldStep::Post(PostKind::List {
                    count: elements.len(),
                    has_tail: tail.is_some(),
                }));
                if let Some(tail) = tail {
                    steps.push(FoldStep::Enter(tail.into_inner()));
                }
                for e in elements.into_iter().rev() {
                    steps.push(FoldStep::Enter(e));
                }
            }
            PseudoExpr::Tuple(elements) => {
                steps.push(FoldStep::Post(PostKind::Tuple {
                    count: elements.len(),
                }));
                for e in elements.into_iter().rev() {
                    steps.push(FoldStep::Enter(e));
                }
            }
            PseudoExpr::Pair(first, second) => {
                steps.push(FoldStep::Post(PostKind::Pair));
                steps.push(FoldStep::Enter(second.into_inner()));
                steps.push(FoldStep::Enter(first.into_inner()));
            }
            PseudoExpr::Constr {
                type_hint,
                tag,
                fields,
                shape,
            } => {
                steps.push(FoldStep::Post(PostKind::Constr {
                    type_hint,
                    tag,
                    count: fields.len(),
                    shape,
                }));
                for f in fields.into_iter().rev() {
                    steps.push(FoldStep::Enter(f));
                }
            }
            PseudoExpr::FieldAccess {
                record, selector, ..
            } => {
                steps.push(FoldStep::Post(PostKind::FieldAccess { selector }));
                steps.push(FoldStep::Enter(record.into_inner()));
            }
            PseudoExpr::IndexAccess { collection, index } => {
                steps.push(FoldStep::Post(PostKind::IndexAccess { index }));
                steps.push(FoldStep::Enter(collection.into_inner()));
            }
            PseudoExpr::BinOp { op, left, right } => {
                steps.push(FoldStep::Post(PostKind::BinOp { op }));
                steps.push(FoldStep::Enter(right.into_inner()));
                steps.push(FoldStep::Enter(left.into_inner()));
            }
            PseudoExpr::UnOp { op, operand } => {
                steps.push(FoldStep::Post(PostKind::UnOp { op }));
                steps.push(FoldStep::Enter(operand.into_inner()));
            }
            PseudoExpr::BuiltinCall { name, args } => {
                steps.push(FoldStep::Post(PostKind::BuiltinCall {
                    name,
                    argc: args.len(),
                }));
                for a in args.into_iter().rev() {
                    steps.push(FoldStep::Enter(a));
                }
            }
            PseudoExpr::Delay(inner) => {
                steps.push(FoldStep::Post(PostKind::Delay));
                steps.push(FoldStep::Enter(inner.into_inner()));
            }
            PseudoExpr::Force(inner) => {
                steps.push(FoldStep::Post(PostKind::Force));
                steps.push(FoldStep::Enter(inner.into_inner()));
            }
            PseudoExpr::Trace { message, value } => {
                steps.push(FoldStep::Post(PostKind::Trace));
                steps.push(FoldStep::Enter(value.into_inner()));
                steps.push(FoldStep::Enter(message.into_inner()));
            }
            // A `when` the implementation has handed to the machine: fold it
            // here rather than through `fold_when`, which would recurse once
            // per nesting level.
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } if self.machine_folds_when() => {
                let mut clause_meta = Vec::with_capacity(clauses.len());
                let mut clause_children: Vec<PseudoExpr> = Vec::new();
                for clause in clauses {
                    // Same order as `fold_clause`: pattern literal, guard, body.
                    let pattern = match clause.pattern {
                        WhenPattern::Literal(lit) => {
                            clause_children.push(lit);
                            None
                        }
                        other => Some(other),
                    };
                    let has_guard = clause.guard.is_some();
                    if let Some(guard) = clause.guard {
                        clause_children.push(guard);
                    }
                    clause_children.push(clause.body);
                    clause_meta.push((pattern, has_guard));
                }
                steps.push(FoldStep::Post(PostKind::When {
                    subject_name,
                    clause_meta,
                }));
                // Reversed so they pop in order; the subject goes last so it
                // pops first, as `fold_when` folded it first.
                for child in clause_children.into_iter().rev() {
                    steps.push(FoldStep::Enter(child));
                }
                steps.push(FoldStep::Enter(subject.into_inner()));
            }
            // Leaves, and any `when` not handed over — see `fold_legacy_arm`.
            other => {
                let folded = self.fold_legacy_arm(other);
                let finished = self.post_expr(folded);
                done.push(finished);
            }
        }
    }

    /// Reassemble a node from the children on `done` and run its `post_*` hook.
    ///
    /// `None` when the step only advanced the scope (a `let` opening its body),
    /// so the caller knows not to run `post_expr` for it.
    fn rebuild(
        &mut self,
        kind: PostKind,
        done: &mut Vec<PseudoExpr>,
        steps: &mut Vec<FoldStep>,
    ) -> Option<PseudoExpr> {
        fn take(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
            let at = done.len() - n;
            done.split_off(at)
        }
        Some(match kind {
            PostKind::Lambda { params } => {
                let body = done.pop().expect("lambda body");
                self.exit_lambda(&params);
                self.post_lambda(params, body)
            }
            PostKind::RecFn { name, params } => {
                let body = done.pop().expect("recfn body");
                self.exit_recfn(&name, &params);
                self.post_recfn(name, params, body)
            }
            PostKind::Apply { argc } => {
                let args = take(done, argc);
                let function = done.pop().expect("apply function");
                self.post_apply(function, args)
            }
            PostKind::LetBody { name, id, body } => {
                let value = done.pop().expect("let value");
                let name = self.enter_let(&name, &id, &value);
                steps.push(FoldStep::Post(PostKind::LetPost { name, id, value }));
                steps.push(FoldStep::Enter(body.into_inner()));
                return None;
            }
            PostKind::LetPost { name, id, value } => {
                let body = done.pop().expect("let body");
                self.exit_let(&name);
                self.post_let(name, id, value, body)
            }
            PostKind::When {
                subject_name,
                clause_meta,
            } => {
                let child_count: usize = clause_meta
                    .iter()
                    .map(|(pattern, has_guard)| {
                        usize::from(pattern.is_none()) + usize::from(*has_guard) + 1
                    })
                    .sum();
                // Clause children sit above the subject on `done`.
                let mut parts = take(done, child_count).into_iter();
                let subject = done.pop().expect("when subject");
                let clauses = clause_meta
                    .into_iter()
                    .map(|(pattern, has_guard)| WhenClause {
                        pattern: match pattern {
                            Some(pattern) => pattern,
                            None => {
                                WhenPattern::Literal(parts.next().expect("when clause literal"))
                            }
                        },
                        guard: has_guard.then(|| parts.next().expect("when clause guard")),
                        body: parts.next().expect("when clause body"),
                    })
                    .collect();
                self.post_when(subject, subject_name, clauses)
            }
            PostKind::If => {
                let mut parts = take(done, 3).into_iter();
                let condition = parts.next().expect("if condition");
                let then_branch = parts.next().expect("if then");
                let else_branch = parts.next().expect("if else");
                self.post_if(condition, then_branch, else_branch)
            }
            PostKind::List { count, has_tail } => {
                let tail = if has_tail { done.pop() } else { None };
                let elements = take(done, count);
                self.post_list(elements, tail)
            }
            PostKind::Tuple { count } => {
                let elements = take(done, count);
                self.post_tuple(elements)
            }
            PostKind::Pair => {
                let second = done.pop().expect("pair second");
                let first = done.pop().expect("pair first");
                self.post_pair(first, second)
            }
            PostKind::Constr {
                type_hint,
                tag,
                count,
                shape,
            } => {
                let fields = take(done, count);
                self.post_constr(type_hint, tag, fields, shape)
            }
            PostKind::FieldAccess { selector } => {
                let record = done.pop().expect("field access record");
                self.post_field_access(record, selector)
            }
            PostKind::IndexAccess { index } => {
                let collection = done.pop().expect("index access collection");
                self.post_index_access(collection, index)
            }
            PostKind::BinOp { op } => {
                let right = done.pop().expect("binop right");
                let left = done.pop().expect("binop left");
                self.post_binop(op, left, right)
            }
            PostKind::UnOp { op } => {
                let operand = done.pop().expect("unop operand");
                self.post_unop(op, operand)
            }
            PostKind::BuiltinCall { name, argc } => {
                let args = take(done, argc);
                self.post_builtin_call(name, args)
            }
            PostKind::Delay => {
                let inner = done.pop().expect("delay inner");
                self.post_delay(inner)
            }
            PostKind::Force => {
                let inner = done.pop().expect("force inner");
                self.post_force(inner)
            }
            PostKind::Trace => {
                let value = done.pop().expect("trace value");
                let message = done.pop().expect("trace message");
                self.post_trace(message, value)
            }
        })
    }

    /// The kinds not on the machine: the leaves, and `when` — whose clauses go
    /// through [`Self::fold_when`], a hook an implementation may replace.
    fn fold_legacy_arm(&mut self, expr: PseudoExpr) -> PseudoExpr {
        match expr {
            PseudoExpr::Int(n) => self.post_int(n),
            PseudoExpr::ByteArray(b) => self.post_byte_array(b),
            PseudoExpr::String(s) => self.post_string(s),
            PseudoExpr::Bool(b) => self.post_bool(b),
            PseudoExpr::Unit => self.post_unit(),
            PseudoExpr::Var { name, id } => self.post_var(name, id),
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => self.fold_when(subject.into_inner(), subject_name, clauses),
            PseudoExpr::Error { message } => self.post_error(message),
            PseudoExpr::Raw { uplc, reason } => self.post_raw(uplc, reason),
            PseudoExpr::Data(data) => self.post_data(data),
            PseudoExpr::HelperSymbol(intrinsic) => self.post_helper_symbol(intrinsic),
            other => unreachable!("{other:?} is folded by the machine"),
        }
    }

    /// Opt in to having the machine fold `when` nodes.
    ///
    /// Off by default, and deliberately so. Folding a `when` through
    /// [`Self::fold_when`] costs one call frame per nesting level, because
    /// the hook can only reach its children by re-entering [`Self::fold`] —
    /// the machine's step stack is not visible to it. The machine can do it
    /// flat instead, but only for an implementation that overrides **none**
    /// of `fold_when`, `fold_clause` and `fold_pattern`: the flat path
    /// reassembles the node itself and would silently skip all three.
    ///
    /// The default is "no" so that forgetting to opt in costs a stack frame,
    /// not correctness. Opting in wrongly is caught by the snapshot corpus.
    fn machine_folds_when(&self) -> bool {
        false
    }

    fn fold_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        let subject = self.fold(subject);
        let clauses = clauses.into_iter().map(|c| self.fold_clause(c)).collect();
        self.post_when(subject, subject_name, clauses)
    }

    fn fold_clause(&mut self, clause: WhenClause) -> WhenClause {
        let pattern = self.fold_pattern(clause.pattern);
        let guard = clause.guard.map(|g| self.fold(g));
        let body = self.fold(clause.body);
        WhenClause {
            pattern,
            guard,
            body,
        }
    }

    /// Fold patterns — only `Literal` patterns contain sub-expressions.
    fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
        match pattern {
            WhenPattern::Literal(expr) => WhenPattern::Literal(self.fold(expr)),
            other => other,
        }
    }
}

/// One step of the [`ExprVisitor`] walk.
///
/// `Visit` descends into a node; the other variants fire hooks between
/// children (`visit_let_value_post`, lambda/recfn `_post`, per-clause pre/post).
enum VisitStep<'a> {
    Visit(&'a PseudoExpr),
    LambdaPost(&'a [Binder]),
    RecFnPost(&'a Binder, &'a [Binder]),
    LetValuePost(&'a str, &'a Option<VarId>, &'a PseudoExpr),
    LetPost(&'a str),
    ClausePre(Option<&'a Binder>, &'a WhenClause),
    ClausePost(Option<&'a Binder>, &'a WhenClause),
}

/// Trait for read-only AST walks (counting, analysis).
///
/// Override `visit_*` methods to inspect nodes.
/// Default implementations do nothing.
pub(crate) trait ExprVisitor {
    /// Called for every variable reference.
    fn visit_var(&mut self, _name: &str, _id: &Option<VarId>) {}

    /// Called on a full let node before walking its value and body.
    fn visit_let(
        &mut self,
        _name: &str,
        _id: &Option<VarId>,
        _value: &PseudoExpr,
        _body: &PseudoExpr,
    ) {
    }

    /// Called when entering a let binding (before walking value/body).
    fn visit_let_pre(&mut self, _name: &str) {}

    /// Called after walking the bound value, but before walking the let body.
    fn visit_let_value_post(&mut self, _name: &str, _id: &Option<VarId>, _value: &PseudoExpr) {}

    /// Called when leaving a let binding (after walking value/body).
    fn visit_let_post(&mut self, _name: &str) {}

    /// Called when entering a lambda (before walking body).
    fn visit_lambda_pre(&mut self, _params: &[Binder]) {}

    /// Called when leaving a lambda.
    fn visit_lambda_post(&mut self, _params: &[Binder]) {}

    /// Called on a full recfn node before walking its body.
    fn visit_recfn(&mut self, _name: &Binder, _params: &[Binder], _body: &PseudoExpr) {}

    /// Called when entering a recfn (before walking body).
    fn visit_recfn_pre(&mut self, _name: &Binder, _params: &[Binder]) {}

    /// Called when leaving a recfn.
    fn visit_recfn_post(&mut self, _name: &Binder, _params: &[Binder]) {}

    /// Called on a `when` node before walking its subject, guards, and bodies.
    fn visit_when(
        &mut self,
        _subject: &PseudoExpr,
        _subject_name: Option<&Binder>,
        _clauses: &[WhenClause],
    ) {
    }

    /// Called after a clause's literal pattern expression has been walked,
    /// but before walking the clause guard and body.
    fn visit_when_clause_pre(&mut self, _subject_name: Option<&Binder>, _clause: &WhenClause) {}

    /// Called after walking the clause guard and body.
    fn visit_when_clause_post(&mut self, _subject_name: Option<&Binder>, _clause: &WhenClause) {}

    /// Called on an `apply` node before walking the callee and arguments.
    fn visit_apply(&mut self, _expr: &PseudoExpr, _function: &PseudoExpr, _args: &[PseudoExpr]) {}

    /// Called on a `force` node before walking its inner expression.
    fn visit_force(&mut self, _inner: &PseudoExpr) {}

    /// Entry point. Walks the expression with stack safety.
    fn walk(&mut self, expr: &PseudoExpr) {
        crate::stack::grow_deep(|| self.walk_inner(expr))
    }

    /// Inner walk — an explicit worklist over the tree.
    ///
    /// Same constraint as [`Self::fold_inner`]: script-controlled depth on a
    /// `wasm32` engine stack that cannot grow. Shared driver for every
    /// `ExprVisitor`.
    ///
    /// Hooks that must fire between children (`visit_let_value_post`, the
    /// lambda/recfn `_post` pair, per-clause pre/post) are explicit steps so
    /// they still run at that point in the traversal.
    fn walk_inner(&mut self, expr: &PseudoExpr) {
        let mut steps: Vec<VisitStep<'_>> = vec![VisitStep::Visit(expr)];

        while let Some(step) = steps.pop() {
            let node = match step {
                VisitStep::LambdaPost(params) => {
                    self.visit_lambda_post(params);
                    continue;
                }
                VisitStep::RecFnPost(name, params) => {
                    self.visit_recfn_post(name, params);
                    continue;
                }
                VisitStep::LetValuePost(name, id, value) => {
                    self.visit_let_value_post(name, id, value);
                    continue;
                }
                VisitStep::LetPost(name) => {
                    self.visit_let_post(name);
                    continue;
                }
                VisitStep::ClausePre(subject_name, clause) => {
                    self.visit_when_clause_pre(subject_name, clause);
                    continue;
                }
                VisitStep::ClausePost(subject_name, clause) => {
                    self.visit_when_clause_post(subject_name, clause);
                    continue;
                }
                VisitStep::Visit(node) => node,
            };

            // Children are pushed in reverse so they pop in source order.
            match node {
                PseudoExpr::Var { name, id } => {
                    self.visit_var(name, id);
                }

                PseudoExpr::Lambda { params, body } => {
                    self.visit_lambda_pre(params);
                    steps.push(VisitStep::LambdaPost(params));
                    steps.push(VisitStep::Visit(body));
                }

                PseudoExpr::RecFn { name, params, body } => {
                    self.visit_recfn(name, params, body);
                    self.visit_recfn_pre(name, params);
                    steps.push(VisitStep::RecFnPost(name, params));
                    steps.push(VisitStep::Visit(body));
                }

                PseudoExpr::Apply { function, args } => {
                    self.visit_apply(node, function, args);
                    steps.extend(args.iter().rev().map(VisitStep::Visit));
                    steps.push(VisitStep::Visit(function));
                }

                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    self.visit_let(name, id, value, body);
                    self.visit_let_pre(name);
                    steps.push(VisitStep::LetPost(name));
                    steps.push(VisitStep::Visit(body));
                    steps.push(VisitStep::LetValuePost(name, id, value));
                    steps.push(VisitStep::Visit(value));
                }

                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(VisitStep::Visit(else_branch));
                    steps.push(VisitStep::Visit(then_branch));
                    steps.push(VisitStep::Visit(condition));
                }

                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    self.visit_when(subject, subject_name.as_ref(), clauses);

                    // Built forwards, pushed reversed, so clauses run in source order.
                    let mut seq: Vec<VisitStep<'_>> = Vec::new();
                    seq.push(VisitStep::Visit(subject));
                    for clause in clauses {
                        if let WhenPattern::Literal(lit) = &clause.pattern {
                            seq.push(VisitStep::Visit(lit));
                        }
                        seq.push(VisitStep::ClausePre(subject_name.as_ref(), clause));
                        if let Some(guard) = &clause.guard {
                            seq.push(VisitStep::Visit(guard));
                        }
                        seq.push(VisitStep::Visit(&clause.body));
                        seq.push(VisitStep::ClausePost(subject_name.as_ref(), clause));
                    }
                    steps.extend(seq.into_iter().rev());
                }

                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail {
                        steps.push(VisitStep::Visit(t));
                    }
                    steps.extend(elements.iter().rev().map(VisitStep::Visit));
                }

                PseudoExpr::Tuple(elements) => {
                    steps.extend(elements.iter().rev().map(VisitStep::Visit));
                }

                PseudoExpr::Pair(first, second) => {
                    steps.push(VisitStep::Visit(second));
                    steps.push(VisitStep::Visit(first));
                }

                PseudoExpr::Constr { fields, .. } => {
                    steps.extend(fields.iter().rev().map(VisitStep::Visit));
                }

                PseudoExpr::FieldAccess { record, .. } => {
                    steps.push(VisitStep::Visit(record));
                }

                PseudoExpr::IndexAccess { collection, .. } => {
                    steps.push(VisitStep::Visit(collection));
                }

                PseudoExpr::BinOp { left, right, .. } => {
                    steps.push(VisitStep::Visit(right));
                    steps.push(VisitStep::Visit(left));
                }

                PseudoExpr::UnOp { operand, .. } => {
                    steps.push(VisitStep::Visit(operand));
                }

                PseudoExpr::BuiltinCall { args, .. } => {
                    steps.extend(args.iter().rev().map(VisitStep::Visit));
                }

                PseudoExpr::Delay(inner) => {
                    steps.push(VisitStep::Visit(inner));
                }

                PseudoExpr::Force(inner) => {
                    self.visit_force(inner);
                    steps.push(VisitStep::Visit(inner));
                }

                PseudoExpr::Trace { message, value } => {
                    steps.push(VisitStep::Visit(value));
                    steps.push(VisitStep::Visit(message));
                }

                // Leaf nodes — nothing to descend into
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
    }
}

#[cfg(test)]
mod tests;
