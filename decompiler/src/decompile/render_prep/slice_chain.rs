use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use super::purity::is_pure_value;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

// Inline slice-chain aliases at render time.
//
// `simplify` tracks `let X = Y[k..]` chains in `tail_chain_offsets`
// and folds `X[n]` to `Y[n+k]`, but only where it sees the access;
// split scopes, helper hoisting and alias chains across rec_fn
// boundaries leave the `let` standing. This pass walks the AST,
// collects every `let X = Y[k..]` binding, replaces each `X`
// reference with the stored chain, then folds:
//   * `Y[k..][n]` -> `Y[k+n]`
//   * `Y[k..][m..]` -> `Y[(k+m)..]`
//   * `Y[k][n]` -> unchanged (`Y[k]` is a single element)

pub(super) fn inline_slice_chain_aliases(expr: PseudoExpr) -> PseudoExpr {
    // Recognize a `List.tail` slice step in either encoding produced
    // upstream — `Apply(BuiltinCall(List.tail, []), [arg])` (curried) or
    // `BuiltinCall(List.tail, [arg])` (direct) — and return the stripped
    // `arg`. The renderer's `count_tail_chain_any` accepts both, so the
    // slice-chain fold needs the same coverage or `coll[N..][K]` shapes
    // from the direct form leak through unfolded.
    fn strip_list_tail(expr: &PseudoExpr) -> Option<&PseudoExpr> {
        match expr {
            PseudoExpr::Apply { function, args } if args.len() == 1 => {
                if let PseudoExpr::BuiltinCall {
                    name,
                    args: builtin_args,
                } = function.as_ref()
                    && *name == crate::BuiltinId::ListTail
                    && builtin_args.is_empty()
                {
                    return Some(&args[0]);
                }
                None
            }
            PseudoExpr::BuiltinCall { name, args } if args.len() == 1 => {
                if *name == crate::BuiltinId::ListTail {
                    Some(&args[0])
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Return `(base, offset)` if `expr` is a nested `List.tail` chain
    /// over an `is_safe_base` base; `offset` counts the steps.
    fn unwrap_slice(expr: &PseudoExpr) -> Option<(PseudoExpr, usize)> {
        let mut current = expr;
        let mut depth = 0_usize;
        while let Some(inner) = strip_list_tail(current) {
            depth += 1;
            current = inner;
        }
        if depth == 0 {
            return None;
        }
        if !is_safe_base(current) {
            return None;
        }
        Some((current.clone(), depth))
    }

    /// Bases safe to inline into multiple use sites: short
    /// expressions, so duplication stays cheap.
    fn is_safe_base(expr: &PseudoExpr) -> bool {
        let mut current = expr;
        loop {
            match current {
                PseudoExpr::Var { .. } => return true,
                PseudoExpr::FieldAccess { record, .. } => current = record,
                PseudoExpr::IndexAccess { collection, .. } => current = collection,
                _ => return false,
            }
        }
    }

    fn make_list_tail_chain(base: PseudoExpr, depth: usize) -> PseudoExpr {
        let mut result = base;
        for _ in 0..depth {
            result = PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::BuiltinCall {
                    name: "List.tail".to_string().into(),
                    args: vec![].into(),
                }),
                args: vec![result].into(),
            };
        }
        result
    }

    /// `(base, offset)` known for a slice alias.
    #[derive(Clone, Default)]
    struct SliceMap {
        authoritative: HashMap<VarId, (PseudoExpr, usize)>,
        compat: HashMap<String, (PseudoExpr, usize)>,
    }

    impl SliceMap {
        fn get_var(&self, name: &str, id: Option<VarId>) -> Option<&(PseudoExpr, usize)> {
            if let Some(real_id) = id.get() {
                self.authoritative.get(&real_id)
            } else {
                self.compat.get(name)
            }
        }

        fn insert_binding(&mut self, name: String, id: Option<VarId>, value: (PseudoExpr, usize)) {
            if let Some(real_id) = id.get() {
                self.authoritative.insert(real_id, value.clone());
            }
            self.compat.insert(name, value);
        }

        fn shadow_binding(&mut self, name: &str, id: Option<VarId>) {
            if let Some(real_id) = id.get() {
                self.authoritative.remove(&real_id);
            }
            self.compat.remove(name);
        }

        fn shadow_binder(&mut self, binder: &Binder) {
            self.shadow_binding(binder.as_str(), Some(binder.id));
        }

        fn shadow_pattern(&mut self, pattern: &WhenPattern) {
            match pattern {
                WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                    for binder in fields {
                        self.shadow_binder(binder);
                    }
                }
                WhenPattern::List { elements, tail } => {
                    for binder in elements {
                        self.shadow_binder(binder);
                    }
                    if let Some(tail) = tail {
                        self.shadow_binder(tail);
                    }
                }
                WhenPattern::Pair(left, right) => {
                    self.shadow_binder(left);
                    self.shadow_binder(right);
                }
                WhenPattern::Var(binder) => self.shadow_binder(binder),
                WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
            }
        }
    }

    fn rebuild_index_access(collection: PseudoExpr, index: usize) -> PseudoExpr {
        // Fold `List({elements, tail: None})[k]` to `elements[k]`
        // when `k < elements.len()` AND all elements `0..k` are
        // pure values, so discarding them has no observable
        // effect.
        //
        // Slice chains over the literal count too:
        // `List.tail(List.tail([a,b,c,d]))[k]` adds the slice
        // depth to `k`.

        // Peel List.tail wrappers for a literal-list base AND the
        // cumulative depth. Like `unwrap_slice`, but the base it
        // accepts is `List { tail: None }`, not `is_safe_base`.
        let mut current = &collection;
        let mut depth = 0_usize;
        while let Some(inner) = strip_list_tail(current) {
            depth += 1;
            current = inner;
        }
        if let PseudoExpr::List {
            elements,
            tail: None,
        } = current
        {
            let offset = index + depth;
            if offset < elements.len() && elements[..offset].iter().all(is_pure_value) {
                return elements[offset].clone();
            }
        }
        // Fall back to the slice-chain fold X[k..][n] → X[k+n] using the base
        // `current` / `depth` already peeled above. This rewrite is IN-PLACE
        // — `current` appears exactly ONCE in the output, so the base is never
        // duplicated. `unwrap_slice`'s `is_safe_base` purity/size gate exists
        // to protect the base-DUPLICATING alias inliner
        // (`make_list_tail_chain`) and would be over-conservative here. That
        // lets a `When`/`expect`-rooted base fold too, e.g.
        // `(when … { … ; _ -> fail }).fields[1..][1]` → `… .fields[2]`: both
        // sides lower to `head_list(tail_list^(k+n)(X))` for ANY list-typed
        // `X`, and `X` itself is untouched, so the `_ -> fail` inside it
        // survives verbatim.
        if depth > 0 {
            return PseudoExpr::IndexAccess {
                collection: PBox::new(current.clone()),
                index: index + depth,
            };
        }
        PseudoExpr::IndexAccess {
            collection: PBox::new(collection),
            index,
        }
    }

    // `super::purity::is_pure_value` refuses to treat the
    // `Var{name:"expect!", id:None}` abort sentinel as pure — otherwise
    // `[expect!, b][1]` could fold to `b` and silently drop the abort.

    // Two arms evaluate children out of the left-to-right order a generic
    // `children()` walker would use — `Apply`'s args before its function,
    // and a `When` clause's body before its guard — and that exact order
    // is preserved (push children in the REVERSE of the desired pop order)
    // rather than "normalized," per the no-reordering rule: this pass
    // allocates no fresh ids and mutates no state shared between those
    // particular children, but the rule is to preserve order literally,
    // not to re-derive from scratch that a given reordering is safe.
    fn substitute(expr: PseudoExpr, slices: &SliceMap) -> PseudoExpr {
        use std::rc::Rc;

        /// A finished child: either a plain expression, or (only ever
        /// produced/consumed within one `When`'s processing) a rebuilt
        /// clause — `WhenClause` isn't a `PseudoExpr`, so it needs its own
        /// slot on the results stack rather than forcing everything through
        /// `PseudoExpr`.
        enum Rebuilt {
            Expr(PseudoExpr),
            Clause(WhenClause),
        }

        enum Task {
            Enter(PseudoExpr, Rc<SliceMap>),
            Post(Post),
        }

        enum Post {
            IndexAccess {
                index: usize,
            },
            Apply {
                argc: usize,
            },
            LetBody {
                name: String,
                id: Option<VarId>,
                body: PseudoExpr,
                parent: Rc<SliceMap>,
            },
            LetPost {
                name: String,
                id: Option<VarId>,
                value: PseudoExpr,
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
                clause_count: usize,
            },
            WhenClause {
                pattern: WhenPattern,
                has_guard: bool,
            },
            If,
            FieldAccess {
                selector: FieldSelector,
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
                shape: ConstructorShape,
            },
            Delay,
            Force,
            Trace,
        }

        fn pop_expr(done: &mut Vec<Rebuilt>) -> PseudoExpr {
            match done.pop().expect("child result") {
                Rebuilt::Expr(e) => e,
                Rebuilt::Clause(_) => unreachable!("clause popped as expr"),
            }
        }

        fn take_expr(done: &mut Vec<Rebuilt>, n: usize) -> Vec<PseudoExpr> {
            let at = done.len() - n;
            done.split_off(at)
                .into_iter()
                .map(|r| match r {
                    Rebuilt::Expr(e) => e,
                    Rebuilt::Clause(_) => unreachable!("clause taken as expr"),
                })
                .collect()
        }

        let mut stack: Vec<Task> = vec![Task::Enter(expr, Rc::new(slices.clone()))];
        let mut done: Vec<Rebuilt> = Vec::new();

        while let Some(task) = stack.pop() {
            match task {
                Task::Enter(expr, scope) => match expr {
                    PseudoExpr::Var { name, id } => {
                        if let Some((base, depth)) = scope.get_var(&name, id) {
                            done.push(Rebuilt::Expr(make_list_tail_chain(base.clone(), *depth)));
                        } else {
                            done.push(Rebuilt::Expr(PseudoExpr::Var { name, id }));
                        }
                    }
                    PseudoExpr::IndexAccess { collection, index } => {
                        stack.push(Task::Post(Post::IndexAccess { index }));
                        stack.push(Task::Enter(collection.into_inner(), scope));
                    }
                    PseudoExpr::Apply { function, args } => {
                        // Fold List.tail(X) where X is in slice map. Args
                        // before function — see fn doc.
                        stack.push(Task::Post(Post::Apply { argc: args.len() }));
                        stack.push(Task::Enter(function.into_inner(), scope.clone()));
                        for arg in args.into_iter().rev() {
                            stack.push(Task::Enter(arg, scope.clone()));
                        }
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        stack.push(Task::Post(Post::LetBody {
                            name,
                            id,
                            body: body.into_inner(),
                            parent: scope.clone(),
                        }));
                        stack.push(Task::Enter(value.into_inner(), scope));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        let mut child = (*scope).clone();
                        for param in &params {
                            child.shadow_binder(param);
                        }
                        stack.push(Task::Post(Post::Lambda { params }));
                        stack.push(Task::Enter(body.into_inner(), Rc::new(child)));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let mut child = (*scope).clone();
                        child.shadow_binder(&name);
                        for param in &params {
                            child.shadow_binder(param);
                        }
                        stack.push(Task::Post(Post::RecFn { name, params }));
                        stack.push(Task::Enter(body.into_inner(), Rc::new(child)));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        stack.push(Task::Post(Post::When {
                            subject_name: subject_name.clone(),
                            clause_count: clauses.len(),
                        }));
                        // Reversed so the first clause ends up nearest the
                        // top (processed right after `subject`).
                        for clause in clauses.into_iter().rev() {
                            let mut child = (*scope).clone();
                            if let Some(sn) = &subject_name {
                                child.shadow_binder(sn);
                            }
                            child.shadow_pattern(&clause.pattern);
                            let child = Rc::new(child);
                            let has_guard = clause.guard.is_some();
                            stack.push(Task::Post(Post::WhenClause {
                                pattern: clause.pattern,
                                has_guard,
                            }));
                            // Body before guard.
                            if let Some(guard) = clause.guard {
                                stack.push(Task::Enter(guard, child.clone()));
                            }
                            stack.push(Task::Enter(clause.body, child));
                        }
                        stack.push(Task::Enter(subject.into_inner(), scope));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        stack.push(Task::Post(Post::If));
                        stack.push(Task::Enter(else_branch.into_inner(), scope.clone()));
                        stack.push(Task::Enter(then_branch.into_inner(), scope.clone()));
                        stack.push(Task::Enter(condition.into_inner(), scope));
                    }
                    PseudoExpr::FieldAccess { record, selector } => {
                        stack.push(Task::Post(Post::FieldAccess { selector }));
                        stack.push(Task::Enter(record.into_inner(), scope));
                    }
                    PseudoExpr::BinOp { op, left, right } => {
                        stack.push(Task::Post(Post::BinOp { op }));
                        stack.push(Task::Enter(right.into_inner(), scope.clone()));
                        stack.push(Task::Enter(left.into_inner(), scope));
                    }
                    PseudoExpr::UnOp { op, operand } => {
                        stack.push(Task::Post(Post::UnOp { op }));
                        stack.push(Task::Enter(operand.into_inner(), scope));
                    }
                    PseudoExpr::BuiltinCall { name, args } => {
                        stack.push(Task::Post(Post::BuiltinCall {
                            name,
                            argc: args.len(),
                        }));
                        for a in args.into_iter().rev() {
                            stack.push(Task::Enter(a, scope.clone()));
                        }
                    }
                    PseudoExpr::List { elements, tail } => {
                        stack.push(Task::Post(Post::List {
                            count: elements.len(),
                            has_tail: tail.is_some(),
                        }));
                        if let Some(t) = tail {
                            stack.push(Task::Enter(t.into_inner(), scope.clone()));
                        }
                        for e in elements.into_iter().rev() {
                            stack.push(Task::Enter(e, scope.clone()));
                        }
                    }
                    PseudoExpr::Tuple(items) => {
                        stack.push(Task::Post(Post::Tuple { count: items.len() }));
                        for i in items.into_iter().rev() {
                            stack.push(Task::Enter(i, scope.clone()));
                        }
                    }
                    PseudoExpr::Pair(a, b) => {
                        stack.push(Task::Post(Post::Pair));
                        stack.push(Task::Enter(b.into_inner(), scope.clone()));
                        stack.push(Task::Enter(a.into_inner(), scope));
                    }
                    PseudoExpr::Constr {
                        type_hint,
                        tag,
                        fields,
                        shape,
                    } => {
                        stack.push(Task::Post(Post::Constr {
                            type_hint,
                            tag,
                            count: fields.len(),
                            shape,
                        }));
                        for f in fields.into_iter().rev() {
                            stack.push(Task::Enter(f, scope.clone()));
                        }
                    }
                    PseudoExpr::Delay(inner) => {
                        stack.push(Task::Post(Post::Delay));
                        stack.push(Task::Enter(inner.into_inner(), scope));
                    }
                    PseudoExpr::Force(inner) => {
                        stack.push(Task::Post(Post::Force));
                        stack.push(Task::Enter(inner.into_inner(), scope));
                    }
                    PseudoExpr::Trace { message, value } => {
                        stack.push(Task::Post(Post::Trace));
                        stack.push(Task::Enter(value.into_inner(), scope.clone()));
                        stack.push(Task::Enter(message.into_inner(), scope));
                    }
                    other => done.push(Rebuilt::Expr(other)),
                },
                Task::Post(op) => match op {
                    Post::IndexAccess { index } => {
                        let collection = pop_expr(&mut done);
                        done.push(Rebuilt::Expr(rebuild_index_access(collection, index)));
                    }
                    Post::Apply { argc } => {
                        let function = pop_expr(&mut done);
                        let args = take_expr(&mut done, argc);
                        done.push(Rebuilt::Expr(PseudoExpr::Apply {
                            function: PBox::new(function),
                            args: args.into(),
                        }));
                    }
                    Post::LetBody {
                        name,
                        id,
                        body,
                        parent,
                    } => {
                        let value = pop_expr(&mut done);
                        // The let survives even when its value enters the
                        // slice map, so an alias with non-slice uses still
                        // renders; dead-let elim drops the fully
                        // substituted ones.
                        let mut child = (*parent).clone();
                        child.shadow_binding(&name, id);
                        if let Some((base, depth)) = unwrap_slice(&value) {
                            child.insert_binding(name.clone(), id, (base, depth));
                        }
                        stack.push(Task::Post(Post::LetPost { name, id, value }));
                        stack.push(Task::Enter(body, Rc::new(child)));
                    }
                    Post::LetPost { name, id, value } => {
                        let body = pop_expr(&mut done);
                        done.push(Rebuilt::Expr(PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }));
                    }
                    Post::Lambda { params } => {
                        let body = pop_expr(&mut done);
                        done.push(Rebuilt::Expr(PseudoExpr::Lambda {
                            params,
                            body: PBox::new(body),
                        }));
                    }
                    Post::RecFn { name, params } => {
                        let body = pop_expr(&mut done);
                        done.push(Rebuilt::Expr(PseudoExpr::RecFn {
                            name,
                            params,
                            body: PBox::new(body),
                        }));
                    }
                    Post::WhenClause { pattern, has_guard } => {
                        let guard = if has_guard {
                            Some(pop_expr(&mut done))
                        } else {
                            None
                        };
                        let body = pop_expr(&mut done);
                        done.push(Rebuilt::Clause(WhenClause {
                            pattern,
                            guard,
                            body,
                        }));
                    }
                    Post::When {
                        subject_name,
                        clause_count,
                    } => {
                        let at = done.len() - clause_count;
                        let clauses: Vec<WhenClause> = done
                            .split_off(at)
                            .into_iter()
                            .map(|r| match r {
                                Rebuilt::Clause(c) => c,
                                Rebuilt::Expr(_) => unreachable!("expr taken as clause"),
                            })
                            .collect();
                        let subject = pop_expr(&mut done);
                        done.push(Rebuilt::Expr(PseudoExpr::When {
                            subject: PBox::new(subject),
                            subject_name,
                            clauses,
                        }));
                    }
                    Post::If => {
                        let mut parts = take_expr(&mut done, 3).into_iter();
                        let condition = parts.next().expect("if condition");
                        let then_branch = parts.next().expect("if then");
                        let else_branch = parts.next().expect("if else");
                        done.push(Rebuilt::Expr(PseudoExpr::If {
                            condition: PBox::new(condition),
                            then_branch: PBox::new(then_branch),
                            else_branch: PBox::new(else_branch),
                        }));
                    }
                    Post::FieldAccess { selector } => {
                        let record = pop_expr(&mut done);
                        done.push(Rebuilt::Expr(PseudoExpr::FieldAccess {
                            record: PBox::new(record),
                            selector,
                        }));
                    }
                    Post::BinOp { op } => {
                        let right = pop_expr(&mut done);
                        let left = pop_expr(&mut done);
                        done.push(Rebuilt::Expr(PseudoExpr::BinOp {
                            op,
                            left: PBox::new(left),
                            right: PBox::new(right),
                        }));
                    }
                    Post::UnOp { op } => {
                        let operand = pop_expr(&mut done);
                        done.push(Rebuilt::Expr(PseudoExpr::UnOp {
                            op,
                            operand: PBox::new(operand),
                        }));
                    }
                    Post::BuiltinCall { name, argc } => {
                        let args = take_expr(&mut done, argc);
                        done.push(Rebuilt::Expr(PseudoExpr::BuiltinCall {
                            name,
                            args: args.into(),
                        }));
                    }
                    Post::List { count, has_tail } => {
                        let tail = if has_tail {
                            Some(pop_expr(&mut done))
                        } else {
                            None
                        };
                        let elements = take_expr(&mut done, count);
                        done.push(Rebuilt::Expr(PseudoExpr::List {
                            elements: elements.into(),
                            tail: tail.map(PBox::new),
                        }));
                    }
                    Post::Tuple { count } => {
                        let items = take_expr(&mut done, count);
                        done.push(Rebuilt::Expr(PseudoExpr::Tuple(items.into())));
                    }
                    Post::Pair => {
                        let b = pop_expr(&mut done);
                        let a = pop_expr(&mut done);
                        done.push(Rebuilt::Expr(PseudoExpr::Pair(PBox::new(a), PBox::new(b))));
                    }
                    Post::Constr {
                        type_hint,
                        tag,
                        count,
                        shape,
                    } => {
                        let fields = take_expr(&mut done, count);
                        done.push(Rebuilt::Expr(PseudoExpr::Constr {
                            type_hint,
                            tag,
                            fields: fields.into(),
                            shape,
                        }));
                    }
                    Post::Delay => {
                        let inner = pop_expr(&mut done);
                        done.push(Rebuilt::Expr(PseudoExpr::Delay(PBox::new(inner))));
                    }
                    Post::Force => {
                        let inner = pop_expr(&mut done);
                        done.push(Rebuilt::Expr(PseudoExpr::Force(PBox::new(inner))));
                    }
                    Post::Trace => {
                        let value = pop_expr(&mut done);
                        let message = pop_expr(&mut done);
                        done.push(Rebuilt::Expr(PseudoExpr::Trace {
                            message: PBox::new(message),
                            value: PBox::new(value),
                        }));
                    }
                },
            }
        }

        debug_assert_eq!(done.len(), 1, "substitute machine must leave one result");
        pop_expr(&mut done)
    }

    substitute(expr, &SliceMap::default())
}
