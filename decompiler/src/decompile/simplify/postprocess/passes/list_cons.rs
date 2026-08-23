use crate::builtins::BuiltinId;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::nameless::convert::{nameless_to_pseudo, pseudo_to_nameless};
use crate::pseudo::nameless::fold::NamelessFolder;
use crate::pseudo::nameless::{NamelessExpr, NamelessPattern};
use crate::pseudo::var_id::VarId;

/// Normalize builtin list constructors into first-class list literals:
/// `List.cons(x, [])` becomes `[x]`, nested cons chains flatten, and
/// empty spread tails like `[x, ..[]]` are dropped.
///
/// `contains_list_cons_marker` skips the nameless roundtrip when there
/// is nothing to rewrite, since the roundtrip is lossy for duplicate
/// VarIds.
pub(crate) fn normalize_list_cons_literals(expr: PseudoExpr) -> PseudoExpr {
    if !contains_list_cons_marker(&expr) {
        return expr;
    }
    let (nameless, table) = pseudo_to_nameless(&expr);
    let normalized = normalize_list_cons_literals_nameless(nameless);
    nameless_to_pseudo(&normalized, &table)
}

/// True iff `expr` contains a list-cons builtin anywhere:
/// directly, curried, or as the value of a `Let` an alias may
/// use. Bare `Var`s never match on name alone, so the scan
/// cannot over-match across scopes.
///
/// A false result means the tree holds no list-cons builtin at
/// all, and the pass has nothing to rewrite.
fn contains_list_cons_marker(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::BuiltinCall { name, args } => {
                if is_list_cons_builtin(*name) {
                    return true;
                }
                pending.extend(args.iter().rev());
            }
            PseudoExpr::Lambda { body, .. } => pending.push(body),
            PseudoExpr::RecFn { body, .. } => pending.push(body),
            PseudoExpr::Apply { function, args } => {
                pending.extend(args.iter().rev());
                pending.push(function);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
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
                    if let Some(g) = &c.guard {
                        pending.push(g);
                    }
                }
                pending.push(subject);
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail.as_ref() {
                    pending.push(t);
                }
                pending.extend(elements.iter().rev());
            }
            PseudoExpr::Tuple(items) => pending.extend(items.iter().rev()),
            PseudoExpr::Pair(a, b) => {
                pending.push(b);
                pending.push(a);
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter().rev()),
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            PseudoExpr::Var { .. }
            | PseudoExpr::Int(_)
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
    false
}

fn is_list_cons_builtin(name: BuiltinId) -> bool {
    *name == crate::BuiltinId::ListPrepend
        || *name == crate::BuiltinId::ListCons
        || name == "MkCons"
        || name == "cons_list"
        || name == "mk_cons"
}

/// Nameless implementation of [`normalize_list_cons_literals`].
/// Keys the alias stack by `VarId` rather than name — id is the
/// authoritative identity in nameless form.
pub(crate) fn normalize_list_cons_literals_nameless(expr: NamelessExpr) -> NamelessExpr {
    struct ConsAliasScope {
        binder: VarId,
        builtin: Option<BuiltinId>,
    }

    struct NormalizeListCons {
        cons_alias_stack: Vec<ConsAliasScope>,
    }

    impl NormalizeListCons {
        fn lookup_cons_alias(&self, id: VarId) -> Option<BuiltinId> {
            for scope in self.cons_alias_stack.iter().rev() {
                if scope.binder == id {
                    return scope.builtin;
                }
            }
            None
        }

        fn push_scope(&mut self, binder: VarId, builtin: Option<BuiltinId>) {
            self.cons_alias_stack
                .push(ConsAliasScope { binder, builtin });
        }

        fn push_blocker(&mut self, binder: VarId) {
            self.push_scope(binder, None);
        }

        fn pop_scopes(&mut self, count: usize) {
            for _ in 0..count {
                self.cons_alias_stack.pop();
            }
        }

        fn push_pattern_blockers(&mut self, pattern: &NamelessPattern) -> usize {
            let before = self.cons_alias_stack.len();
            match pattern {
                NamelessPattern::Var(id) => self.push_blocker(*id),
                NamelessPattern::Constructor { fields, .. } | NamelessPattern::Tuple(fields) => {
                    for id in fields {
                        self.push_blocker(*id);
                    }
                }
                NamelessPattern::List { elements, tail } => {
                    for id in elements {
                        self.push_blocker(*id);
                    }
                    if let Some(t) = tail {
                        self.push_blocker(*t);
                    }
                }
                NamelessPattern::Pair(a, b) => {
                    self.push_blocker(*a);
                    self.push_blocker(*b);
                }
                NamelessPattern::Wildcard | NamelessPattern::Literal(_) => {}
            }
            self.cons_alias_stack.len() - before
        }

        fn build_list_from_cons_args(&self, mut args: Vec<NamelessExpr>) -> Option<NamelessExpr> {
            if args.len() != 2 {
                return None;
            }
            let tail_expr = args.pop().expect("list cons tail argument should exist");
            let head = args.pop().expect("list cons head argument should exist");
            if let NamelessExpr::List { mut elements, tail } = tail_expr {
                elements.insert(0, head);
                return Some(NamelessExpr::List { elements, tail });
            }
            Some(NamelessExpr::List {
                elements: vec![head],
                tail: Some(Box::new(tail_expr)),
            })
        }
    }

    fn extract_nullary_list_cons_builtin_nameless(expr: &NamelessExpr) -> Option<BuiltinId> {
        match expr {
            NamelessExpr::BuiltinCall { name, args }
                if args.is_empty() && is_list_cons_builtin(*name) =>
            {
                Some(*name)
            }
            NamelessExpr::Apply { function, args } if args.is_empty() => match function.as_ref() {
                NamelessExpr::BuiltinCall {
                    name,
                    args: builtin_args,
                } if builtin_args.is_empty() && is_list_cons_builtin(*name) => Some(*name),
                _ => None,
            },
            _ => None,
        }
    }

    use crate::pseudo::nameless::fold::count_var_uses as count_var_uses_nameless;

    impl NamelessFolder for NormalizeListCons {
        fn enter_lambda(&mut self, params: &[VarId]) {
            for p in params {
                self.push_blocker(*p);
            }
        }
        fn exit_lambda(&mut self, params: &[VarId]) {
            self.pop_scopes(params.len());
        }
        fn enter_recfn(&mut self, name: VarId, params: &[VarId]) {
            self.push_blocker(name);
            for p in params {
                self.push_blocker(*p);
            }
        }
        fn exit_recfn(&mut self, _name: VarId, params: &[VarId]) {
            self.pop_scopes(1 + params.len());
        }
        fn enter_let(&mut self, binder: VarId, value: &NamelessExpr) {
            self.push_scope(binder, extract_nullary_list_cons_builtin_nameless(value));
        }
        fn exit_let(&mut self, _binder: VarId) {
            self.cons_alias_stack.pop();
        }
        fn enter_when(&mut self, _: &NamelessExpr, subject_name: Option<VarId>) {
            if let Some(id) = subject_name {
                self.push_blocker(id);
            }
        }
        fn exit_when(&mut self, subject_name: Option<VarId>) {
            if subject_name.is_some() {
                self.pop_scopes(1);
            }
        }
        fn enter_clause(&mut self, pattern: &NamelessPattern) {
            self.push_pattern_blockers(pattern);
        }
        fn exit_clause(&mut self, pattern: &NamelessPattern) {
            // Recomputes what `push_pattern_blockers` pushed; its
            // return value does not reach this hook.
            let count = match pattern {
                NamelessPattern::Var(_) => 1,
                NamelessPattern::Constructor { fields, .. } | NamelessPattern::Tuple(fields) => {
                    fields.len()
                }
                NamelessPattern::List { elements, tail } => elements.len() + tail.iter().count(),
                NamelessPattern::Pair(_, _) => 2,
                NamelessPattern::Wildcard | NamelessPattern::Literal(_) => 0,
            };
            self.pop_scopes(count);
        }

        fn post_builtin_call(&mut self, name: BuiltinId, args: Vec<NamelessExpr>) -> NamelessExpr {
            if *name == crate::BuiltinId::ListCons && args.len() == 2 {
                return self
                    .build_list_from_cons_args(args)
                    .expect("two-argument List.cons conversion should produce a list");
            }
            NamelessExpr::BuiltinCall { name, args }
        }

        fn post_apply(&mut self, function: NamelessExpr, args: Vec<NamelessExpr>) -> NamelessExpr {
            if args.len() == 2 {
                let cons_builtin = match &function {
                    NamelessExpr::BuiltinCall { name, args: bargs } if bargs.is_empty() => {
                        is_list_cons_builtin(*name).then_some(*name)
                    }
                    NamelessExpr::Apply {
                        function: inner_fn,
                        args: inner_args,
                    } if inner_args.is_empty() => match inner_fn.as_ref() {
                        NamelessExpr::BuiltinCall { name, args: bargs }
                            if bargs.is_empty() && is_list_cons_builtin(*name) =>
                        {
                            Some(*name)
                        }
                        _ => None,
                    },
                    NamelessExpr::Var(id) => self.lookup_cons_alias(*id),
                    _ => None,
                };
                if cons_builtin.is_some() {
                    if let Some(list) = self.build_list_from_cons_args(args) {
                        return list;
                    }
                    unreachable!("two-argument list cons conversion should produce a list");
                }
            }
            NamelessExpr::Apply {
                function: Box::new(function),
                args,
            }
        }

        fn post_let(
            &mut self,
            binder: VarId,
            value: NamelessExpr,
            body: NamelessExpr,
        ) -> NamelessExpr {
            if extract_nullary_list_cons_builtin_nameless(&value).is_some()
                && count_var_uses_nameless(&body, binder) == 0
            {
                return body;
            }
            NamelessExpr::Let {
                binder,
                value: Box::new(value),
                body: Box::new(body),
            }
        }

        fn post_list(
            &mut self,
            elements: Vec<NamelessExpr>,
            tail: Option<NamelessExpr>,
        ) -> NamelessExpr {
            let tail = match tail {
                Some(NamelessExpr::List {
                    elements: ref inner,
                    tail: None,
                }) if inner.is_empty() => None,
                other => other,
            };
            NamelessExpr::List {
                elements,
                tail: tail.map(Box::new),
            }
        }
    }

    NormalizeListCons {
        cons_alias_stack: Vec::new(),
    }
    .fold(expr)
}

#[cfg(test)]
mod tests;
