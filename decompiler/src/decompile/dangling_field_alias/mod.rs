use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

use super::ScriptVersion;
use super::simplify::postprocess::{ContextField, ContextType, context_field_at};

mod payload_repair;

use self::payload_repair::repair_dangling_constr_payload_binders;

#[allow(non_upper_case_globals)]
const ScriptContext_MAX_FIELDS: usize = 4;

// Resolve dangling `field_N` / Cardano-named references.
//
// `simplify::let_binding::aliases::introduce_field_index_aliases` synthesises
// `let field_N = parent[N] in body` bindings for repeated `parent[N]`
// accesses. Later passes (helper hoisting, single-use inlining, readability
// rewrites) can drop the binding without rewriting use sites that survived
// in adjacent scopes, leaving `field_N` — or its Cardano-named alias, such
// as `inputs`, `outputs` — free in the final AST.
//
// This pass tracks lexical scope and replaces such free references with a
// chained access from the closest in-scope Cardano context anchor
// (`tx_info`, `script_context`, or `script_info`), trading a more verbose
// access path for a well-scoped, semantics-preserving expression.
//
// Must run AFTER the last `resolve_cardano_field_names`, so it sees the
// fully-renamed Cardano-named accesses, and AFTER every helper-hoisting and
// single-use-inlining pass that might drop an alias binding.

pub(crate) fn inline_dangling_field_aliases(
    expr: PseudoExpr,
    version: ScriptVersion,
    kind_annotations: &std::collections::HashMap<
        crate::pseudo::var_id::VarId,
        crate::pseudo::nameless::VarKind,
    >,
    use_varkind_recovery: bool,
) -> PseudoExpr {
    // Pre-pass: scan for `field_N` aliases used as a When subject
    // (Constr-match position). Those are almost certainly
    // ScriptContext-typed — a list/int can't be matched as a Constr.
    let mut script_context_field_aliases: HashSet<(String, usize)> = HashSet::new();
    collect_when_subject_field_aliases(&expr, &mut script_context_field_aliases);

    let mut resolver = DanglingResolver {
        version,
        scope: Vec::new(),
        scope_ids: Vec::new(),
        script_context_field_aliases,
    };
    let expr = resolver.go(expr);
    repair_dangling_constr_payload_binders(expr, kind_annotations, use_varkind_recovery)
}

fn collect_when_subject_field_aliases(expr: &PseudoExpr, out: &mut HashSet<(String, usize)>) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::When {
                subject,
                subject_name: _,
                clauses,
            } => {
                // Subject as a `field_N` Var — record its index.
                if let PseudoExpr::Var { name, .. } = subject.as_ref()
                    && let Some(rest) = name.strip_prefix("field_")
                    && let Ok(idx) = rest.parse::<usize>()
                {
                    out.insert((name.clone(), idx));
                }
                for clause in clauses.iter().rev() {
                    pending.push(&clause.body);
                    if let Some(g) = &clause.guard {
                        pending.push(g);
                    }
                }
                pending.push(subject);
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
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
            PseudoExpr::Apply { function, args } => {
                for arg in args.iter().rev() {
                    pending.push(arg);
                }
                pending.push(function);
            }
            PseudoExpr::FieldAccess { record, .. } => {
                pending.push(record);
            }
            PseudoExpr::IndexAccess { collection, .. } => {
                pending.push(collection);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => {
                pending.push(operand);
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args.iter().rev() {
                    pending.push(arg);
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
            PseudoExpr::Tuple(items) => {
                for i in items.iter().rev() {
                    pending.push(i);
                }
            }
            PseudoExpr::Pair(a, b) => {
                pending.push(b);
                pending.push(a);
            }
            PseudoExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    pending.push(f);
                }
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                pending.push(inner);
            }
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            _ => {}
        }
    }
}

struct DanglingResolver {
    version: ScriptVersion,
    scope: Vec<HashSet<String>>,
    /// Parallel map of scope binders' VarIds, so a synthesized
    /// anchor `Var` (script_context / tx_info) carries the
    /// binder's own id, compat placeholders included, instead of
    /// a freshly minted one. Populated alongside `scope` by
    /// `push_scope_with_ids`.
    scope_ids: Vec<std::collections::HashMap<String, crate::pseudo::var_id::VarId>>,
    /// (alias_name, idx) pairs for `field_N` synthetic aliases used
    /// as a `when` subject (Constr-match position) anywhere in the
    /// AST. Their parent is almost certainly ScriptContext — every
    /// ScriptContext field is Constr-typed, whereas TxInfo fields are
    /// mostly list/map/int and are never matched as Constr. Filled by
    /// a pre-pass before resolution.
    script_context_field_aliases: HashSet<(String, usize)>,
}

#[derive(Clone, Copy)]
enum AnchorKind {
    ScriptContext,
    TxInfo,
}

impl DanglingResolver {
    fn is_bound(&self, name: &str) -> bool {
        self.scope.iter().any(|s| s.contains(name))
    }

    /// Push a scope, recording each name's VarId for the
    /// anchor lookup during dangling-ref resolution.
    fn push_scope_with_ids<I: IntoIterator<Item = (String, crate::pseudo::var_id::VarId)>>(
        &mut self,
        binders: I,
    ) {
        let mut names = HashSet::new();
        let mut ids = std::collections::HashMap::new();
        for (name, id) in binders {
            names.insert(name.clone());
            ids.insert(name, id);
        }
        self.scope.push(names);
        self.scope_ids.push(ids);
    }

    fn pop_scope(&mut self) {
        self.scope.pop();
        self.scope_ids.pop();
    }

    /// Look up the VarId for a name in the scope chain (innermost wins).
    /// Returns `None` only if the name is not bound.
    fn lookup_scope_id(&self, name: &str) -> Option<crate::pseudo::var_id::VarId> {
        self.scope_ids
            .iter()
            .rev()
            .find_map(|frame| frame.get(name).copied())
    }

    fn find_anchor(&self) -> Option<(&'static str, AnchorKind)> {
        for level in self.scope.iter().rev() {
            if level.contains("tx_info") {
                return Some(("tx_info", AnchorKind::TxInfo));
            }
        }
        for level in self.scope.iter().rev() {
            if level.contains("script_context") {
                return Some(("script_context", AnchorKind::ScriptContext));
            }
        }
        None
    }

    fn field_index_for(&self, parent: ContextType, name: &str) -> Option<(usize, ContextField)> {
        // Named Cardano-schema fields (`inputs`, `outputs`, …) — safe to
        // resolve against the requested parent.
        if let Some(field) = ContextField::from_display_name(name) {
            for i in 0..32 {
                match context_field_at(parent, i, self.version) {
                    Some(f) if f == field => return Some((i, f)),
                    Some(_) => continue,
                    None => break,
                }
            }
        }
        // Synthetic `field_N` aliases — DO NOT resolve via this path.
        // `simplify::let_binding::aliases::introduce_field_index_aliases`
        // mints `field_N` for every `.fields` parent (script_context,
        // redeemer, script_info, inner Constr-payloads, tx_info, …), not
        // just tx_info, so mapping a free `field_N` to `tx_info.fields[N]`
        // unconditionally produces wrong chains like
        // `script_context.tx_info.reference_inputs` for a free `field_1`
        // that originated from `script_context.fields[1]` (= redeemer).
        // Leaving the reference dangling is uglier but semantically
        // correct, and downstream invariants (and the dangling-resolver
        // tests) flag the remaining free vars.
        None
    }

    fn try_resolve_var(&self, name: &str) -> Option<PseudoExpr> {
        if self.is_bound(name) {
            return None;
        }

        // Named script_context-level fields (`tx_info`, `redeemer`,
        // `script_info`) resolve relative to the closest script_context
        // anchor. Synthetic `field_N` aliases are not legacy names, so
        // they never take this branch.
        if let Some(field) = ContextField::from_display_name(name) {
            for i in 0..ScriptContext_MAX_FIELDS {
                match context_field_at(ContextType::ScriptContext, i, self.version) {
                    Some(f) if f == field => {
                        if self.is_bound("script_context") {
                            let id = self
                                .lookup_scope_id("script_context")
                                .expect("script_context anchor should have a recorded VarId");
                            let anchor = PseudoExpr::Var {
                                name: "script_context".to_string(),
                                id: Some(id),
                            };
                            return Some(PseudoExpr::field_access(anchor, field.display_name()));
                        }
                        return None;
                    }
                    Some(_) => continue,
                    None => break,
                }
            }
        }

        // Fallback: tx_info-level field. Both named fields (`inputs`,
        // `outputs`, …) and synthetic `field_N` aliases land here, EXCEPT
        // aliases the When-subject pre-pass marked ScriptContext-typed.
        let synthetic_field_idx = name
            .strip_prefix("field_")
            .and_then(|rest| rest.parse::<usize>().ok());
        let prefer_script_context = synthetic_field_idx
            .map(|idx| {
                self.script_context_field_aliases
                    .contains(&(name.to_string(), idx))
            })
            .unwrap_or(false);
        let (anchor_name, kind) = self.find_anchor()?;
        let (parent_type, prefix_with_tx_info) = if prefer_script_context {
            (ContextType::ScriptContext, false)
        } else {
            match kind {
                AnchorKind::ScriptContext => (ContextType::TxInfo, true),
                AnchorKind::TxInfo => (ContextType::TxInfo, false),
            }
        };
        let (_, field) = if let Some(idx) = synthetic_field_idx {
            let f = context_field_at(parent_type, idx, self.version)?;
            (idx, f)
        } else {
            self.field_index_for(parent_type, name)?
        };

        let anchor_id = self
            .lookup_scope_id(anchor_name)
            .expect("dangling field anchor should have a recorded VarId");
        let anchor = PseudoExpr::Var {
            name: anchor_name.to_string(),
            id: Some(anchor_id),
        };
        let parent_expr = if prefix_with_tx_info {
            PseudoExpr::field_access(anchor, "tx_info")
        } else {
            anchor
        };
        Some(PseudoExpr::field_access(parent_expr, field.display_name()))
    }

    fn go(&mut self, expr: PseudoExpr) -> PseudoExpr {
        /// A finished child: either a plain expression, or (only ever
        /// produced/consumed within one `When`'s processing) a rebuilt
        /// clause — `WhenClause` isn't a `PseudoExpr`, so it needs its own
        /// slot on the results stack.
        enum Rebuilt {
            Expr(PseudoExpr),
            Clause(WhenClause),
        }

        enum Task {
            Enter(PseudoExpr),
            Post(Post),
        }

        enum Post {
            Lambda {
                params: Vec<Binder>,
            },
            RecFn {
                name: Binder,
                params: Vec<Binder>,
            },
            LetBody {
                name: String,
                id: Option<VarId>,
                body: PseudoExpr,
            },
            LetPost {
                name: String,
                id: Option<VarId>,
                value: PseudoExpr,
            },
            When {
                subject_name: Option<Binder>,
                clause_count: usize,
            },
            WhenClauseStart {
                bound: Vec<(String, VarId)>,
            },
            WhenClauseEnd {
                pattern: WhenPattern,
                has_guard: bool,
            },
            If,
            Apply {
                argc: usize,
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

        let mut stack: Vec<Task> = vec![Task::Enter(expr)];
        let mut done: Vec<Rebuilt> = Vec::new();

        while let Some(task) = stack.pop() {
            match task {
                Task::Enter(expr) => match expr {
                    PseudoExpr::Var { name, id } => {
                        if let Some(replacement) = self.try_resolve_var(&name) {
                            done.push(Rebuilt::Expr(replacement));
                        } else {
                            done.push(Rebuilt::Expr(PseudoExpr::Var { name, id }));
                        }
                    }
                    PseudoExpr::Lambda { params, body } => {
                        self.push_scope_with_ids(
                            params.iter().map(|b| (b.to_string(), b.var_id())),
                        );
                        stack.push(Task::Post(Post::Lambda { params }));
                        stack.push(Task::Enter(body.into_inner()));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let binders: Vec<(String, VarId)> =
                            std::iter::once((name.to_string(), name.var_id()))
                                .chain(params.iter().map(|b| (b.to_string(), b.var_id())))
                                .collect();
                        self.push_scope_with_ids(binders);
                        stack.push(Task::Post(Post::RecFn { name, params }));
                        stack.push(Task::Enter(body.into_inner()));
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
                        }));
                        stack.push(Task::Enter(value.into_inner()));
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
                            let mut bound = pattern_bound_binders(&clause.pattern);
                            if let Some(ref n) = subject_name {
                                bound.push((n.to_string(), n.var_id()));
                            }
                            let has_guard = clause.guard.is_some();
                            stack.push(Task::Post(Post::WhenClauseEnd {
                                pattern: clause.pattern,
                                has_guard,
                            }));
                            if let Some(guard) = clause.guard {
                                stack.push(Task::Enter(guard));
                            }
                            stack.push(Task::Enter(clause.body));
                            stack.push(Task::Post(Post::WhenClauseStart { bound }));
                        }
                        stack.push(Task::Enter(subject.into_inner()));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        stack.push(Task::Post(Post::If));
                        stack.push(Task::Enter(else_branch.into_inner()));
                        stack.push(Task::Enter(then_branch.into_inner()));
                        stack.push(Task::Enter(condition.into_inner()));
                    }
                    PseudoExpr::Apply { function, args } => {
                        stack.push(Task::Post(Post::Apply { argc: args.len() }));
                        for a in args.into_iter().rev() {
                            stack.push(Task::Enter(a));
                        }
                        stack.push(Task::Enter(function.into_inner()));
                    }
                    PseudoExpr::FieldAccess { record, selector } => {
                        stack.push(Task::Post(Post::FieldAccess { selector }));
                        stack.push(Task::Enter(record.into_inner()));
                    }
                    PseudoExpr::IndexAccess { collection, index } => {
                        stack.push(Task::Post(Post::IndexAccess { index }));
                        stack.push(Task::Enter(collection.into_inner()));
                    }
                    PseudoExpr::BinOp { op, left, right } => {
                        stack.push(Task::Post(Post::BinOp { op }));
                        stack.push(Task::Enter(right.into_inner()));
                        stack.push(Task::Enter(left.into_inner()));
                    }
                    PseudoExpr::UnOp { op, operand } => {
                        stack.push(Task::Post(Post::UnOp { op }));
                        stack.push(Task::Enter(operand.into_inner()));
                    }
                    PseudoExpr::BuiltinCall { name, args } => {
                        stack.push(Task::Post(Post::BuiltinCall {
                            name,
                            argc: args.len(),
                        }));
                        for a in args.into_iter().rev() {
                            stack.push(Task::Enter(a));
                        }
                    }
                    PseudoExpr::List { elements, tail } => {
                        stack.push(Task::Post(Post::List {
                            count: elements.len(),
                            has_tail: tail.is_some(),
                        }));
                        if let Some(t) = tail {
                            stack.push(Task::Enter(t.into_inner()));
                        }
                        for e in elements.into_iter().rev() {
                            stack.push(Task::Enter(e));
                        }
                    }
                    PseudoExpr::Tuple(items) => {
                        stack.push(Task::Post(Post::Tuple { count: items.len() }));
                        for i in items.into_iter().rev() {
                            stack.push(Task::Enter(i));
                        }
                    }
                    PseudoExpr::Pair(a, b) => {
                        stack.push(Task::Post(Post::Pair));
                        stack.push(Task::Enter(b.into_inner()));
                        stack.push(Task::Enter(a.into_inner()));
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
                            stack.push(Task::Enter(f));
                        }
                    }
                    PseudoExpr::Delay(inner) => {
                        stack.push(Task::Post(Post::Delay));
                        stack.push(Task::Enter(inner.into_inner()));
                    }
                    PseudoExpr::Force(inner) => {
                        stack.push(Task::Post(Post::Force));
                        stack.push(Task::Enter(inner.into_inner()));
                    }
                    PseudoExpr::Trace { message, value } => {
                        stack.push(Task::Post(Post::Trace));
                        stack.push(Task::Enter(value.into_inner()));
                        stack.push(Task::Enter(message.into_inner()));
                    }
                    other => done.push(Rebuilt::Expr(other)),
                },
                Task::Post(op) => match op {
                    Post::Lambda { params } => {
                        let body = pop_expr(&mut done);
                        self.pop_scope();
                        done.push(Rebuilt::Expr(PseudoExpr::Lambda {
                            params,
                            body: PBox::new(body),
                        }));
                    }
                    Post::RecFn { name, params } => {
                        let body = pop_expr(&mut done);
                        self.pop_scope();
                        done.push(Rebuilt::Expr(PseudoExpr::RecFn {
                            name,
                            params,
                            body: PBox::new(body),
                        }));
                    }
                    Post::LetBody { name, id, body } => {
                        let value = pop_expr(&mut done);
                        if let Some(vid) = id {
                            self.push_scope_with_ids(std::iter::once((name.clone(), vid)));
                        } else {
                            self.push_scope_with_ids(std::iter::empty());
                        }
                        stack.push(Task::Post(Post::LetPost { name, id, value }));
                        stack.push(Task::Enter(body));
                    }
                    Post::LetPost { name, id, value } => {
                        let body = pop_expr(&mut done);
                        self.pop_scope();
                        done.push(Rebuilt::Expr(PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }));
                    }
                    Post::WhenClauseStart { bound } => {
                        self.push_scope_with_ids(bound);
                    }
                    Post::WhenClauseEnd { pattern, has_guard } => {
                        let guard = if has_guard {
                            Some(pop_expr(&mut done))
                        } else {
                            None
                        };
                        let body = pop_expr(&mut done);
                        self.pop_scope();
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
                    Post::Apply { argc } => {
                        let args = take_expr(&mut done, argc);
                        let function = pop_expr(&mut done);
                        done.push(Rebuilt::Expr(PseudoExpr::Apply {
                            function: PBox::new(function),
                            args: args.into(),
                        }));
                    }
                    Post::FieldAccess { selector } => {
                        let record = pop_expr(&mut done);
                        done.push(Rebuilt::Expr(PseudoExpr::FieldAccess {
                            record: PBox::new(record),
                            selector,
                        }));
                    }
                    Post::IndexAccess { index } => {
                        let collection = pop_expr(&mut done);
                        done.push(Rebuilt::Expr(PseudoExpr::IndexAccess {
                            collection: PBox::new(collection),
                            index,
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

        debug_assert_eq!(done.len(), 1, "go machine must leave one result");
        pop_expr(&mut done)
    }
}

fn pattern_bound_binders(pattern: &WhenPattern) -> Vec<(String, VarId)> {
    match pattern {
        WhenPattern::Constructor { fields, .. } => fields
            .iter()
            .map(|binder| (binder.to_string(), binder.var_id()))
            .collect(),
        WhenPattern::Pair(a, b) => vec![(a.to_string(), a.var_id()), (b.to_string(), b.var_id())],
        WhenPattern::Tuple(fields) => fields
            .iter()
            .map(|binder| (binder.to_string(), binder.var_id()))
            .collect(),
        WhenPattern::List { elements, tail } => {
            let mut names: Vec<(String, VarId)> = elements
                .iter()
                .map(|binder| (binder.to_string(), binder.var_id()))
                .collect();
            if let Some(t) = tail {
                names.push((t.to_string(), t.var_id()));
            }
            names
        }
        WhenPattern::Var(b) => vec![(b.to_string(), b.var_id())],
        WhenPattern::Wildcard | WhenPattern::Literal(_) => vec![],
    }
}

#[cfg(test)]
mod tests;
