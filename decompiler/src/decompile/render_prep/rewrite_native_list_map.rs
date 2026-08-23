//! Recognise `list.map(xs, f)` from the native-list `rec fn` shape
//! produced by `lift_list_fold_to_when` + `decode_church_to_native`.
//!
//! After those two, a map helper is a 1-param `RecFn` whose `When`
//! body rebuilds `[F(xs.head), ..self(xs[1..])]`. Replacing the whole
//! `RecFn` with a `Lambda` that calls `list.map` is only sound if the
//! cons arm is a true map cell — not a filter, fold, or rebuild that
//! still mentions `xs` besides `.head`.
//!
//! - RecFn must have exactly 1 param and a `When` body with exactly two
//!   clauses (nil + cons).
//! - The nil arm body must be `[]`, a `Var` named `e`, or an empty
//!   tag-0 `Constr` — the church-encoded empty list. The `church_true`
//!   pre-decode form is left to `cse_church_list_map_helpers`.
//! - The cons-arm pattern is `[_, ..]` (wildcard head + tail) — the
//!   shape `lift_list_fold_to_when` produces. An explicit `[h, ..t]`
//!   is also accepted; its `Var(h)` references are substituted too.
//! - The cons-arm body, after peeling its leading `Let` chain, must be
//!   `List { elements: [head_expr], tail: Some(t) }` or a 2-arg call
//!   to a collected church-cons helper, where `t` is
//!   `Apply(Var(self_id), [tail_ref])` and `tail_ref` resolves to
//!   `xs[1..]` or the tail binder.
//! - The outer lambda reuses the original arg-binder; the head lambda
//!   reuses an explicit head binder's VarId, else mints a fresh one.
//! - `xs.head` inside head_expr becomes the new head binder. Other
//!   references to `xs` are left intact — they would mark a non-map
//!   shape the predicate should have rejected.

use crate::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

/// One pending step of the walks below.
enum Step {
    Enter(PseudoExpr),
    Post(NodePost),
}

/// Everything about a node that is NOT one of its child expressions, held
/// while those children are being rewritten.
enum NodePost {
    Let {
        name: String,
        id: Option<VarId>,
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
        /// Per clause: its pattern (never descended into) and whether it had a guard.
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// Queue `expr`'s children — pushed in REVERSE so they pop in source order —
/// behind the `Post` that rebuilds the node. `Err(leaf)` for a node with no
/// children, which both walks return unchanged.
fn push_children(expr: PseudoExpr, steps: &mut Vec<Step>) -> Result<(), PseudoExpr> {
    match expr {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } => {
            steps.push(Step::Post(NodePost::Let { name, id }));
            steps.push(Step::Enter(body.into_inner()));
            steps.push(Step::Enter(value.into_inner()));
        }
        PseudoExpr::Lambda { params, body } => {
            steps.push(Step::Post(NodePost::Lambda { params }));
            steps.push(Step::Enter(body.into_inner()));
        }
        PseudoExpr::RecFn { name, params, body } => {
            steps.push(Step::Post(NodePost::RecFn { name, params }));
            steps.push(Step::Enter(body.into_inner()));
        }
        PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } => {
            let mut clause_meta = Vec::with_capacity(clauses.len());
            let mut clause_children = Vec::new();
            for c in clauses {
                clause_meta.push((c.pattern, c.guard.is_some()));
                if let Some(g) = c.guard {
                    clause_children.push(g);
                }
                clause_children.push(c.body);
            }
            steps.push(Step::Post(NodePost::When {
                subject_name,
                clause_meta,
            }));
            for c in clause_children.into_iter().rev() {
                steps.push(Step::Enter(c));
            }
            steps.push(Step::Enter(subject.into_inner()));
        }
        other => match plain_children(other) {
            Ok((kind, children)) => {
                steps.push(Step::Post(NodePost::Plain(kind)));
                for c in children.into_iter().rev() {
                    steps.push(Step::Enter(c));
                }
            }
            Err(leaf) => return Err(leaf),
        },
    }
    Ok(())
}

/// Rebuild a node from its already-rewritten children, popped off `done` in
/// the same source order they were pushed in.
fn rebuild(post: NodePost, done: &mut Vec<PseudoExpr>) -> PseudoExpr {
    match post {
        NodePost::Let { name, id } => {
            let body = done.pop().expect("let body");
            let value = done.pop().expect("let value");
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }
        NodePost::Lambda { params } => PseudoExpr::Lambda {
            params,
            body: PBox::new(done.pop().expect("lambda body")),
        },
        NodePost::RecFn { name, params } => PseudoExpr::RecFn {
            name,
            params,
            body: PBox::new(done.pop().expect("recfn body")),
        },
        NodePost::When {
            subject_name,
            clause_meta,
        } => {
            let total = 1 + clause_meta
                .iter()
                .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                .sum::<usize>();
            let mut parts = take(done, total).into_iter();
            let subject = parts.next().expect("when subject");
            let clauses = clause_meta
                .into_iter()
                .map(|(pattern, has_guard)| WhenClause {
                    pattern,
                    guard: has_guard.then(|| parts.next().expect("when guard")),
                    body: parts.next().expect("when clause body"),
                })
                .collect();
            PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses,
            }
        }
        NodePost::Plain(kind) => rebuild_plain(kind, done),
    }
}

pub(super) fn rewrite_native_list_map(expr: PseudoExpr) -> PseudoExpr {
    let mut helpers: std::collections::HashSet<VarId> = Default::default();
    collect_church_cons_helpers(&expr, &mut helpers);
    rewrite(expr, &helpers)
}

/// Collect VarIds whose let-bound value is the church-cons template
/// `fn(x, y) { [x, ..y] }`. `decode_church_to_native` leaves these
/// behind where a bare reference kept `inline_constructor_helpers`
/// from dropping the helper.
fn collect_church_cons_helpers(expr: &PseudoExpr, out: &mut std::collections::HashSet<VarId>) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::Let {
            id: Some(vid),
            value,
            ..
        } = cur
        {
            if is_church_cons_helper_body(value.as_ref()) {
                out.insert(*vid);
            }
        }
        pending.extend(children(cur).into_iter().rev());
    }
}

fn is_church_cons_helper_body(expr: &PseudoExpr) -> bool {
    let PseudoExpr::Lambda { params, body } = expr else {
        return false;
    };
    if params.len() != 2 {
        return false;
    }
    let head_id = params[0].id;
    let tail_id = params[1].id;
    let PseudoExpr::List {
        elements,
        tail: Some(tail_box),
    } = body.as_ref()
    else {
        return false;
    };
    if elements.len() != 1 {
        return false;
    }
    let head_ok = matches!(&elements[0], PseudoExpr::Var { id: Some(v), .. } if *v == head_id);
    let tail_ok = matches!(tail_box.as_ref(), PseudoExpr::Var { id: Some(v), .. } if *v == tail_id);
    head_ok && tail_ok
}

fn children(expr: &PseudoExpr) -> Vec<&PseudoExpr> {
    use crate::pseudo::ast::WhenClause;
    let mut out = Vec::new();
    match expr {
        PseudoExpr::Let { value, body, .. } => {
            out.push(value.as_ref());
            out.push(body.as_ref());
        }
        PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
            out.push(body.as_ref());
        }
        PseudoExpr::Apply { function, args } => {
            out.push(function.as_ref());
            for a in args {
                out.push(a);
            }
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            out.push(condition.as_ref());
            out.push(then_branch.as_ref());
            out.push(else_branch.as_ref());
        }
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            out.push(subject.as_ref());
            for WhenClause { guard, body, .. } in clauses {
                if let Some(g) = guard {
                    out.push(g);
                }
                out.push(body);
            }
        }
        PseudoExpr::List { elements, tail } => {
            for e in elements {
                out.push(e);
            }
            if let Some(t) = tail {
                out.push(t.as_ref());
            }
        }
        PseudoExpr::Tuple(items) => {
            for i in items {
                out.push(i);
            }
        }
        PseudoExpr::Pair(a, b) => {
            out.push(a.as_ref());
            out.push(b.as_ref());
        }
        PseudoExpr::Constr { fields, .. } => {
            for f in fields {
                out.push(f);
            }
        }
        PseudoExpr::FieldAccess { record, .. } => {
            out.push(record.as_ref());
        }
        PseudoExpr::IndexAccess { collection, .. } => {
            out.push(collection.as_ref());
        }
        PseudoExpr::BinOp { left, right, .. } => {
            out.push(left.as_ref());
            out.push(right.as_ref());
        }
        PseudoExpr::UnOp { operand, .. } => {
            out.push(operand.as_ref());
        }
        PseudoExpr::BuiltinCall { args, .. } => {
            for a in args {
                out.push(a);
            }
        }
        PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
            out.push(inner.as_ref());
        }
        PseudoExpr::Trace { message, value } => {
            out.push(message.as_ref());
            out.push(value.as_ref());
        }
        _ => {}
    }
    out
}

/// Bottom-up: rebuild each node from its rewritten children, then run
/// `try_rewrite_recfn` on it.
fn rewrite(expr: PseudoExpr, helpers: &std::collections::HashSet<VarId>) -> PseudoExpr {
    let mut steps: Vec<Step> = vec![Step::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(expr) => {
                if let Err(leaf) = push_children(expr, &mut steps) {
                    // `recurse_children` returned a leaf unchanged and
                    // `try_rewrite_recfn` is the identity on a non-`RecFn`.
                    done.push(leaf);
                }
            }
            Step::Post(post) => {
                let rebuilt = rebuild(post, &mut done);
                done.push(try_rewrite_recfn(rebuilt, helpers));
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite must leave exactly one result");
    done.pop().expect("rewrite result")
}

fn try_rewrite_recfn(expr: PseudoExpr, helpers: &std::collections::HashSet<VarId>) -> PseudoExpr {
    let PseudoExpr::RecFn { name, params, body } = expr else {
        return expr;
    };
    if params.len() != 1 {
        return PseudoExpr::RecFn { name, params, body };
    }
    let arg_binder = &params[0];
    let arg_id = arg_binder.id;
    let self_id = name.id;
    let PseudoExpr::When {
        subject,
        subject_name,
        clauses,
    } = body.as_ref()
    else {
        return PseudoExpr::RecFn { name, params, body };
    };
    if !var_id_is(subject, arg_id) || clauses.len() != 2 {
        return PseudoExpr::RecFn { name, params, body };
    }
    let _ = subject_name;
    let (nil_idx, cons_idx) = match (
        is_nil_pattern(&clauses[0].pattern),
        is_nil_pattern(&clauses[1].pattern),
    ) {
        (true, false) => (0, 1),
        (false, true) => (1, 0),
        _ => return PseudoExpr::RecFn { name, params, body },
    };
    let nil_arm = &clauses[nil_idx];
    let cons_arm = &clauses[cons_idx];
    if !is_empty_list_literal(&nil_arm.body) {
        return PseudoExpr::RecFn { name, params, body };
    }
    // Cons pattern `[_, ..]`: a wildcard head binder is named `_`, so
    // any other name is an explicit binder.
    let (head_binder_id_explicit, tail_binder_id) = match &cons_arm.pattern {
        WhenPattern::List {
            elements,
            tail: Some(tail_b),
        } if elements.len() == 1 => {
            let head_is_explicit = elements[0].name != "_";
            (
                if head_is_explicit {
                    Some(elements[0].id)
                } else {
                    None
                },
                Some(tail_b.id),
            )
        }
        _ => return PseudoExpr::RecFn { name, params, body },
    };
    let head_name_explicit = match &cons_arm.pattern {
        WhenPattern::List { elements, .. } if elements.len() == 1 && elements[0].name != "_" => {
            Some(elements[0].name.clone())
        }
        _ => None,
    };
    // Peel the leading let-chain.
    let mut let_chain: Vec<(String, Option<VarId>, PseudoExpr)> = Vec::new();
    let mut cur = &cons_arm.body;
    while let PseudoExpr::Let {
        name: ln,
        id,
        value,
        body: lb,
    } = cur
    {
        let_chain.push((ln.clone(), *id, value.as_ref().clone()));
        cur = lb.as_ref();
    }
    // Final cons cell: a native `List` with one element and a tail, or a
    // 2-arg call to a collected church-cons helper.
    let (head_expr, tail_expr) = match cur {
        PseudoExpr::List {
            elements,
            tail: Some(tail_box),
        } if elements.len() == 1 => (elements[0].clone(), tail_box.as_ref().clone()),
        PseudoExpr::Apply { function, args } if args.len() == 2 => {
            if let PseudoExpr::Var { id: Some(vid), .. } = function.as_ref() {
                if helpers.contains(vid) {
                    (args[0].clone(), args[1].clone())
                } else {
                    return PseudoExpr::RecFn { name, params, body };
                }
            } else {
                return PseudoExpr::RecFn { name, params, body };
            }
        }
        _ => return PseudoExpr::RecFn { name, params, body },
    };
    // Recursive call: `self(arg[1..])` or `self(tail_binder)`.
    let PseudoExpr::Apply {
        function: rfn,
        args: rargs,
    } = &tail_expr
    else {
        return PseudoExpr::RecFn { name, params, body };
    };
    if !var_id_is(rfn, self_id) || rargs.len() != 1 {
        return PseudoExpr::RecFn { name, params, body };
    }
    if !is_tail_ref_of(&rargs[0], arg_id, tail_binder_id) {
        return PseudoExpr::RecFn { name, params, body };
    }
    // Build the head lambda.
    let head_id = head_binder_id_explicit.unwrap_or_else(VarId::fresh_binding);
    let head_name = head_name_explicit.unwrap_or_else(|| "head".to_string());
    let mut head_body = head_expr;
    // Re-wrap with original let-chain, substituting `xs.head` and
    // (if explicit) the head binder with the new head Var.
    for (ln, lid, lvalue) in let_chain.into_iter().rev() {
        let new_value = substitute_head(lvalue, arg_id, head_binder_id_explicit, head_id);
        head_body = PseudoExpr::Let {
            name: ln,
            id: lid,
            value: PBox::new(new_value),
            body: PBox::new(head_body),
        };
    }
    head_body = substitute_head(head_body, arg_id, head_binder_id_explicit, head_id);
    // `substitute_head` stamps every head reference with `head_id` and
    // the placeholder display name `"head"`. With an explicit source
    // binder (e.g. `entry`) on the parameter, those refs would render
    // as a free `head`, so rename them to the parameter's name.
    head_body = normalize_head_ref_names(head_body, head_id, &head_name);
    let head_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new(head_name, head_id)],
        body: PBox::new(head_body),
    };
    // `list.map` is a synthetic `Var` applied to two args; the
    // renderer prints the name verbatim.
    let list_map_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: "list.map".to_string(),
            id: None,
        }),
        args: vec![
            PseudoExpr::Var {
                name: arg_binder.name.clone(),
                id: Some(arg_id),
            },
            head_lambda,
        ]
        .into(),
    };
    PseudoExpr::Lambda {
        params: vec![arg_binder.clone()],
        body: PBox::new(list_map_call),
    }
}

/// Set the display name of every `Var` carrying `head_id` to
/// `head_name`, so head references agree with the head lambda
/// parameter whichever `substitute_head` branch produced them.
fn normalize_head_ref_names(expr: PseudoExpr, head_id: VarId, head_name: &str) -> PseudoExpr {
    struct HeadRenamer<'a> {
        head_id: VarId,
        head_name: &'a str,
    }
    impl ExprFolder for HeadRenamer<'_> {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
            if id == Some(self.head_id) {
                return PseudoExpr::Var {
                    name: self.head_name.to_string(),
                    id,
                };
            }
            PseudoExpr::Var { name, id }
        }
    }
    HeadRenamer { head_id, head_name }.fold(expr)
}

/// Replace `arg_id`'s `.head` projection (and, when the cons pattern had an
/// explicit head binder, that binder's references) with the new head `Var`.
fn substitute_head(
    expr: PseudoExpr,
    arg_id: VarId,
    explicit_head_id: Option<VarId>,
    new_head_id: VarId,
) -> PseudoExpr {
    let mut steps: Vec<Step> = vec![Step::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(expr) => match expr {
                PseudoExpr::FieldAccess {
                    record,
                    selector: FieldSelector::ListHead,
                } if var_id_is(record.as_ref(), arg_id) => done.push(PseudoExpr::Var {
                    name: "head".to_string(),
                    id: Some(new_head_id),
                }),
                PseudoExpr::Var {
                    name: _,
                    id: Some(v),
                } if explicit_head_id == Some(v) => done.push(PseudoExpr::Var {
                    name: "head".to_string(),
                    id: Some(new_head_id),
                }),
                other => {
                    if let Err(leaf) = push_children(other, &mut steps) {
                        done.push(leaf);
                    }
                }
            },
            Step::Post(post) => {
                let rebuilt = rebuild(post, &mut done);
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "substitute_head must leave one result");
    done.pop().expect("substitute_head result")
}

fn var_id_is(expr: &PseudoExpr, expected: VarId) -> bool {
    matches!(expr, PseudoExpr::Var { id: Some(v), .. } if *v == expected)
}

fn is_nil_pattern(p: &WhenPattern) -> bool {
    match p {
        WhenPattern::List {
            elements,
            tail: None,
        } => elements.is_empty(),
        WhenPattern::Constructor {
            shape: ConstructorShape::Known(KnownConstructor::Nil),
            ..
        } => true,
        _ => false,
    }
}

fn is_empty_list_literal(expr: &PseudoExpr) -> bool {
    match expr {
        PseudoExpr::List {
            elements,
            tail: None,
        } if elements.is_empty() => true,
        // V1/V2 scripts bind `const e = Unknown_E_0_0` at module top —
        // the church-encoded empty list. `decode_church_to_native`
        // resolves it to a literal `[]`, but uses still render as a
        // Var named `e`, so treat that as equivalent.
        PseudoExpr::Var { name, .. } if name == "e" => true,
        // Same sentinel as a bare `Constr`, in scopes that never
        // routed it through the `e` binding.
        PseudoExpr::Constr { tag: 0, fields, .. } if fields.is_empty() => true,
        _ => false,
    }
}

/// `arg[1..]` is `Apply(BuiltinCall(ListTail,[]), [Var(arg_id)])` OR
/// `BuiltinCall(ListTail, [Var(arg_id)])`, OR if a tail-binder is
/// available, `Var(tail_binder_id)`.
fn is_tail_ref_of(expr: &PseudoExpr, arg_id: VarId, tail_binder: Option<VarId>) -> bool {
    if let Some(tb) = tail_binder {
        if matches!(expr, PseudoExpr::Var { id: Some(v), .. } if *v == tb) {
            return true;
        }
    }
    let arg_expr =
        |e: &PseudoExpr| matches!(e, PseudoExpr::Var { id: Some(v), .. } if *v == arg_id);
    match expr {
        PseudoExpr::BuiltinCall { name, args } if *name == BuiltinId::ListTail => {
            args.len() == 1 && arg_expr(&args[0])
        }
        PseudoExpr::Apply { function, args } => match function.as_ref() {
            PseudoExpr::BuiltinCall {
                name,
                args: builtin_args,
            } if *name == BuiltinId::ListTail && builtin_args.is_empty() => {
                args.len() == 1 && arg_expr(&args[0])
            }
            _ => false,
        },
        _ => false,
    }
}
