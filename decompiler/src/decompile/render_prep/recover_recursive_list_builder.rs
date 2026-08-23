//! Recover the Constr-encoded list a recursive builder produces, both
//! arms at once.
//!
//! [`super::recover_constr_cons_spread`] folds a cons cell whose tail
//! already resolves to a list, and deliberately stops at the recursive
//! shape:
//!
//! ```text
//! rec fn o(z) {
//!   case_list(Unknown_E_0_0, fn(x, y) { Unknown_E_2_1(x, o(y)) }, z)
//! }
//! ```
//!
//! Its cons tail is a CALL, which no value-level chase can resolve, and
//! its nil arm is the shared nullary stub — folding one without the
//! other would swap a stub for a spread with a stub tail, which reads
//! worse than either. PlutusTx emits this builder for every
//! `BuiltinList → [a]` conversion, so the two stubs are the most
//! repeated things in a PlutusTx-compiled script: 36 of the 140
//! stub-constructor mentions in one V3 corpus script.
//!
//! The recursion is the proof the value chase was missing. A
//! one-parameter recursive function that emits `Constr<1>(head,
//! self(tail))` builds a list by induction: the cell is a list if the
//! recursive result is, and the base case is whatever the other arm
//! returns. So inside such a function — and only inside it — the nullary
//! `Constr<0>` IS that base case, and both arms relabel together:
//! `[]` and `[head, ..self(tail)]`.
//!
//! Why the base case is safe to name: every result position of one
//! function has one type. The source this came from was typed, so a
//! function that returns a cons cell on one path cannot return an
//! unrelated nullary value on another — and tag 0 is the only nullary
//! tag the cons-shaped type can have. That is what the sibling pass
//! could not assume: it sees the stub from OUTSIDE any function, where
//! the same shape really is shared with genuine nullary enum values.
//!
//! A cons-shaped user ADT (`Done | Node(head, self(tail))`) renders as a
//! list here. It is one: the constructor NAMES were already lost to the
//! stub, and `[head, ..tail]` says more about the value than
//! `Unknown_E_2_1(head, tail)` does.
//!
//! Scoped to one function body. A nested `RecFn` is a different builder
//! and is left for its own turn — it supplies no evidence for the outer
//! one either. Nothing outside the proven body is touched, so the stub
//! keeps whatever other meanings it carries elsewhere.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PVec;
use std::collections::HashSet;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{
    PlainPost, children, plain_children, rebuild_plain, rewrite_bottom_up, take,
};

pub(super) fn recover_recursive_list_builder(expr: PseudoExpr) -> PseudoExpr {
    // The Scott nil is a MODULE-LEVEL function here, so the set has to
    // be read off the whole tree before descending into any builder.
    let (nils, conses) = collect_scott_list_fns(&expr);
    walk(expr, &nils, &conses)
}

fn walk(expr: PseudoExpr, nils: &HashSet<VarId>, conses: &HashSet<VarId>) -> PseudoExpr {
    rewrite_bottom_up(expr, |expr| {
        let PseudoExpr::RecFn { name, params, body } = expr else {
            return expr;
        };
        let self_id = name.var_id();
        if params.len() != 1 {
            return PseudoExpr::RecFn { name, params, body };
        }
        // Binders holding this function's own result: `let t = self(xs)`.
        // The cons cell's tail often reaches the cell through one.
        let aliases = collect_self_call_aliases(&body, self_id);
        let ctx = Ctx {
            self_id,
            aliases,
            nils,
            conses,
        };
        if !builds_list_by_recursion(&body, &ctx) {
            return PseudoExpr::RecFn { name, params, body };
        }
        PseudoExpr::RecFn {
            name,
            params,
            body: PBox::new(relabel(body.into_inner(), &ctx, true)),
        }
    })
}

/// What a single builder is proven against.
struct Ctx<'a> {
    self_id: VarId,
    /// Binders bound to `self(x)` inside this body.
    aliases: HashSet<VarId>,
    /// Functions that ARE the Scott nil, program-wide.
    nils: &'a HashSet<VarId>,
    /// Functions that ARE the Scott cons, program-wide.
    conses: &'a HashSet<VarId>,
}

/// Binders whose value is this function calling itself.
fn collect_self_call_aliases(body: &PseudoExpr, self_id: VarId) -> HashSet<VarId> {
    struct Collect {
        self_id: VarId,
        found: HashSet<VarId>,
    }
    impl ExprVisitor for Collect {
        fn visit_let(
            &mut self,
            _name: &str,
            id: &Option<VarId>,
            value: &PseudoExpr,
            _body: &PseudoExpr,
        ) {
            if let Some(vid) = id
                && let PseudoExpr::Apply { function, args } = value
                && args.len() == 1
                && matches!(
                    strip_force(function),
                    PseudoExpr::Var { id: Some(v), .. } if *v == self.self_id
                )
            {
                self.found.insert(*vid);
            }
        }
    }
    let mut c = Collect {
        self_id,
        found: HashSet::new(),
    };
    c.walk(body);
    c.found
}

/// The two halves of the Scott list encoding, found STRUCTURALLY —
/// never by name — anywhere in the program:
///
/// ```text
/// nil       = fn(n, _) { n }          `λn.λc. n`
/// cons h t  = fn(_, c) { c(h, t) }    `λh.λt.λn.λc. c h t`
/// ```
///
/// `nil` is also the church `True`, which is why the naming settled on
/// `church_true` and left `[] -> church_true` sitting in a list builder.
/// Being that term is NOT on its own a reason to call it the empty
/// list — what licenses the relabel is the same thing that licensed it
/// for the `Constr<0>` spelling: the enclosing function is a PROVEN list
/// builder and the reference sits in its result position. A program that
/// only ever uses `fn(n, _) { n }` as a boolean has no proven builder to
/// relabel inside, so the set stays inert.
///
/// The cons set carries its own weight: it is what recognises the
/// `church_cons(head, self(tail))` CALL as a cons cell, and there the
/// four-parameter shape is the whole proof.
fn collect_scott_list_fns(expr: &PseudoExpr) -> (HashSet<VarId>, HashSet<VarId>) {
    /// Flatten the curried form: `fn(a) { fn(b) { … } }` and
    /// `fn(a, b) { … }` are the same function.
    fn uncurry(expr: &PseudoExpr) -> (Vec<VarId>, &PseudoExpr) {
        let mut params = Vec::new();
        let mut cur = expr;
        while let PseudoExpr::Lambda { params: p, body } = cur {
            params.extend(p.iter().map(|b| b.var_id()));
            cur = body;
        }
        (params, cur)
    }
    fn is_scott_nil(value: &PseudoExpr) -> bool {
        let (params, body) = uncurry(value);
        params.len() == 2 && matches!(body, PseudoExpr::Var { id: Some(v), .. } if *v == params[0])
    }
    fn is_scott_cons(value: &PseudoExpr) -> bool {
        let (params, body) = uncurry(value);
        // h, t, n, c — `n` is bound but unused, `c` gets `(h, t)`.
        if params.len() != 4 {
            return false;
        }
        let PseudoExpr::Apply { function, args } = body else {
            return false;
        };
        args.len() == 2
            && matches!(function.as_ref(), PseudoExpr::Var { id: Some(v), .. } if *v == params[3])
            && matches!(&args[0], PseudoExpr::Var { id: Some(v), .. } if *v == params[0])
            && matches!(&args[1], PseudoExpr::Var { id: Some(v), .. } if *v == params[1])
    }
    struct Collect {
        nils: HashSet<VarId>,
        conses: HashSet<VarId>,
    }
    impl ExprVisitor for Collect {
        fn visit_let(
            &mut self,
            _name: &str,
            id: &Option<VarId>,
            value: &PseudoExpr,
            _body: &PseudoExpr,
        ) {
            let Some(vid) = id else { return };
            if is_scott_nil(value) {
                self.nils.insert(*vid);
            } else if is_scott_cons(value) {
                self.conses.insert(*vid);
            }
        }
    }
    let mut c = Collect {
        nils: HashSet::new(),
        conses: HashSet::new(),
    };
    c.walk(expr);
    (c.nils, c.conses)
}

/// Whether the body emits `Constr<1>(head, self(tail))` — the cell whose
/// list-ness the recursion establishes.
fn builds_list_by_recursion(body: &PseudoExpr, ctx: &Ctx) -> bool {
    let mut stack: Vec<&PseudoExpr> = vec![body];
    while let Some(body) = stack.pop() {
        // Stop where the relabel stops. A nested `RecFn` that happens to
        // call the outer function would otherwise supply evidence for a
        // body the rewrite never visits — proving one function from
        // another's shape.
        if matches!(body, PseudoExpr::RecFn { .. }) {
            continue;
        }
        if cons_cell_recursing_on(body, ctx).is_some()
            || spread_recursing_on(body, ctx)
            || scott_cons_recursing_on(body, ctx).is_some()
        {
            return true;
        }
        for c in children(body).into_iter().rev() {
            stack.push(c);
        }
    }
    false
}

/// Whether `expr` is the cons cell ALREADY recovered into a spread —
/// `[head, ..self(tail)]`.
///
/// A sibling pass folds some of these before this one runs, and the
/// result is the same proof: a one-parameter recursive function whose
/// cons arm is a list with the recursive result as its tail builds a
/// list by induction, so the other arm is its base case.
fn spread_recursing_on(expr: &PseudoExpr, ctx: &Ctx) -> bool {
    let PseudoExpr::List { elements, tail } = expr else {
        return false;
    };
    elements.len() == 1 && tail.as_deref().is_some_and(|t| is_self_result(t, ctx))
}

/// The cons cell written as a CALL to the Scott cons —
/// `church_cons(head, self(tail))`. Returns `(head, tail)`.
fn scott_cons_recursing_on<'a>(
    expr: &'a PseudoExpr,
    ctx: &Ctx,
) -> Option<(&'a PseudoExpr, &'a PseudoExpr)> {
    let PseudoExpr::Apply { function, args } = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let PseudoExpr::Var { id: Some(v), .. } = strip_force(function) else {
        return None;
    };
    if !ctx.conses.contains(v) || !is_self_result(&args[1], ctx) {
        return None;
    }
    Some((&args[0], &args[1]))
}

/// The recursive result: the self-call itself, or a binder holding it.
/// `let t = self(xs)` then `[h, ..t]` is the same cell written in two
/// steps, and the lowering writes it that way whenever the tail is used
/// more than once.
fn is_self_result(expr: &PseudoExpr, ctx: &Ctx) -> bool {
    match strip_force(expr) {
        PseudoExpr::Apply { function, args } => {
            args.len() == 1
                && matches!(strip_force(function), PseudoExpr::Var { id: Some(v), .. } if *v == ctx.self_id)
        }
        PseudoExpr::Var { id: Some(v), .. } => ctx.aliases.contains(v),
        _ => false,
    }
}

/// The `(head, tail)` of a cons cell whose tail is this function calling
/// itself.
fn cons_cell_recursing_on<'a>(
    expr: &'a PseudoExpr,
    ctx: &Ctx,
) -> Option<(&'a PseudoExpr, &'a PseudoExpr)> {
    let PseudoExpr::Constr {
        tag: 1,
        fields,
        shape,
        ..
    } = expr
    else {
        return None;
    };
    if !is_cons_shape(shape) || fields.len() != 2 {
        return None;
    }
    if !is_self_result(&fields[1], ctx) {
        return None;
    }
    // A head that is a `let` chain is a statement sequence, and the list
    // literal renders its elements inline — `[let x = ..\n f(x), ..t]`
    // reads as broken syntax, which is worse than the stub it replaces.
    if matches!(fields[0], PseudoExpr::Let { .. }) {
        return None;
    }
    Some((&fields[0], &fields[1]))
}

/// Rewrite both arms inside the proven builder. Stops at a nested
/// `RecFn`: that is a different function, with its own base case.
///
/// `result` tracks whether the position being rewritten is one the
/// builder RETURNS from. Only there is a nullary `Constr<0>` the base
/// case: the same stub passed as an argument — `g(Constr<0>)` inside the
/// cons arm — is some other nullary value, and calling it `[]` would
/// state something false. The cons cell carries its own proof (its tail
/// is the self-call) and is folded wherever it appears.
fn relabel(expr: PseudoExpr, ctx: &Ctx, result: bool) -> PseudoExpr {
    let mut steps: Vec<RelabelStep> = vec![RelabelStep::Enter(expr, result)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RelabelStep::Enter(expr, result) => match expr {
                // Stops at a nested `RecFn`: that is a different function,
                // with its own base case. Neither descended into nor folded.
                PseudoExpr::RecFn { .. } => done.push(expr),
                // A `let` returns its body; its value is a side computation.
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(RelabelStep::Post(RelabelPost::Let { name, id }, result));
                    steps.push(RelabelStep::Enter(body.into_inner(), result));
                    steps.push(RelabelStep::Enter(value.into_inner(), false));
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
                            clause_children.push((g, false));
                        }
                        clause_children.push((c.body, result));
                    }
                    steps.push(RelabelStep::Post(
                        RelabelPost::When {
                            subject_name,
                            clause_meta,
                        },
                        result,
                    ));
                    for (c, r) in clause_children.into_iter().rev() {
                        steps.push(RelabelStep::Enter(c, r));
                    }
                    steps.push(RelabelStep::Enter(subject.into_inner(), false));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(RelabelStep::Post(RelabelPost::Plain(PlainPost::If), result));
                    steps.push(RelabelStep::Enter(else_branch.into_inner(), result));
                    steps.push(RelabelStep::Enter(then_branch.into_inner(), result));
                    steps.push(RelabelStep::Enter(condition.into_inner(), false));
                }
                // The message is passed through untouched, exactly as the
                // recursion left it; only the value is a child.
                PseudoExpr::Trace { message, value } => {
                    steps.push(RelabelStep::Post(RelabelPost::Trace { message }, result));
                    steps.push(RelabelStep::Enter(value.into_inner(), result));
                }
                // A list eliminator takes its branches as ARGUMENTS: the nil arm
                // of `case_list(nil, fn(h, t) { cons }, xs)` is arg 0. The
                // witness is a LAMBDA argument carrying the cons cell — that is
                // the cons CONTINUATION, and only a call shaped like an
                // eliminator has one. Accepting any argument that merely
                // contains a cons somewhere would make an ordinary
                // `f(Unknown_E_0_0, g(.., cons, ..))` relabel its first
                // argument.
                PseudoExpr::Apply { .. } => {
                    // A Scott-cons call is itself an `Apply`; recognise it here
                    // rather than letting the generic path keep result-position
                    // on its arguments.
                    let scott = scott_cons_recursing_on(&expr, ctx).is_some();
                    let PseudoExpr::Apply { function, args } = expr else {
                        unreachable!("matched Apply above");
                    };
                    let eliminator = args.iter().any(|a| {
                        matches!(a, PseudoExpr::Lambda { .. }) && contains_cons_cell(a, ctx)
                    });
                    // For a Scott-cons call NEITHER argument is in result
                    // position: the head is an ELEMENT and the tail is the
                    // recursive call. Carrying `result` in would let a head that
                    // happens to be the nil term become `[]` — `cons(nil,
                    // self(t))` is a list whose first element is `nil`, not
                    // `[[], ..]`.
                    let arg_result = if scott { false } else { result && eliminator };
                    let argc = args.len();
                    steps.push(RelabelStep::Post(
                        RelabelPost::Plain(PlainPost::Apply { argc }),
                        result,
                    ));
                    for a in args.into_vec().into_iter().rev() {
                        steps.push(RelabelStep::Enter(a, arg_result));
                    }
                    steps.push(RelabelStep::Enter(function.into_inner(), false));
                }
                // The eliminator's cons continuation returns the cell.
                PseudoExpr::Lambda { params, body } => {
                    steps.push(RelabelStep::Post(RelabelPost::Lambda { params }, result));
                    steps.push(RelabelStep::Enter(body.into_inner(), result));
                }
                // Thunk wrappers pass the value through unchanged.
                PseudoExpr::Force(inner) => {
                    steps.push(RelabelStep::Post(
                        RelabelPost::Plain(PlainPost::Force),
                        result,
                    ));
                    steps.push(RelabelStep::Enter(inner.into_inner(), result));
                }
                PseudoExpr::Delay(inner) => {
                    steps.push(RelabelStep::Post(
                        RelabelPost::Plain(PlainPost::Delay),
                        result,
                    ));
                    steps.push(RelabelStep::Enter(inner.into_inner(), result));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(RelabelStep::Post(RelabelPost::Plain(kind), result));
                        for c in children.into_iter().rev() {
                            steps.push(RelabelStep::Enter(c, false));
                        }
                    }
                    // A leaf is left unchanged by the descent, and the node's
                    // own rewrite still runs on it (`church_true` → `[]`).
                    Err(leaf) => done.push(fold_here(leaf, ctx, result)),
                },
            },
            RelabelStep::Post(post, result) => {
                let rebuilt = match post {
                    RelabelPost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    RelabelPost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    RelabelPost::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let total = 1 + clause_meta
                            .iter()
                            .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                            .sum::<usize>();
                        let mut parts = take(&mut done, total).into_iter();
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
                    RelabelPost::Trace { message } => PseudoExpr::Trace {
                        message,
                        value: PBox::new(done.pop().expect("trace value")),
                    },
                    RelabelPost::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(fold_here(rebuilt, ctx, result));
            }
        }
    }

    done.pop().expect("relabel leaves exactly one result")
}

/// One pending step of [`relabel`]'s explicit stack. The `bool` is the
/// result-position flag for that node.
enum RelabelStep {
    Enter(PseudoExpr, bool),
    Post(RelabelPost, bool),
}

/// Everything about a node that is NOT one of the child expressions being
/// rewritten.
enum RelabelPost {
    Let {
        name: String,
        id: Option<VarId>,
    },
    Lambda {
        params: Vec<Binder>,
    },
    When {
        subject_name: Option<Binder>,
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    /// A `Trace`'s message is never descended into, so it rides along here
    /// rather than through the child stack.
    Trace {
        message: PBox,
    },
    Plain(PlainPost),
}

/// The node's own rewrite, run once its children are rebuilt.
fn fold_here(expr: PseudoExpr, ctx: &Ctx, result: bool) -> PseudoExpr {
    match &expr {
        // The cons cell: `[head, ..self(tail)]`.
        PseudoExpr::Constr { .. } if cons_cell_recursing_on(&expr, ctx).is_some() => {
            let PseudoExpr::Constr { fields, .. } = expr else {
                unreachable!("matched Constr above");
            };
            let mut fields = fields.into_iter();
            let head = fields.next().expect("cons cell has two fields");
            let tail = fields.next().expect("cons cell has two fields");
            PseudoExpr::List {
                elements: vec![head].into(),
                tail: Some(PBox::new(tail)),
            }
        }
        // The cons cell written as a Scott-cons CALL.
        PseudoExpr::Apply { .. } if scott_cons_recursing_on(&expr, ctx).is_some() => {
            let PseudoExpr::Apply { args, .. } = expr else {
                unreachable!("matched Apply above");
            };
            let mut args = args.into_iter();
            let head = args.next().expect("scott cons has two args");
            let tail = args.next().expect("scott cons has two args");
            PseudoExpr::List {
                elements: vec![head].into(),
                tail: Some(PBox::new(tail)),
            }
        }
        // The base case the recursion bottoms out in.
        PseudoExpr::Constr {
            tag: 0,
            fields,
            shape,
            ..
        } if result && fields.is_empty() && is_nullary_stub_or_nil(shape) => PseudoExpr::List {
            elements: PVec::new(),
            tail: None,
        },
        // The same base case written as the Scott nil. `fn(t, _) { t }`
        // is the church `True` AND the Scott `nil`, and the naming
        // picked `church_true`; inside a proven list builder the
        // result position can only be the empty list.
        PseudoExpr::Var { id: Some(v), .. } if result && ctx.nils.contains(v) => PseudoExpr::List {
            elements: PVec::new(),
            tail: None,
        },
        _ => expr,
    }
}

/// Whether `expr` contains the recognised cons cell anywhere.
fn contains_cons_cell(expr: &PseudoExpr, ctx: &Ctx) -> bool {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        if cons_cell_recursing_on(expr, ctx).is_some()
            || scott_cons_recursing_on(expr, ctx).is_some()
            || spread_recursing_on(expr, ctx)
        {
            return true;
        }
        for c in children(expr).into_iter().rev() {
            stack.push(c);
        }
    }
    false
}

/// A tag-1 arity-2 constructor — the recovered `Known(Cons)` or the stub
/// the Data encoding leaves behind.
fn is_cons_shape(shape: &ConstructorShape) -> bool {
    matches!(
        shape,
        ConstructorShape::Known(KnownConstructor::Cons)
            | ConstructorShape::Unknown {
                tag: 1,
                arity: 2,
                ..
            }
    )
}

/// A nullary tag-0 constructor: the recovered `Known(Nil)`, or the stub
/// that shares its shape. Inside a proven builder the stub is the nil —
/// that is exactly what the sibling pass could not conclude on its own.
fn is_nullary_stub_or_nil(shape: &ConstructorShape) -> bool {
    matches!(
        shape,
        ConstructorShape::Known(KnownConstructor::Nil)
            | ConstructorShape::Unknown {
                tag: 0,
                arity: 0,
                ..
            }
    )
}

/// Look through the `force` wrapper the lowering leaves on a recursive
/// callee.
fn strip_force(expr: &PseudoExpr) -> &PseudoExpr {
    let mut current = expr;
    while let PseudoExpr::Force(inner) = current {
        current = inner.as_ref();
    }
    current
}

#[cfg(test)]
mod tests;
