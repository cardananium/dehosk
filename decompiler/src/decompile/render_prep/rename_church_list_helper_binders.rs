//! Rename church-list-map rec-fn binders to readable names.
//!
//! Runs after `lift_list_fold_to_when` and
//! `cse_church_list_map_helpers`; the helpers they leave carry
//! synthesized names. The rec-fn name becomes `step`, its single
//! param `xs`.
//!
//! Display-only: VarIds and binder identities are untouched and refs
//! resolve by VarId, so the rename is observed only at the printer.
//! Fires only on RecFns matching the strict church-list-map shape.

use crate::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

pub(super) fn rename_church_list_helper_binders(expr: PseudoExpr) -> PseudoExpr {
    rewrite(expr)
}

/// One pending step of [`rewrite`]'s explicit stack — same shape as the
/// sibling render-prep passes in `scope_recurse` (`fold_identity_aliases`
/// in particular): this pass has no scope of its own to thread, so a step
/// carries no environment; only Let/Lambda/RecFn/When get their own arm,
/// everything else is a [`PlainPost`].
enum RewriteStep {
    Enter(PseudoExpr),
    Post(RewritePost),
}

enum RewritePost {
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
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(super::scope_recurse::PlainPost),
}

fn rewrite(expr: PseudoExpr) -> PseudoExpr {
    use super::scope_recurse::{plain_children, rebuild_plain, take};

    let mut steps: Vec<RewriteStep> = vec![RewriteStep::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RewriteStep::Enter(expr) => match expr {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(RewriteStep::Post(RewritePost::Let { name, id }));
                    steps.push(RewriteStep::Enter(body.into_inner()));
                    match value.into_inner() {
                        PseudoExpr::RecFn {
                            name: rec_name,
                            params,
                            body: rec_body,
                        } if is_church_list_map_shape(&rec_name, &params, &rec_body) => {
                            let mut rec_name = rec_name;
                            let mut params = params;
                            let arg_id = params[0].id;
                            let self_id = rec_name.id;
                            rec_name.set_display_name("step");
                            params[0].set_display_name("xs");
                            // Update Var refs to `arg_id`/`self_id` in body so
                            // the rendered output uses the new names too.
                            let renamed_body =
                                rename_var_refs(rec_body.into_inner(), arg_id, self_id);
                            steps.push(RewriteStep::Post(RewritePost::RecFn {
                                name: rec_name,
                                params,
                            }));
                            steps.push(RewriteStep::Enter(renamed_body));
                        }
                        other => steps.push(RewriteStep::Enter(other)),
                    }
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(RewriteStep::Post(RewritePost::Lambda { params }));
                    steps.push(RewriteStep::Enter(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(RewriteStep::Post(RewritePost::RecFn { name, params }));
                    steps.push(RewriteStep::Enter(body.into_inner()));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    let mut bodies_and_guards = Vec::with_capacity(clauses.len());
                    for c in clauses {
                        clause_meta.push((c.pattern, c.guard.is_some()));
                        bodies_and_guards.push((c.guard, c.body));
                    }
                    steps.push(RewriteStep::Post(RewritePost::When {
                        subject_name,
                        clause_meta,
                    }));
                    for (guard, body) in bodies_and_guards.into_iter().rev() {
                        steps.push(RewriteStep::Enter(body));
                        if let Some(g) = guard {
                            steps.push(RewriteStep::Enter(g));
                        }
                    }
                    steps.push(RewriteStep::Enter(subject.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(RewriteStep::Post(RewritePost::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(RewriteStep::Enter(c));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            RewriteStep::Post(post) => {
                let rebuilt = match post {
                    RewritePost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    RewritePost::Lambda { params } => {
                        let body = done.pop().expect("lambda body");
                        PseudoExpr::Lambda {
                            params,
                            body: PBox::new(body),
                        }
                    }
                    RewritePost::RecFn { name, params } => {
                        let body = done.pop().expect("recfn body");
                        PseudoExpr::RecFn {
                            name,
                            params,
                            body: PBox::new(body),
                        }
                    }
                    RewritePost::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let total: usize = 1 + clause_meta
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
                    RewritePost::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "the rewrite machine must leave one result");
    done.pop().expect("rewrite result")
}

/// Match `rec fn self(arg) { when arg is { [] -> _; [_, ..] ->
/// church_cons(F, self(arg[1..])) } }` — possibly with a let chain
/// inside the cons arm.
fn is_church_list_map_shape(name: &Binder, params: &[Binder], body: &PseudoExpr) -> bool {
    if params.len() != 1 {
        return false;
    }
    let arg_id = params[0].id;
    let self_id = name.id;

    let PseudoExpr::When {
        subject, clauses, ..
    } = body
    else {
        return false;
    };
    if !var_matches(subject, arg_id) {
        return false;
    }
    if clauses.len() != 2 {
        return false;
    }
    let (nil_idx, cons_idx) = match (
        is_nil_pattern(&clauses[0].pattern),
        is_nil_pattern(&clauses[1].pattern),
    ) {
        (true, false) => (0, 1),
        (false, true) => (1, 0),
        _ => return false,
    };
    let _ = nil_idx;
    let cons_arm = &clauses[cons_idx];
    // cons pattern: `[_, ..]` or Cons
    let cons_pattern_ok = matches!(
        &cons_arm.pattern,
        WhenPattern::List {
            elements,
            tail: Some(_),
        } if elements.len() == 1
    ) || matches!(
        &cons_arm.pattern,
        WhenPattern::Constructor {
            shape: ConstructorShape::Known(KnownConstructor::Cons),
            fields,
            ..
        } if fields.len() == 2
    );
    if !cons_pattern_ok {
        return false;
    }
    // peel let chain
    let mut cur = &cons_arm.body;
    while let PseudoExpr::Let { body, .. } = cur {
        cur = body;
    }
    let PseudoExpr::Apply { function, args } = cur else {
        return false;
    };
    let inner = strip_forces(function);
    let PseudoExpr::Var {
        name: cons_name, ..
    } = inner
    else {
        return false;
    };
    if cons_name != "church_cons" {
        return false;
    }
    if args.len() != 2 {
        return false;
    }
    // last arg must be self(arg[1..])
    let PseudoExpr::Apply {
        function: rfn,
        args: rargs,
    } = &args[1]
    else {
        return false;
    };
    if !var_matches(rfn, self_id) {
        return false;
    }
    rargs.len() == 1 && is_list_tail_of(&rargs[0], arg_id)
}

/// Walk `expr` rewriting any `Var { id: Some(arg_id) }` → name `xs`
/// and `Var { id: Some(self_id) }` → name `step`. Display-only.
fn rename_var_refs(expr: PseudoExpr, arg_id: VarId, self_id: VarId) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;

    struct VarRenamer {
        arg_id: VarId,
        self_id: VarId,
    }

    impl ExprFolder for VarRenamer {
        fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
            let new_name = match id {
                Some(v) if v == self.arg_id => "xs".to_string(),
                Some(v) if v == self.self_id => "step".to_string(),
                _ => name,
            };
            PseudoExpr::Var { name: new_name, id }
        }

        fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
            pattern
        }
    }

    VarRenamer { arg_id, self_id }.fold(expr)
}

fn var_matches(expr: &PseudoExpr, expected: VarId) -> bool {
    let inner = strip_forces(expr);
    matches!(inner, PseudoExpr::Var { id: Some(v), .. } if *v == expected)
}

fn strip_forces(expr: &PseudoExpr) -> &PseudoExpr {
    let mut cur = expr;
    while let PseudoExpr::Force(inner) = cur {
        cur = inner.as_ref();
    }
    cur
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

fn is_list_tail_of(expr: &PseudoExpr, arg_id: VarId) -> bool {
    match expr {
        PseudoExpr::BuiltinCall { name, args } if *name == BuiltinId::ListTail => {
            args.len() == 1 && var_matches(&args[0], arg_id)
        }
        PseudoExpr::Apply { function, args } => {
            matches!(
                function.as_ref(),
                PseudoExpr::BuiltinCall { name, args: a } if *name == BuiltinId::ListTail && a.is_empty()
            ) && args.len() == 1
                && var_matches(&args[0], arg_id)
        }
        _ => false,
    }
}
