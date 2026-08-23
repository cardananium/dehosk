use crate::pseudo::ast::PBox;
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;

use super::collectors::collect_local_generated_payload_binders;
use super::scope::binder_matches_var;

pub(in crate::decompile::late::normalize) struct PayloadRewriteCtx<'a> {
    pub subject_name: &'a str,
    pub subject_id: VarId,
    pub field_binders: &'a BTreeMap<usize, Binder>,
    pub generated_var_fields: &'a HashMap<VarId, usize>,
    pub condition_binder: Option<&'a Binder>,
    pub kind_annotations: &'a HashMap<VarId, VarKind>,
    pub use_varkind_recovery: bool,
}

/// Split a node into a SHELL — every immediate child replaced by a `Unit`
/// placeholder — plus those children in `map_children` order. The shell is
/// refilled by [`join_children`], which re-walks the same slots in the same
/// order, so the placeholders are never observed.
fn split_children(expr: PseudoExpr) -> (PseudoExpr, Vec<PseudoExpr>) {
    let mut kids: Vec<PseudoExpr> = Vec::new();
    let shell = crate::decompile::render_prep::scope_recurse::map_children(expr, |c| {
        kids.push(c);
        PseudoExpr::Unit
    });
    (shell, kids)
}

/// Put rewritten children back into a shell from [`split_children`].
fn join_children(shell: PseudoExpr, kids: Vec<PseudoExpr>) -> PseudoExpr {
    let mut kids = kids.into_iter();
    crate::decompile::render_prep::scope_recurse::map_children(shell, |_| {
        kids.next().expect("split_children left one child per slot")
    })
}

/// Takes the last `n` items off `done` — the children of the node being
/// reassembled, left there in source order by the walk.
fn take_done(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
    let at = done.len() - n;
    done.split_off(at)
}

/// A job on [`PayloadRewriteCtx::rewrite`]'s stack.
enum RwStep {
    Visit(PseudoExpr),
    Post(RwPost),
}

/// Work after children are rebuilt. `IndexAccess` and `If` inspect those
/// children before deciding what to build, so each is its own step.
enum RwPost {
    IndexAccess {
        index: usize,
    },
    If,
    /// A node with no post-decision: its `split_children` shell plus its
    /// child count.
    Plain(PseudoExpr, usize),
}

impl PayloadRewriteCtx<'_> {
    /// Children are pushed in REVERSE so they pop in source order and are
    /// popped off `done` in that same order when the node is rebuilt. That
    /// ordering is load-bearing: the `If` arm's fallback mints a binder id
    /// with `VarId::fresh_binding()` AFTER its three children are rewritten,
    /// so the mint sequence is post-order over `If` nodes.
    pub(in crate::decompile::late::normalize) fn rewrite(&self, expr: PseudoExpr) -> PseudoExpr {
        let mut steps: Vec<RwStep> = vec![RwStep::Visit(expr)];
        let mut done: Vec<PseudoExpr> = Vec::new();

        while let Some(step) = steps.pop() {
            match step {
                RwStep::Visit(expr) => match expr {
                    PseudoExpr::Var { name, id } => {
                        if let Some(id_val) = id
                            && let Some(index) = self.generated_var_fields.get(&id_val)
                            && let Some(binder) = self.field_binders.get(index)
                        {
                            done.push(PseudoExpr::Var {
                                name: binder.name.clone(),
                                id: Some(binder.id),
                            });
                            continue;
                        }
                        done.push(PseudoExpr::Var { name, id });
                    }
                    PseudoExpr::IndexAccess { collection, index } => {
                        steps.push(RwStep::Post(RwPost::IndexAccess { index }));
                        steps.push(RwStep::Visit(collection.into_inner()));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        steps.push(RwStep::Post(RwPost::If));
                        steps.push(RwStep::Visit(else_branch.into_inner()));
                        steps.push(RwStep::Visit(then_branch.into_inner()));
                        steps.push(RwStep::Visit(condition.into_inner()));
                    }
                    other => {
                        let (shell, kids) = split_children(other);
                        steps.push(RwStep::Post(RwPost::Plain(shell, kids.len())));
                        for kid in kids.into_iter().rev() {
                            steps.push(RwStep::Visit(kid));
                        }
                    }
                },
                RwStep::Post(post) => {
                    let rebuilt = match post {
                        RwPost::IndexAccess { index } => {
                            let rewritten_collection = done.pop().expect("index access collection");
                            if let PseudoExpr::FieldAccess {
                                record, selector, ..
                            } = &rewritten_collection
                                && selector.as_pretty_name() == "fields"
                                && let PseudoExpr::Var {
                                    name: record_name,
                                    id: Some(record_id),
                                    ..
                                } = record.as_ref()
                                && binder_matches_var(
                                    &Binder::new(self.subject_name.to_string(), self.subject_id),
                                    record_name,
                                    Some(*record_id),
                                )
                                && let Some(binder) = self.field_binders.get(&index)
                            {
                                done.push(PseudoExpr::var_with_id(binder.name.clone(), binder.id));
                                continue;
                            }
                            PseudoExpr::IndexAccess {
                                collection: PBox::new(rewritten_collection),
                                index,
                            }
                        }
                        RwPost::If => {
                            let else_branch = done.pop().expect("if else branch");
                            let then_branch = done.pop().expect("if then branch");
                            let condition_expr = done.pop().expect("if condition");

                            if self.condition_binder.is_some_and(|binder| {
                                matches!(
                                    &condition_expr,
                                    PseudoExpr::Var { name, id, .. } if name == &binder.name && *id == Some(binder.id)
                                )
                            }) {
                                let mut then_binders = Vec::new();
                                let mut else_binders = Vec::new();
                                collect_local_generated_payload_binders(
                                    &then_branch,
                                    &HashSet::new(),
                                    &mut then_binders,
                                    self.kind_annotations,
                                    self.use_varkind_recovery,
                                );
                                collect_local_generated_payload_binders(
                                    &else_branch,
                                    &HashSet::new(),
                                    &mut else_binders,
                                    self.kind_annotations,
                                    self.use_varkind_recovery,
                                );

                                if then_binders.len() == 1 && else_binders.len() == 1 {
                                    let then_binder = then_binders[0].clone();
                                    let else_binder = else_binders[0].clone();
                                    done.push(PseudoExpr::When {
                                        subject: PBox::new(condition_expr),
                                        subject_name: None,
                                        clauses: vec![
                                            crate::pseudo::ast::WhenClause {
                                                pattern: crate::pseudo::ast::WhenPattern::constructor(
                                                    ConstructorShape::unknown_data(1, 1),
                                                    vec![then_binder],
                                                ),
                                                guard: None,
                                                body: then_branch,
                                            },
                                            crate::pseudo::ast::WhenClause {
                                                pattern: crate::pseudo::ast::WhenPattern::constructor(
                                                    ConstructorShape::unknown_data(0, 1),
                                                    vec![else_binder],
                                                ),
                                                guard: None,
                                                body: else_branch,
                                            },
                                        ],
                                    });
                                    continue;
                                }

                                done.push(PseudoExpr::When {
                                    subject: PBox::new(condition_expr),
                                    subject_name: None,
                                    clauses: vec![
                                        crate::pseudo::ast::WhenClause {
                                            pattern: crate::pseudo::ast::WhenPattern::constructor(
                                                ConstructorShape::unknown_data(1, 1),
                                                vec![Binder::new("_", VarId::fresh_binding())],
                                            ),
                                            guard: None,
                                            body: then_branch,
                                        },
                                        crate::pseudo::ast::WhenClause {
                                            pattern: crate::pseudo::ast::WhenPattern::Wildcard,
                                            guard: None,
                                            body: else_branch,
                                        },
                                    ],
                                });
                                continue;
                            }

                            PseudoExpr::If {
                                condition: PBox::new(condition_expr),
                                then_branch: PBox::new(then_branch),
                                else_branch: PBox::new(else_branch),
                            }
                        }
                        RwPost::Plain(shell, n) => {
                            let kids = take_done(&mut done, n);
                            join_children(shell, kids)
                        }
                    };
                    done.push(rebuilt);
                }
            }
        }

        done.pop().expect("rewrite leaves exactly one result")
    }
}
