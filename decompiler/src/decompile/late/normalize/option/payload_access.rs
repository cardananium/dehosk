use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

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

/// A job on [`replace_subject_payload_access`]'s stack.
enum AccessStep {
    Visit(PseudoExpr),
    /// Rebuild a node from the `usize` children already on `done`, using its
    /// `split_children` shell.
    Post(PseudoExpr, usize),
}

/// `changed` is a `||` fold up the tree — every arm ORs its children's
/// flags and only the root's value is observed — so one accumulator over
/// the whole walk is the answer.
pub(in crate::decompile::late::normalize) fn replace_subject_payload_access(
    expr: PseudoExpr,
    target_id: Option<VarId>,
    binder: &Binder,
) -> (PseudoExpr, bool) {
    let mut steps: Vec<AccessStep> = vec![AccessStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();
    let mut changed = false;

    while let Some(step) = steps.pop() {
        match step {
            AccessStep::Visit(expr) => match expr {
                PseudoExpr::IndexAccess { collection, index } => {
                    if let PseudoExpr::FieldAccess {
                        record, selector, ..
                    } = collection.as_ref()
                        && selector.as_pretty_name() == "fields"
                        && let PseudoExpr::Var { id, .. } = record.as_ref()
                        && target_id.is_some()
                        && *id == target_id
                    {
                        changed = true;
                        if index == 0 {
                            done.push(PseudoExpr::var_with_id(binder.name.clone(), binder.id));
                            continue;
                        }

                        done.push(PseudoExpr::IndexAccess {
                            collection: PBox::new(PseudoExpr::var_with_id(
                                binder.name.clone(),
                                binder.id,
                            )),
                            index,
                        });
                        continue;
                    }

                    steps.push(AccessStep::Post(
                        PseudoExpr::IndexAccess {
                            collection: PBox::new(PseudoExpr::Unit),
                            index,
                        },
                        1,
                    ));
                    steps.push(AccessStep::Visit(collection.into_inner()));
                }
                other => {
                    let (shell, kids) = split_children(other);
                    steps.push(AccessStep::Post(shell, kids.len()));
                    for kid in kids.into_iter().rev() {
                        steps.push(AccessStep::Visit(kid));
                    }
                }
            },
            AccessStep::Post(shell, n) => {
                let kids = take_done(&mut done, n);
                done.push(join_children(shell, kids));
            }
        }
    }

    (
        done.pop()
            .expect("replace_subject_payload_access leaves exactly one result"),
        changed,
    )
}
