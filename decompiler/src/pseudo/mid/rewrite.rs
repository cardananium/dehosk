//! Iterative, owned bottom-up rewriting of a `MidExpr` tree.
//!
//! Lives here rather than beside the passes that use it because it is an
//! algorithm over `MidExpr`, and `pseudo` may not depend on `decompile`.

use super::expr::MidExpr;

/// Rewrite every node bottom-up, iteratively: `rewrite` sees a node only after
/// all of its children have already been rewritten.
///
/// This exists because the `&mut` form of a bottom-up walk cannot be
/// expressed in safe Rust. To act on a node AFTER its children, you must
/// still hold `&mut node` while the children — borrowed out of that same node —
/// are being processed, and no safe reference can express that. Ownership
/// dissolves the conflict: [`MidExpr::take_children`] moves the children out
/// and leaves placeholders, so nothing is aliased, and
/// [`MidExpr::put_children`] reassembles the node once they come back.
pub(crate) fn rewrite_bottom_up(
    root: MidExpr,
    rewrite: &mut impl FnMut(MidExpr) -> MidExpr,
) -> MidExpr {
    rewrite_bottom_up_selective(root, &mut |_| Descend::All, rewrite)
}

/// Which of a node's children a bottom-up rewrite should descend into.
///
/// Indices are positions in [`MidExpr::children`] — `Let` is `[value, body]`,
/// `Case` is `[scrutinee, arm0, arm1, …]`, and so on.
pub(crate) enum Descend {
    /// Every child.
    All,
    /// No child: the node is handed to `rewrite` with its subtrees untouched.
    None,
    /// Only these child positions, ascending. The rest pass through unchanged.
    Only(Vec<usize>),
}

/// [`rewrite_bottom_up`], but the caller chooses per node which children to
/// descend into.
///
/// This is what a shadowing-aware rewrite needs: substituting a variable must
/// walk a `let`'s VALUE but stop at its body when the binder shadows the
/// target, and must not enter a `case` arm that rebinds it. Expressing that as
/// data — a [`Descend`] per node — keeps the descent inside the machine.
pub(crate) fn rewrite_bottom_up_selective(
    root: MidExpr,
    plan: &mut impl FnMut(&MidExpr) -> Descend,
    rewrite: &mut impl FnMut(MidExpr) -> MidExpr,
) -> MidExpr {
    rewrite_bottom_up_fixpoint(root, plan, &mut |node| Rewritten::Done(rewrite(node)))
}

/// What a rewrite did to a node.
pub(crate) enum Rewritten {
    /// Finished: the node goes up to its parent as it stands.
    Done(MidExpr),
    /// Rewritten into a DIFFERENT shape that has to be walked in turn — its
    /// children re-processed, then offered to `rewrite` again.
    ///
    /// Termination is the caller's to argue: the rewrite must make progress,
    /// or the machine loops.
    Again(MidExpr),
}

/// [`rewrite_bottom_up_selective`], with a rewrite that may hand a node back
/// for another pass.
///
/// This is the shape of a rewrite that BUILDS structure: folding
/// `Apply(Closure(p, body), arg)` into `Let(p = arg, body)` produces a `let`
/// that may itself be foldable, so the result re-enters rather than being
/// handed to the parent.
pub(crate) fn rewrite_bottom_up_fixpoint(
    root: MidExpr,
    plan: &mut impl FnMut(&MidExpr) -> Descend,
    rewrite: &mut impl FnMut(MidExpr) -> Rewritten,
) -> MidExpr {
    enum Task {
        /// Split this node apart and queue its children.
        Enter(MidExpr),
        /// A child that is NOT descended into: it moves to the value stack as
        /// it stands, keeping the positions its `Exit` will pop lined up.
        Pass(MidExpr),
        /// Children are done and sit on the value stack: put them back and
        /// hand the reassembled node to `rewrite`.
        Exit { shell: MidExpr, arity: usize },
    }

    let mut tasks = vec![Task::Enter(root)];
    let mut done: Vec<MidExpr> = Vec::new();

    while let Some(task) = tasks.pop() {
        match task {
            Task::Pass(node) => done.push(node),
            Task::Enter(mut node) => {
                let descend = plan(&node);
                let kids = node.take_children();
                tasks.push(Task::Exit {
                    shell: node,
                    arity: kids.len(),
                });
                // Reversed so the children pop — and therefore land on `done` —
                // in source order.
                for (i, kid) in kids.into_iter().enumerate().rev() {
                    let enter = match &descend {
                        Descend::All => true,
                        Descend::None => false,
                        Descend::Only(idxs) => idxs.contains(&i),
                    };
                    tasks.push(if enter {
                        Task::Enter(kid)
                    } else {
                        Task::Pass(kid)
                    });
                }
            }
            Task::Exit { mut shell, arity } => {
                let at = done.len() - arity;
                let kids = done.split_off(at);
                shell.put_children(kids);
                match rewrite(shell) {
                    Rewritten::Done(node) => done.push(node),
                    Rewritten::Again(node) => tasks.push(Task::Enter(node)),
                }
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "the rewrite machine must leave one result");
    done.pop().expect("rewrite result")
}
