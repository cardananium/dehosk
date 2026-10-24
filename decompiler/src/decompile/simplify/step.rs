//! Resumable simplification steps.
//!
//! A `simplify_*` helper that has to simplify sub-expressions before it can
//! finish does not call `self.simplify` on them: it returns a [`Step`] that
//! names them and says how to continue, and the fold machine simplifies them
//! on its own step stack before handing the results back. The nesting such a
//! helper descends through is the script's — tens of thousands of levels fit
//! in the size limit — and on `wasm32` the engine's call stack cannot grow to
//! match, so a nested `self.simplify` per level is not an option.

use super::Simplifier;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::walker::Entered;

/// A simplification, either finished or waiting for sub-expressions to be
/// simplified first.
pub(super) enum Step<T = PseudoExpr> {
    /// Finished.
    Done(T),
    /// Simplify these, in order, then continue with their results.
    Fold(Vec<PseudoExpr>, Then<T>),
}

/// How a [`Step::Fold`] continues once its expressions are simplified.
pub(super) type Then<T> = Box<dyn FnOnce(&mut Simplifier, Vec<PseudoExpr>) -> Step<T>>;

impl<T: 'static> Step<T> {
    /// Simplify `exprs`, in order, then continue with `then`.
    pub(super) fn fold_all(
        exprs: Vec<PseudoExpr>,
        then: impl FnOnce(&mut Simplifier, Vec<PseudoExpr>) -> Step<T> + 'static,
    ) -> Self {
        Step::Fold(exprs, Box::new(then))
    }

    /// Simplify `expr`, then continue with `then`.
    pub(super) fn fold(
        expr: PseudoExpr,
        then: impl FnOnce(&mut Simplifier, PseudoExpr) -> Step<T> + 'static,
    ) -> Self {
        Step::Fold(
            vec![expr],
            Box::new(move |simplifier, mut folded| {
                let expr = folded.pop().expect("one simplified expression");
                then(simplifier, expr)
            }),
        )
    }

    /// Continue with `then` once this step has its result — at once if it
    /// already has it.
    pub(super) fn then<U: 'static>(
        self,
        simplifier: &mut Simplifier,
        then: impl FnOnce(&mut Simplifier, T) -> Step<U> + 'static,
    ) -> Step<U> {
        match self {
            Step::Done(value) => then(simplifier, value),
            Step::Fold(exprs, first) => Step::Fold(
                exprs,
                Box::new(move |simplifier, folded| {
                    first(simplifier, folded).then(simplifier, then)
                }),
            ),
        }
    }

    /// [`Self::then`] for a continuation that needs nothing more simplified.
    pub(super) fn map<U: 'static>(
        self,
        simplifier: &mut Simplifier,
        f: impl FnOnce(T) -> U + 'static,
    ) -> Step<U> {
        self.then(simplifier, move |_, value| Step::Done(f(value)))
    }
}

impl Step {
    /// The result is `expr`, simplified — `self.simplify(expr)` in tail
    /// position.
    pub(super) fn refold(expr: PseudoExpr) -> Self {
        Step::Fold(
            vec![expr],
            Box::new(|_, mut folded| Step::Done(folded.pop().expect("one simplified expression"))),
        )
    }
}

impl Simplifier {
    /// Hand `step` to the fold machine: a finished result, or the
    /// expressions to simplify next with the continuation parked on
    /// `awaiting` until the machine resumes it.
    pub(super) fn suspend(&mut self, step: Step) -> Entered {
        match step {
            Step::Done(expr) => Entered::Done(expr),
            Step::Fold(exprs, then) => {
                self.awaiting.push(then);
                Entered::Await(exprs)
            }
        }
    }

    /// Continue the innermost suspended step with its simplified
    /// expressions.
    pub(super) fn resume_awaiting(&mut self, folded: Vec<PseudoExpr>) -> Entered {
        let then = self
            .awaiting
            .pop()
            .expect("a suspended simplification for every resume");
        let step = then(self, folded);
        self.suspend(step)
    }

    /// Run `step` to its result outside the fold machine, simplifying each
    /// expression it waits for through `Walker::fold` — so the suites can
    /// drive a single `simplify_*` helper.
    #[cfg(test)]
    pub(super) fn finish<T: 'static>(&mut self, mut step: Step<T>) -> T {
        use crate::pseudo::walker::Walker;
        loop {
            match step {
                Step::Done(value) => return value,
                Step::Fold(exprs, then) => {
                    let folded = exprs.into_iter().map(|expr| self.fold(expr)).collect();
                    step = then(self, folded);
                }
            }
        }
    }
}
