//! Mid-level IR between UPLC and PseudoExpr.
//!
//! MidExpr preserves UPLC evaluation semantics (thunks, force, closures)
//! while providing a structured representation suitable for analysis and
//! pre-computation. Every node carries an ID for provenance tracking.

use num_bigint::BigInt;
use uplc::builtins::DefaultFunction;

use super::super::pbox::{Nested, Owned, OwnedVec};
use super::super::var_id::VarId;
use super::expr_id::MidExprId;

/// A boxed child expression with an iterative destructor.
pub(crate) type MBox = Owned<MidExpr>;
/// A list of child expressions with an iterative destructor.
pub(crate) type MVec = OwnedVec<MidExpr>;

/// Mid-level expression preserving UPLC semantics with analysis annotations.
///
/// `Clone` is a heap walk — see the `impl` below — and the children sit in
/// [`MBox`] / [`MVec`], whose destructors are heap walks too: nesting depth is
/// script-controlled, so neither may take a call frame per level.
#[derive(Debug)]
pub(crate) enum MidExpr {
    /// Literal constant value.
    Lit { id: MidExprId, value: MidLiteral },

    /// Variable reference.
    Var { id: MidExprId, var: VarId },

    /// Thunk: suspended computation (UPLC Delay).
    /// The body is NOT evaluated until forced.
    Thunk {
        id: MidExprId,
        body: MBox,
        /// If true, this thunk wraps a value-form (Lambda, Lit, Constr)
        /// and can be stripped during lowering without changing semantics.
        cosmetic: bool,
    },

    /// Force evaluation of a thunk (UPLC Force).
    Force {
        id: MidExprId,
        body: MBox,
        /// If the inner is known to be a thunk, the resolved
        /// expression. Set during the pre-computation pass.
        resolved: Option<MBox>,
    },

    /// Closure (UPLC Lambda). Captures lexical environment.
    Closure {
        id: MidExprId,
        params: Vec<VarId>,
        body: MBox,
        /// If this is a recursive function (Y-combinator), the self-reference VarId.
        recursive: Option<VarId>,
    },

    /// Function application (UPLC Apply).
    Apply {
        id: MidExprId,
        function: MBox,
        args: MVec,
    },

    /// Let binding (reconstructed from Apply(Lambda, value)).
    Let {
        id: MidExprId,
        var: VarId,
        value: MBox,
        body: MBox,
        /// Number of references to this variable (filled during analysis).
        use_count: u32,
    },

    /// Builtin function, possibly partially applied.
    Builtin {
        id: MidExprId,
        fun: DefaultFunction,
        /// Number of Force operations consumed (for polymorphic builtins).
        forces: u8,
        /// Arguments accumulated so far.
        args: MVec,
        /// If all args are constants, the pre-computed result.
        folded: Option<MidLiteral>,
    },

    /// Constructor application (Plutus V3 Constr or Scott-encoded).
    Constr {
        id: MidExprId,
        tag: usize,
        fields: MVec,
    },

    /// Pattern match / case analysis.
    Case {
        id: MidExprId,
        scrutinee: MBox,
        branches: Vec<MidBranch>,
        /// How this case was encoded in UPLC.
        encoding: CaseEncoding,
    },

    /// Conditional (from IfThenElse builtin).
    If {
        id: MidExprId,
        condition: MBox,
        then_branch: MBox,
        else_branch: MBox,
    },

    /// Error / fail.
    Error { id: MidExprId },

    /// Trace (debug logging).
    Trace {
        id: MidExprId,
        message: MBox,
        body: MBox,
    },

    /// Plutus Data literal.
    Data {
        id: MidExprId,
        data: Box<uplc::PlutusData>,
    },
}

/// Branch in a case expression.
#[derive(Debug, Clone)]
pub(crate) struct MidBranch {
    /// Constructor tag this branch matches.
    pub tag: usize,
    /// Variables bound to constructor fields in this branch.
    pub binders: Vec<VarId>,
    /// Branch body.
    pub body: MidExpr,
}

/// Releases the body without recursing: a body's own `case` holds more
/// branches, as many levels deep as the script nests them.
impl Drop for MidBranch {
    fn drop(&mut self) {
        let hole = MidExpr::Error { id: self.body.id() };
        drop_iteratively(std::mem::replace(&mut self.body, hole));
    }
}

/// Hands the containers this node's children so they can release a tree
/// without recursing. Order matches [`MidExpr::children`].
impl Nested for MidExpr {
    fn take_children(&mut self) -> Vec<MidExpr> {
        MidExpr::take_children(self)
    }
}

/// How a case/match was encoded in UPLC.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CaseEncoding {
    /// Plutus V3 native Constr/Case terms.
    Native,
    /// Scott encoding: force(force(scrutinee)(branch0)(branch1)...).
    Scott,
    /// IfThenElse-based: if(tag == N, branchN, ...).
    IfChain,
    /// ChooseList-based: chooseList(list, empty, nonempty).
    ChooseList,
    /// Native `case` whose scrutinee is proven to be a builtin list: branch 0
    /// is `cons(head, tail)`, branch 1 is `nil`.
    BuiltinList,
}

/// Literal values (subset of UPLC Constants).
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum MidLiteral {
    Integer(BigInt),
    ByteString(Vec<u8>),
    String(String),
    Bool(bool),
    Unit,
    Data(Box<uplc::PlutusData>),
    List(Vec<MidLiteral>),
    Pair(Box<MidLiteral>, Box<MidLiteral>),
    /// BLS elements stored as compressed bytes (opaque).
    Bls12_381G1(Vec<u8>),
    Bls12_381G2(Vec<u8>),
}

// ===== MidExpr accessors =====

impl MidExpr {
    pub(crate) fn id(&self) -> MidExprId {
        match self {
            MidExpr::Lit { id, .. }
            | MidExpr::Var { id, .. }
            | MidExpr::Thunk { id, .. }
            | MidExpr::Force { id, .. }
            | MidExpr::Closure { id, .. }
            | MidExpr::Apply { id, .. }
            | MidExpr::Let { id, .. }
            | MidExpr::Builtin { id, .. }
            | MidExpr::Constr { id, .. }
            | MidExpr::Case { id, .. }
            | MidExpr::If { id, .. }
            | MidExpr::Error { id }
            | MidExpr::Trace { id, .. }
            | MidExpr::Data { id, .. } => *id,
        }
    }

    /// Replace this node's id, whatever variant it is.
    pub(crate) fn set_id(&mut self, new_id: MidExprId) {
        match self {
            MidExpr::Lit { id, .. }
            | MidExpr::Var { id, .. }
            | MidExpr::Thunk { id, .. }
            | MidExpr::Force { id, .. }
            | MidExpr::Closure { id, .. }
            | MidExpr::Apply { id, .. }
            | MidExpr::Let { id, .. }
            | MidExpr::Builtin { id, .. }
            | MidExpr::Constr { id, .. }
            | MidExpr::Case { id, .. }
            | MidExpr::If { id, .. }
            | MidExpr::Error { id }
            | MidExpr::Trace { id, .. }
            | MidExpr::Data { id, .. } => *id = new_id,
        }
    }

    pub(crate) fn children(&self) -> Vec<&MidExpr> {
        match self {
            MidExpr::Lit { .. }
            | MidExpr::Var { .. }
            | MidExpr::Error { .. }
            | MidExpr::Data { .. } => vec![],
            MidExpr::Thunk { body, .. } => vec![body],
            MidExpr::Force { body, resolved, .. } => {
                let mut c = vec![body.as_ref()];
                if let Some(r) = resolved {
                    c.push(r.as_ref());
                }
                c
            }
            MidExpr::Closure { body, .. } => vec![body],
            MidExpr::Apply { function, args, .. } => {
                let mut c = vec![function.as_ref()];
                c.extend(args.iter());
                c
            }
            MidExpr::Let { value, body, .. } => vec![value, body],
            MidExpr::Builtin { args, .. } => args.iter().collect(),
            MidExpr::Constr { fields, .. } => fields.iter().collect(),
            MidExpr::Case {
                scrutinee,
                branches,
                ..
            } => {
                let mut c = vec![scrutinee.as_ref()];
                for b in branches {
                    c.push(&b.body);
                }
                c
            }
            MidExpr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                vec![condition, then_branch, else_branch]
            }
            MidExpr::Trace { message, body, .. } => vec![message, body],
        }
    }

    /// The `&mut` twin of [`Self::children`]. Kept adjacent to it so the two
    /// arm lists are edited together — a walk that uses one and a walk that
    /// uses the other must agree on what a node's children are.
    pub(crate) fn children_mut(&mut self) -> Vec<&mut MidExpr> {
        match self {
            MidExpr::Lit { .. }
            | MidExpr::Var { .. }
            | MidExpr::Error { .. }
            | MidExpr::Data { .. } => vec![],
            MidExpr::Thunk { body, .. } => vec![body],
            MidExpr::Force { body, resolved, .. } => {
                let mut c = vec![body.as_mut()];
                if let Some(r) = resolved {
                    c.push(r.as_mut());
                }
                c
            }
            MidExpr::Closure { body, .. } => vec![body],
            MidExpr::Apply { function, args, .. } => {
                let mut c = vec![function.as_mut()];
                c.extend(args.iter_mut());
                c
            }
            MidExpr::Let { value, body, .. } => vec![value, body],
            MidExpr::Builtin { args, .. } => args.iter_mut().collect(),
            MidExpr::Constr { fields, .. } => fields.iter_mut().collect(),
            MidExpr::Case {
                scrutinee,
                branches,
                ..
            } => {
                let mut c = vec![scrutinee.as_mut()];
                for b in branches {
                    c.push(&mut b.body);
                }
                c
            }
            MidExpr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                vec![condition, then_branch, else_branch]
            }
            MidExpr::Trace { message, body, .. } => vec![message, body],
        }
    }

    /// Move every child OUT of this node, leaving cheap placeholders behind.
    ///
    /// The node stays structurally valid (same variant, same arity) so it can
    /// be reassembled with [`Self::put_children`] once the children have been
    /// rewritten. This is what lets a bottom-up rewrite run on an explicit
    /// stack: a `&mut` walk cannot hold a node while its children are borrowed
    /// out of it, but an OWNED one has no such conflict.
    ///
    /// Yields the children in the same order as [`Self::children`].
    pub(crate) fn take_children(&mut self) -> Vec<MidExpr> {
        let hole_id = self.id();
        let mut out = Vec::new();
        let mut take =
            |slot: &mut MidExpr| out.push(std::mem::replace(slot, MidExpr::Error { id: hole_id }));
        match self {
            MidExpr::Lit { .. }
            | MidExpr::Var { .. }
            | MidExpr::Error { .. }
            | MidExpr::Data { .. } => {}
            MidExpr::Thunk { body, .. } => take(body),
            MidExpr::Force { body, resolved, .. } => {
                take(body);
                if let Some(r) = resolved {
                    take(r);
                }
            }
            MidExpr::Closure { body, .. } => take(body),
            MidExpr::Apply { function, args, .. } => {
                take(function);
                args.iter_mut().for_each(&mut take);
            }
            MidExpr::Let { value, body, .. } => {
                take(value);
                take(body);
            }
            MidExpr::Builtin { args, .. } => args.iter_mut().for_each(&mut take),
            MidExpr::Constr { fields, .. } => fields.iter_mut().for_each(&mut take),
            MidExpr::Case {
                scrutinee,
                branches,
                ..
            } => {
                take(scrutinee);
                branches.iter_mut().for_each(|b| take(&mut b.body));
            }
            MidExpr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                take(condition);
                take(then_branch);
                take(else_branch);
            }
            MidExpr::Trace { message, body, .. } => {
                take(message);
                take(body);
            }
        }
        out
    }

    /// Put children back into the placeholders [`Self::take_children`] left.
    ///
    /// # Panics
    /// If `kids` is not exactly what `take_children` yielded for this node —
    /// that would mean the two arm lists have drifted apart.
    pub(crate) fn put_children(&mut self, kids: Vec<MidExpr>) {
        let expected = kids.len();
        let mut kids = kids.into_iter();
        for slot in self.children_mut() {
            *slot = kids.next().expect("put_children: too few children");
        }
        assert!(
            kids.next().is_none(),
            "put_children: {expected} children did not fit the node",
        );
    }

    /// Rebuild this node around already-cloned children, given in
    /// [`Self::children`]'s order. Fields that hold no `MidExpr` are copied.
    fn clone_with_children(&self, children: impl Iterator<Item = MidExpr>) -> MidExpr {
        let mut children = children;
        let mut next = || children.next().expect("clone_with_children: missing child");
        match self {
            MidExpr::Lit { id, value } => MidExpr::Lit {
                id: *id,
                value: value.clone(),
            },
            MidExpr::Var { id, var } => MidExpr::Var { id: *id, var: *var },
            MidExpr::Thunk { id, cosmetic, .. } => MidExpr::Thunk {
                id: *id,
                body: MBox::new(next()),
                cosmetic: *cosmetic,
            },
            MidExpr::Force { id, resolved, .. } => {
                let body = MBox::new(next());
                MidExpr::Force {
                    id: *id,
                    body,
                    resolved: resolved.as_ref().map(|_| MBox::new(next())),
                }
            }
            MidExpr::Closure {
                id,
                params,
                recursive,
                ..
            } => MidExpr::Closure {
                id: *id,
                params: params.clone(),
                body: MBox::new(next()),
                recursive: *recursive,
            },
            MidExpr::Apply { id, args, .. } => {
                let function = MBox::new(next());
                MidExpr::Apply {
                    id: *id,
                    function,
                    args: (0..args.len()).map(|_| next()).collect(),
                }
            }
            MidExpr::Let {
                id, var, use_count, ..
            } => {
                let value = MBox::new(next());
                MidExpr::Let {
                    id: *id,
                    var: *var,
                    value,
                    body: MBox::new(next()),
                    use_count: *use_count,
                }
            }
            MidExpr::Builtin {
                id,
                fun,
                forces,
                args,
                folded,
            } => MidExpr::Builtin {
                id: *id,
                fun: *fun,
                forces: *forces,
                args: (0..args.len()).map(|_| next()).collect(),
                folded: folded.clone(),
            },
            MidExpr::Constr { id, tag, fields } => MidExpr::Constr {
                id: *id,
                tag: *tag,
                fields: (0..fields.len()).map(|_| next()).collect(),
            },
            MidExpr::Case {
                id,
                branches,
                encoding,
                ..
            } => {
                let scrutinee = MBox::new(next());
                MidExpr::Case {
                    id: *id,
                    scrutinee,
                    branches: branches
                        .iter()
                        .map(|branch| MidBranch {
                            tag: branch.tag,
                            binders: branch.binders.clone(),
                            body: next(),
                        })
                        .collect(),
                    encoding: *encoding,
                }
            }
            MidExpr::If { id, .. } => {
                let condition = MBox::new(next());
                let then_branch = MBox::new(next());
                MidExpr::If {
                    id: *id,
                    condition,
                    then_branch,
                    else_branch: MBox::new(next()),
                }
            }
            MidExpr::Error { id } => MidExpr::Error { id: *id },
            MidExpr::Trace { id, .. } => {
                let message = MBox::new(next());
                MidExpr::Trace {
                    id: *id,
                    message,
                    body: MBox::new(next()),
                }
            }
            MidExpr::Data { id, data } => MidExpr::Data {
                id: *id,
                data: data.clone(),
            },
        }
    }

    /// Iterative: this is called on whole programs, whose depth a script
    /// controls.
    pub(crate) fn node_count(&self) -> usize {
        let mut n = 0usize;
        let mut pending: Vec<&MidExpr> = vec![self];
        while let Some(current) = pending.pop() {
            n += 1;
            pending.extend(current.children());
        }
        n
    }
}

/// Deep clone on a heap stack.
///
/// Nesting depth is script-controlled, and on `wasm32` the engine's call
/// stack cannot be grown to match. Do not replace this with `#[derive(Clone)]`.
impl Clone for MidExpr {
    fn clone(&self) -> Self {
        enum Step<'a> {
            /// Clone this node's children first.
            Visit(&'a MidExpr),
            /// Rebuild this node from the `usize` children on `done`.
            Build(&'a MidExpr, usize),
        }

        let mut steps = vec![Step::Visit(self)];
        let mut done: Vec<MidExpr> = Vec::new();
        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(node) => {
                    let children = node.children();
                    steps.push(Step::Build(node, children.len()));
                    // Reversed so they pop — and so land on `done` — in order.
                    steps.extend(children.into_iter().rev().map(Step::Visit));
                }
                Step::Build(node, count) => {
                    let start = done.len() - count;
                    let rebuilt = node.clone_with_children(done.drain(start..));
                    done.push(rebuilt);
                }
            }
        }
        done.pop().expect("clone leaves exactly one result")
    }
}

#[cfg(test)]
mod tests;

/// Release a tree without recursing into it.
///
/// This is a free function rather than a `Drop` impl because `MidExpr` is
/// destructured by value throughout `decompile::mid`, and a type that
/// implements `Drop` cannot be moved out of (E0509).
///
/// Each node is emptied before it goes out of scope, so the implicit drop only
/// ever frees a childless node and never re-enters.
pub(crate) fn drop_iteratively(mut expr: MidExpr) {
    let mut stack = expr.take_children();
    while let Some(mut child) = stack.pop() {
        stack.append(&mut child.take_children());
    }
}
