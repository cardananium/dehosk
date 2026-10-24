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
///
/// `Clone`, `PartialEq`, `Debug` and `Drop` are heap walks — see the `impl`s
/// below. A list or pair constant nests as deep as the script makes it, so
/// none of them may recurse; do not derive any of them back.
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

impl MidLiteral {
    /// This literal's direct sub-literals, in order.
    fn child_refs_into<'a>(&'a self, out: &mut Vec<&'a MidLiteral>) {
        match self {
            MidLiteral::List(items) => out.extend(items),
            MidLiteral::Pair(first, second) => {
                out.push(first);
                out.push(second);
            }
            _ => {}
        }
    }

    /// Move the sub-literals out, in [`Self::child_refs_into`]'s order,
    /// leaving this node childless.
    fn take_children(&mut self) -> Vec<MidLiteral> {
        match self {
            MidLiteral::List(items) => std::mem::take(items),
            MidLiteral::Pair(first, second) => vec![
                std::mem::replace(first.as_mut(), MidLiteral::Unit),
                std::mem::replace(second.as_mut(), MidLiteral::Unit),
            ],
            _ => Vec::new(),
        }
    }

    /// A copy of this node alone; `None` for a list or pair, whose copy is
    /// assembled from its children's.
    fn clone_leaf(&self) -> Option<MidLiteral> {
        Some(match self {
            MidLiteral::Integer(n) => MidLiteral::Integer(n.clone()),
            MidLiteral::ByteString(bytes) => MidLiteral::ByteString(bytes.clone()),
            MidLiteral::String(text) => MidLiteral::String(text.clone()),
            MidLiteral::Bool(b) => MidLiteral::Bool(*b),
            MidLiteral::Unit => MidLiteral::Unit,
            MidLiteral::Data(data) => MidLiteral::Data(data.clone()),
            MidLiteral::Bls12_381G1(bytes) => MidLiteral::Bls12_381G1(bytes.clone()),
            MidLiteral::Bls12_381G2(bytes) => MidLiteral::Bls12_381G2(bytes.clone()),
            MidLiteral::List(_) | MidLiteral::Pair(..) => return None,
        })
    }
}

impl Clone for MidLiteral {
    fn clone(&self) -> Self {
        enum Step<'a> {
            Visit(&'a MidLiteral),
            /// Rebuild this list or pair from the `usize` clones on `done`.
            Build(&'a MidLiteral, usize),
        }

        let mut steps = vec![Step::Visit(self)];
        let mut done: Vec<MidLiteral> = Vec::new();
        let mut children: Vec<&MidLiteral> = Vec::new();
        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(node) => match node.clone_leaf() {
                    Some(leaf) => done.push(leaf),
                    None => {
                        children.clear();
                        node.child_refs_into(&mut children);
                        steps.push(Step::Build(node, children.len()));
                        // Reversed so they pop — and so land on `done` — in order.
                        steps.extend(children.iter().rev().map(|child| Step::Visit(child)));
                    }
                },
                Step::Build(node, count) => {
                    let mut cloned = done.split_off(done.len() - count);
                    done.push(match node {
                        MidLiteral::List(_) => MidLiteral::List(cloned),
                        MidLiteral::Pair(..) => {
                            let second = cloned.pop().expect("pair second");
                            let first = cloned.pop().expect("pair first");
                            MidLiteral::Pair(Box::new(first), Box::new(second))
                        }
                        _ => unreachable!("leaves are cloned on visit"),
                    });
                }
            }
        }
        done.pop().expect("clone leaves exactly one result")
    }
}

impl PartialEq for MidLiteral {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = vec![(self, other)];
        while let Some(pair) = pending.pop() {
            let same = match pair {
                (MidLiteral::Integer(a), MidLiteral::Integer(b)) => a == b,
                (MidLiteral::ByteString(a), MidLiteral::ByteString(b))
                | (MidLiteral::Bls12_381G1(a), MidLiteral::Bls12_381G1(b))
                | (MidLiteral::Bls12_381G2(a), MidLiteral::Bls12_381G2(b)) => a == b,
                (MidLiteral::String(a), MidLiteral::String(b)) => a == b,
                (MidLiteral::Bool(a), MidLiteral::Bool(b)) => a == b,
                (MidLiteral::Unit, MidLiteral::Unit) => true,
                (MidLiteral::Data(a), MidLiteral::Data(b)) => a == b,
                (MidLiteral::List(a), MidLiteral::List(b)) => {
                    pending.extend(a.iter().zip(b));
                    a.len() == b.len()
                }
                (MidLiteral::Pair(first_a, second_a), MidLiteral::Pair(first_b, second_b)) => {
                    pending.push((second_a, second_b));
                    pending.push((first_a, first_b));
                    true
                }
                _ => false,
            };
            if !same {
                return false;
            }
        }
        true
    }
}

impl crate::pseudo::debug_walk::DebugLayers for MidLiteral {
    fn layer<'a>(&'a self, out: &mut crate::pseudo::debug_walk::Layer<'a, Self>) {
        use crate::pseudo::debug_walk::Field;
        match self {
            MidLiteral::Integer(n) => out.tuple("Integer", &[Field::Leaf(n)]),
            MidLiteral::ByteString(bytes) => out.tuple("ByteString", &[Field::Leaf(bytes)]),
            MidLiteral::String(text) => out.tuple("String", &[Field::Leaf(text)]),
            MidLiteral::Bool(b) => out.tuple("Bool", &[Field::Leaf(b)]),
            MidLiteral::Unit => out.unit("Unit"),
            MidLiteral::Data(data) => out.tuple("Data", &[Field::Leaf(data)]),
            MidLiteral::List(items) => out.tuple("List", &[Field::Nodes(items)]),
            MidLiteral::Pair(first, second) => {
                out.tuple("Pair", &[Field::Node(first), Field::Node(second)])
            }
            MidLiteral::Bls12_381G1(bytes) => out.tuple("Bls12_381G1", &[Field::Leaf(bytes)]),
            MidLiteral::Bls12_381G2(bytes) => out.tuple("Bls12_381G2", &[Field::Leaf(bytes)]),
        }
    }
}

impl std::fmt::Debug for MidLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        crate::pseudo::debug_walk::write(self, f)
    }
}

/// Releases the literal without recursing: each node is emptied before it
/// goes out of scope, so the implicit drop at the end of the loop body only
/// ever frees a childless node.
impl Drop for MidLiteral {
    fn drop(&mut self) {
        let mut pending = self.take_children();
        while let Some(mut node) = pending.pop() {
            pending.append(&mut node.take_children());
        }
    }
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
