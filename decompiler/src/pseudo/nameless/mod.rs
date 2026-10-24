//! Nameless intermediate representation for the simplifier.
//!
//! `NamelessExpr` mirrors `PseudoExpr`, but variables carry only
//! `VarId`, never a `String` name. The dispatch information the
//! simplifier otherwise sniffs out of names lives in
//! [`VarTable`], keyed by `VarId`.
//!
//! The pipeline bridges through `PseudoExpr` before and after the
//! nameless segment.

use std::collections::HashMap;

use num_bigint::BigInt;

use super::ast::{BinaryOp, HelperIntrinsic, PseudoData, UnaryOp};
use super::constructor::ConstructorShape;
use super::field_selector::FieldSelector;
use super::pbox::{Nested, Owned, OwnedVec};
use super::var_id::VarId;
use crate::builtins::BuiltinId;

// =============================================================
// NamelessExpr
// =============================================================

/// A boxed child expression with an iterative destructor.
pub(crate) type NBox = Owned<NamelessExpr>;
/// A list of child expressions with an iterative destructor.
pub(crate) type NVec = OwnedVec<NamelessExpr>;

/// A `when`'s clauses, with an iterative destructor.
///
/// A clause holds its guard and body inline, so a plain
/// `Vec<NamelessClause>` destructor reaches the clauses of a `when` nested
/// in a body through that body — one frame per level, at a nesting depth
/// the script controls. Every clause expression goes to the containers'
/// worklist instead.
#[derive(Clone, Default)]
pub(crate) struct NClauses(Vec<NamelessClause>);

impl NClauses {
    /// Take the clauses out, consuming the container.
    pub(crate) fn into_vec(mut self) -> Vec<NamelessClause> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for NClauses {
    fn drop(&mut self) {
        let mut exprs: Vec<NamelessExpr> = Vec::new();
        for clause in self.0.iter_mut() {
            let NamelessClause {
                pattern,
                guard,
                body,
            } = clause;
            if let NamelessPattern::Literal(lit) = pattern {
                exprs.push(std::mem::replace(lit, NamelessExpr::Unit));
            }
            if let Some(guard) = guard {
                exprs.push(std::mem::replace(guard, NamelessExpr::Unit));
            }
            exprs.push(std::mem::replace(body, NamelessExpr::Unit));
        }
        drop(NVec::from(exprs));
    }
}

impl std::ops::Deref for NClauses {
    type Target = Vec<NamelessClause>;
    fn deref(&self) -> &Vec<NamelessClause> {
        &self.0
    }
}

impl std::ops::DerefMut for NClauses {
    fn deref_mut(&mut self) -> &mut Vec<NamelessClause> {
        &mut self.0
    }
}

impl From<Vec<NamelessClause>> for NClauses {
    fn from(clauses: Vec<NamelessClause>) -> Self {
        NClauses(clauses)
    }
}

impl FromIterator<NamelessClause> for NClauses {
    fn from_iter<I: IntoIterator<Item = NamelessClause>>(iter: I) -> Self {
        NClauses(iter.into_iter().collect())
    }
}

impl IntoIterator for NClauses {
    type Item = NamelessClause;
    type IntoIter = std::vec::IntoIter<NamelessClause>;
    fn into_iter(self) -> Self::IntoIter {
        self.into_vec().into_iter()
    }
}

impl<'a> IntoIterator for &'a NClauses {
    type Item = &'a NamelessClause;
    type IntoIter = std::slice::Iter<'a, NamelessClause>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a> IntoIterator for &'a mut NClauses {
    type Item = &'a mut NamelessClause;
    type IntoIter = std::slice::IterMut<'a, NamelessClause>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

impl std::fmt::Debug for NClauses {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// Hands the containers this node's children so they can release a tree
/// without recursing. Order matches [`NamelessExpr::child_refs_into`].
impl Nested for NamelessExpr {
    fn take_children(&mut self) -> Vec<NamelessExpr> {
        // A childless stand-in, so the emptied node drops shallowly.
        fn take(slot: &mut NamelessExpr) -> NamelessExpr {
            std::mem::replace(slot, NamelessExpr::Unit)
        }

        let mut out = Vec::new();
        match self {
            NamelessExpr::Lambda { body, .. } | NamelessExpr::RecFn { body, .. } => {
                out.push(take(body));
            }
            NamelessExpr::Apply { function, args } => {
                out.push(take(function));
                out.append(&mut args.take());
            }
            NamelessExpr::Let { value, body, .. } => {
                out.push(take(value));
                out.push(take(body));
            }
            NamelessExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                out.push(take(condition));
                out.push(take(then_branch));
                out.push(take(else_branch));
            }
            NamelessExpr::When {
                subject, clauses, ..
            } => {
                out.push(take(subject));
                for clause in clauses.iter_mut() {
                    if let NamelessPattern::Literal(lit) = &mut clause.pattern {
                        out.push(take(lit));
                    }
                    if let Some(guard) = clause.guard.as_mut() {
                        out.push(take(guard));
                    }
                    out.push(take(&mut clause.body));
                }
            }
            NamelessExpr::List { elements, tail } => {
                out.append(&mut elements.take());
                if let Some(tail) = tail.as_mut() {
                    out.push(take(tail));
                }
            }
            NamelessExpr::Tuple(items) => out.append(&mut items.take()),
            NamelessExpr::Pair(first, second) => {
                out.push(take(first));
                out.push(take(second));
            }
            NamelessExpr::Constr { fields, .. } => out.append(&mut fields.take()),
            NamelessExpr::FieldAccess { record, .. } => out.push(take(record)),
            NamelessExpr::IndexAccess { collection, .. } => out.push(take(collection)),
            NamelessExpr::BinOp { left, right, .. } => {
                out.push(take(left));
                out.push(take(right));
            }
            NamelessExpr::UnOp { operand, .. } => out.push(take(operand)),
            NamelessExpr::BuiltinCall { args, .. } => out.append(&mut args.take()),
            NamelessExpr::Delay(inner) | NamelessExpr::Force(inner) => out.push(take(inner)),
            NamelessExpr::Trace { message, value } => {
                out.push(take(message));
                out.push(take(value));
            }
            NamelessExpr::Int(_)
            | NamelessExpr::ByteArray(_)
            | NamelessExpr::String(_)
            | NamelessExpr::Bool(_)
            | NamelessExpr::Unit
            | NamelessExpr::Var(_)
            | NamelessExpr::Error { .. }
            | NamelessExpr::Raw { .. }
            | NamelessExpr::Data(_)
            | NamelessExpr::HelperSymbol(_) => {}
        }
        out
    }
}

/// Pseudo-IR with names erased from variable references.
///
/// Mirrors [`super::ast::PseudoExpr`] structurally, except that
/// [`NamelessExpr::Var`], every [`Binder`](super::ast::Binder)
/// position, and `When` subject names are bare [`VarId`].
/// Patterns mirror this.
///
/// Build through the converters in this module
/// (`pseudo_to_nameless`); a hand-built `NamelessExpr` must keep
/// every `VarId` either referencing an in-scope binder or
/// appearing in the entry-lambda parameter set.
///
/// `Clone` is a heap walk — see the `impl` below. Nesting depth is
/// script-controlled, so it must not sit on the call stack.
#[derive(Debug)]
pub(crate) enum NamelessExpr {
    // ===== Literals =====
    Int(BigInt),
    ByteArray(Vec<u8>),
    String(String),
    Bool(bool),
    Unit,

    // ===== Variables =====
    /// Variable reference. The `VarId` is the only identity —
    /// names live in [`VarTable`].
    Var(VarId),

    // ===== Functions =====
    Lambda {
        params: Vec<VarId>,
        body: NBox,
    },
    RecFn {
        name: VarId,
        params: Vec<VarId>,
        body: NBox,
    },
    Apply {
        function: NBox,
        args: NVec,
    },

    // ===== Bindings =====
    Let {
        binder: VarId,
        value: NBox,
        body: NBox,
    },

    // ===== Control Flow =====
    If {
        condition: NBox,
        then_branch: NBox,
        else_branch: NBox,
    },
    When {
        subject: NBox,
        subject_name: Option<VarId>,
        clauses: NClauses,
    },

    // ===== Data Structures =====
    List {
        elements: NVec,
        tail: Option<NBox>,
    },
    Tuple(NVec),
    Pair(NBox, NBox),
    Constr {
        type_hint: Option<crate::pseudo::type_hint::TypeHintId>,
        tag: usize,
        fields: NVec,
        shape: ConstructorShape,
    },

    // ===== Field / Index Access =====
    FieldAccess {
        record: NBox,
        selector: FieldSelector,
    },
    IndexAccess {
        collection: NBox,
        index: usize,
    },

    // ===== Operators =====
    BinOp {
        op: BinaryOp,
        left: NBox,
        right: NBox,
    },
    UnOp {
        op: UnaryOp,
        operand: NBox,
    },
    BuiltinCall {
        name: BuiltinId,
        args: NVec,
    },

    // ===== Special =====
    Error {
        message: Option<String>,
    },
    Delay(NBox),
    Force(NBox),
    Trace {
        message: NBox,
        value: NBox,
    },
    Raw {
        uplc: String,
        reason: String,
    },

    // ===== Cardano-specific =====
    Data(Box<PseudoData>),

    // ===== Intrinsic markers =====
    HelperSymbol(HelperIntrinsic),
}

/// One step of [`NamelessExpr`]'s clone.
enum CloneStep<'a> {
    /// Clone this node's children first.
    Visit(&'a NamelessExpr),
    /// Rebuild this node from the `usize` children already on the result stack.
    Build(&'a NamelessExpr, usize),
}

impl NamelessExpr {
    /// This node's direct `NamelessExpr` children, in traversal order.
    ///
    /// The single place that knows a node's child order —
    /// [`Self::clone_with_children`] consumes them in exactly this order, and
    /// the two must agree or a clone would silently rewire the tree.
    pub(crate) fn child_refs_into<'a>(&'a self, out: &mut Vec<&'a NamelessExpr>) {
        match self {
            NamelessExpr::Lambda { body, .. } | NamelessExpr::RecFn { body, .. } => {
                out.push(body.as_ref());
            }
            NamelessExpr::Apply { function, args } => {
                out.push(function.as_ref());
                out.extend(args.iter());
            }
            NamelessExpr::Let { value, body, .. } => {
                out.push(value.as_ref());
                out.push(body.as_ref());
            }
            NamelessExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                out.push(condition.as_ref());
                out.push(then_branch.as_ref());
                out.push(else_branch.as_ref());
            }
            NamelessExpr::When {
                subject, clauses, ..
            } => {
                out.push(subject.as_ref());
                for clause in clauses {
                    // A literal pattern carries an expression of its own.
                    if let NamelessPattern::Literal(lit) = &clause.pattern {
                        out.push(lit);
                    }
                    if let Some(guard) = &clause.guard {
                        out.push(guard);
                    }
                    out.push(&clause.body);
                }
            }
            NamelessExpr::List { elements, tail } => {
                out.extend(elements.iter());
                if let Some(tail) = tail {
                    out.push(tail.as_ref());
                }
            }
            NamelessExpr::Tuple(items) => out.extend(items.iter()),
            NamelessExpr::Pair(first, second) => {
                out.push(first.as_ref());
                out.push(second.as_ref());
            }
            NamelessExpr::Constr { fields, .. } => out.extend(fields.iter()),
            NamelessExpr::FieldAccess { record, .. } => out.push(record.as_ref()),
            NamelessExpr::IndexAccess { collection, .. } => out.push(collection.as_ref()),
            NamelessExpr::BinOp { left, right, .. } => {
                out.push(left.as_ref());
                out.push(right.as_ref());
            }
            NamelessExpr::UnOp { operand, .. } => out.push(operand.as_ref()),
            NamelessExpr::BuiltinCall { args, .. } => out.extend(args.iter()),
            NamelessExpr::Delay(inner) | NamelessExpr::Force(inner) => out.push(inner.as_ref()),
            NamelessExpr::Trace { message, value } => {
                out.push(message.as_ref());
                out.push(value.as_ref());
            }
            // Leaves. `Data` holds a `PseudoData`, not a `NamelessExpr`.
            NamelessExpr::Int(_)
            | NamelessExpr::ByteArray(_)
            | NamelessExpr::String(_)
            | NamelessExpr::Bool(_)
            | NamelessExpr::Unit
            | NamelessExpr::Var(_)
            | NamelessExpr::Error { .. }
            | NamelessExpr::Raw { .. }
            | NamelessExpr::Data(_)
            | NamelessExpr::HelperSymbol(_) => {}
        }
    }

    /// Rebuild this node around already-cloned children.
    ///
    /// Non-child fields (binders, tags, shapes, selectors) hold no
    /// `NamelessExpr` and are copied here.
    fn clone_with_children(&self, children: impl Iterator<Item = NamelessExpr>) -> NamelessExpr {
        let mut children = children;
        let mut next = |what: &str| {
            children
                .next()
                .unwrap_or_else(|| panic!("clone_with_children: missing {what}"))
        };
        match self {
            NamelessExpr::Lambda { params, .. } => NamelessExpr::Lambda {
                params: params.clone(),
                body: NBox::new(next("lambda body")),
            },
            NamelessExpr::RecFn { name, params, .. } => NamelessExpr::RecFn {
                name: *name,
                params: params.clone(),
                body: NBox::new(next("recfn body")),
            },
            NamelessExpr::Apply { args, .. } => {
                let function = NBox::new(next("apply callee"));
                NamelessExpr::Apply {
                    function,
                    args: (0..args.len()).map(|_| next("apply arg")).collect(),
                }
            }
            NamelessExpr::Let { binder, .. } => {
                let value = NBox::new(next("let value"));
                let body = NBox::new(next("let body"));
                NamelessExpr::Let {
                    binder: *binder,
                    value,
                    body,
                }
            }
            NamelessExpr::If { .. } => {
                let condition = NBox::new(next("if condition"));
                let then_branch = NBox::new(next("if then-branch"));
                let else_branch = NBox::new(next("if else-branch"));
                NamelessExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                }
            }
            NamelessExpr::When {
                subject_name,
                clauses,
                ..
            } => {
                let subject = NBox::new(next("when subject"));
                let clauses = clauses
                    .iter()
                    .map(|clause| {
                        // Same order as `child_refs_into`: literal, guard, body.
                        let pattern = match &clause.pattern {
                            NamelessPattern::Literal(_) => {
                                NamelessPattern::Literal(next("clause literal"))
                            }
                            // The other patterns hold only binders.
                            other => other.clone(),
                        };
                        let guard = clause.guard.as_ref().map(|_| next("clause guard"));
                        let body = next("clause body");
                        NamelessClause {
                            pattern,
                            guard,
                            body,
                        }
                    })
                    .collect();
                NamelessExpr::When {
                    subject,
                    subject_name: *subject_name,
                    clauses,
                }
            }
            NamelessExpr::List { elements, tail } => {
                let elements = (0..elements.len()).map(|_| next("list element")).collect();
                let tail = tail.as_ref().map(|_| NBox::new(next("list tail")));
                NamelessExpr::List { elements, tail }
            }
            NamelessExpr::Tuple(items) => {
                NamelessExpr::Tuple((0..items.len()).map(|_| next("tuple element")).collect())
            }
            NamelessExpr::Pair(..) => {
                let first = NBox::new(next("pair first"));
                let second = NBox::new(next("pair second"));
                NamelessExpr::Pair(first, second)
            }
            NamelessExpr::Constr {
                type_hint,
                tag,
                fields,
                shape,
            } => NamelessExpr::Constr {
                type_hint: type_hint.clone(),
                tag: *tag,
                fields: (0..fields.len()).map(|_| next("constr field")).collect(),
                shape: *shape,
            },
            NamelessExpr::FieldAccess { selector, .. } => NamelessExpr::FieldAccess {
                record: NBox::new(next("field-access record")),
                selector: selector.clone(),
            },
            NamelessExpr::IndexAccess { index, .. } => NamelessExpr::IndexAccess {
                collection: NBox::new(next("index-access collection")),
                index: *index,
            },
            NamelessExpr::BinOp { op, .. } => {
                let left = NBox::new(next("binop left"));
                let right = NBox::new(next("binop right"));
                NamelessExpr::BinOp {
                    op: *op,
                    left,
                    right,
                }
            }
            NamelessExpr::UnOp { op, .. } => NamelessExpr::UnOp {
                op: *op,
                operand: NBox::new(next("unop operand")),
            },
            NamelessExpr::BuiltinCall { name, args } => NamelessExpr::BuiltinCall {
                name: *name,
                args: (0..args.len()).map(|_| next("builtin arg")).collect(),
            },
            NamelessExpr::Delay(_) => NamelessExpr::Delay(NBox::new(next("delay body"))),
            NamelessExpr::Force(_) => NamelessExpr::Force(NBox::new(next("force body"))),
            NamelessExpr::Trace { .. } => {
                let message = NBox::new(next("trace message"));
                let value = NBox::new(next("trace value"));
                NamelessExpr::Trace { message, value }
            }
            NamelessExpr::Int(value) => NamelessExpr::Int(value.clone()),
            NamelessExpr::ByteArray(value) => NamelessExpr::ByteArray(value.clone()),
            NamelessExpr::String(value) => NamelessExpr::String(value.clone()),
            NamelessExpr::Bool(value) => NamelessExpr::Bool(*value),
            NamelessExpr::Unit => NamelessExpr::Unit,
            NamelessExpr::Var(id) => NamelessExpr::Var(*id),
            NamelessExpr::Error { message } => NamelessExpr::Error {
                message: message.clone(),
            },
            NamelessExpr::Raw { uplc, reason } => NamelessExpr::Raw {
                uplc: uplc.clone(),
                reason: reason.clone(),
            },
            NamelessExpr::Data(data) => NamelessExpr::Data(data.clone()),
            NamelessExpr::HelperSymbol(intrinsic) => NamelessExpr::HelperSymbol(*intrinsic),
        }
    }
}

/// Deep clone on a heap stack.
///
/// Nesting depth is script-controlled, and on `wasm32` the engine's call
/// stack cannot be grown to match. Do not replace this with `#[derive(Clone)]`.
impl Clone for NamelessExpr {
    fn clone(&self) -> Self {
        let mut steps: Vec<CloneStep<'_>> = vec![CloneStep::Visit(self)];
        let mut done: Vec<NamelessExpr> = Vec::new();
        // One buffer for the whole clone: `child_refs_into` would otherwise
        // allocate per node.
        let mut scratch: Vec<&NamelessExpr> = Vec::new();

        while let Some(step) = steps.pop() {
            match step {
                CloneStep::Visit(node) => {
                    scratch.clear();
                    node.child_refs_into(&mut scratch);
                    steps.push(CloneStep::Build(node, scratch.len()));
                    // Reversed so they pop — and so land on `done` — in order.
                    for child in scratch.iter().rev() {
                        steps.push(CloneStep::Visit(child));
                    }
                }
                CloneStep::Build(node, count) => {
                    let start = done.len() - count;
                    let rebuilt = node.clone_with_children(done.drain(start..));
                    done.push(rebuilt);
                }
            }
        }

        done.pop().expect("clone leaves exactly one result")
    }
}

/// Pattern-matching clause in nameless form.
#[derive(Debug, Clone)]
pub(crate) struct NamelessClause {
    pub pattern: NamelessPattern,
    pub guard: Option<NamelessExpr>,
    pub body: NamelessExpr,
}

/// When-pattern in nameless form. All binders are bare `VarId`.
#[derive(Debug, Clone)]
pub(crate) enum NamelessPattern {
    Wildcard,
    Var(VarId),
    Literal(NamelessExpr),
    Constructor {
        type_hint: Option<crate::pseudo::type_hint::TypeHintId>,
        tag: usize,
        fields: Vec<VarId>,
        shape: ConstructorShape,
    },
    List {
        elements: Vec<VarId>,
        tail: Option<VarId>,
    },
    Tuple(Vec<VarId>),
    Pair(VarId, VarId),
}

// =============================================================
// VarTable + VarMetadata
// =============================================================

/// Side table mapping `VarId` → metadata.
///
/// Single source of truth for what the simplifier would otherwise
/// sniff out of variable names: schema-derived field kinds
/// (`FieldIndexAlias`), Cardano-context types, call-result hints.
#[derive(Debug, Clone, Default)]
pub(crate) struct VarTable {
    metadata: HashMap<VarId, VarMetadata>,
}

impl VarTable {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn insert(&mut self, id: VarId, metadata: VarMetadata) {
        self.metadata.insert(id, metadata);
    }

    pub(crate) fn get(&self, id: VarId) -> Option<&VarMetadata> {
        self.metadata.get(&id)
    }

    pub(crate) fn get_mut(&mut self, id: VarId) -> Option<&mut VarMetadata> {
        self.metadata.get_mut(&id)
    }

    pub(crate) fn contains(&self, id: VarId) -> bool {
        self.metadata.contains_key(&id)
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&VarId, &VarMetadata)> {
        self.metadata.iter()
    }

    pub(crate) fn len(&self) -> usize {
        self.metadata.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.metadata.is_empty()
    }
}

/// Per-VarId metadata threading through the nameless IR.
#[derive(Debug, Clone)]
pub(crate) struct VarMetadata {
    /// Where this `VarId` was minted in the pipeline.
    pub origin: VarOrigin,

    /// Human-readable source/semantic name hint attached at mint time
    /// (typically the original UPLC variable name or a readability-rewrite
    /// suggestion). Pure annotation — never a dispatch source.
    pub name_hint: Option<String>,

    /// Final display-name override assigned by the late nameless naming
    /// owner. Raising back to `PseudoExpr` prefers it over `name_hint`,
    /// so `assign_names` leaves the original hint intact.
    pub display_name_hint: Option<String>,

    /// Type / role tag, used by Cardano-context naming and other
    /// dispatch passes WITHOUT relying on string names.
    pub kind: VarKind,
}

impl VarMetadata {
    /// Construct a "user binder" metadata entry — the default for
    /// vars whose origin is the original UPLC source.
    pub(crate) fn user(name_hint: impl Into<Option<String>>) -> Self {
        Self {
            origin: VarOrigin::UserBinder,
            name_hint: name_hint.into(),
            display_name_hint: None,
            kind: VarKind::User,
        }
    }

    /// Construct a synthetic-pass metadata entry.
    pub(crate) fn synthetic(producer: &'static str, hint: impl Into<Option<String>>) -> Self {
        Self {
            origin: VarOrigin::Synthetic {
                producer_pass: producer,
            },
            name_hint: hint.into(),
            display_name_hint: None,
            kind: VarKind::Synthetic,
        }
    }

    /// Name used when raising nameless IR for rendering.
    ///
    /// Skips empty-string hints in either slot so a stray `Some("")`
    /// doesn't shadow a meaningful fallback. Mirrors the
    /// `is_some_and(|n| !n.is_empty())` policy in
    /// `assign_names::candidate_name`.
    pub(crate) fn render_name_hint(&self) -> Option<&str> {
        self.display_name_hint
            .as_deref()
            .filter(|n| !n.is_empty())
            .or_else(|| self.name_hint.as_deref().filter(|n| !n.is_empty()))
    }
}

/// Where a `VarId` was introduced.
#[derive(Debug, Clone)]
pub(crate) enum VarOrigin {
    /// A binder from the original UPLC source (DeBruijn-named or
    /// MIR-lowered from a user lambda / let).
    UserBinder,
    /// A lambda parameter introduced by simplifier rewrites.
    LambdaParam,
    /// A let-binder introduced by simplifier rewrites.
    LetBinder,
    /// A binder minted by a specific simplifier pass.
    Synthetic { producer_pass: &'static str },
}

/// Type / role classification for a `VarId`. Each variant stands
/// in for a name-pattern dispatch site in the simplifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum VarKind {
    /// User-level binder — no special handling.
    User,

    /// Generic synthetic alias — no specific kind information.
    /// Use sparingly; prefer a specific variant.
    Synthetic,

    /// Synthetic alias for `parent.fields[index]`. Replaces the
    /// `field_N` name-pattern dispatch in
    /// `simplify::let_binding::aliases::introduce_field_index_aliases`.
    FieldIndexAlias { parent: VarId, index: usize },

    /// Synthetic alias for `parent[start..]` (List.tail chain).
    /// Replaces the textual `[N..]` chain detection in
    /// `simplify::transform::tail_chain_offsets`.
    SliceTailAlias { parent: VarId, depth: usize },

    /// Result of a function application. Replaces the
    /// `{fn}_result` name-pattern dispatch in
    /// `simplify::helpers::naming::suggest_generated_binding_name`.
    CallResult { callee: VarId },

    /// Hoisted large data literal. Replaces the
    /// `data_literal_N` name-pattern dispatch in
    /// `simplify::apply::hoist::hoist_large_data_literals_from_apply_args`.
    DataLiteralHoist,

    /// Cardano-context-typed binder (script_context, tx_info,
    /// redeemer, script_info). Replaces the string match in
    /// `cardano_context_naming::resolve_cardano_field_names`.
    /// `context_type` is a stringly tag, keeping
    /// `pseudo::nameless` decoupled from `decompile::simplify`'s
    /// internal `ContextType`.
    CardanoContext { context_type: String },

    /// Constr-payload binder — the K-th binder in a Constr<N> pattern
    /// at `pattern_id`. Minted by
    /// `pipeline::sync_late_constr_payload_kind_annotations`, consumed
    /// by `assign_names` to canonicalise unnamed constructor-pattern
    /// binders to `item_{index}`; a binder that already carries a
    /// meaningful name hint keeps it.
    ///
    /// `dangling_field_alias::repair_dangling_constr_payload_binders`
    /// is a name-level orphan-recovery pass over stray reference names
    /// and does NOT consume this kind.
    ConstrPayload { pattern_id: usize, index: usize },

    /// User-ADT field binder named from blueprint metadata. Distinct
    /// from `CardanoContext` so the Cardano-schema field-name lookup
    /// (`record_cardano_context_kind` in `cardano_context_naming.rs`)
    /// doesn't false-hit on user type names.
    ///
    /// Populated by `propagate_types_and_name_constructors` when a
    /// `WhenPattern::Constructor` carries a `TypeHintId` matching a
    /// user-ADT in `BlueprintHints::types`. Consumed by
    /// `assign_names::candidate_name`, which renders the binder as
    /// `field_name` instead of `field_N` / `item_N`.
    UserAdtField {
        type_name: String,
        field_name: String,
    },

    /// Validator entry point — the outermost Lambda after
    /// `hoist_local_helpers` has lifted top-level helpers into a Let
    /// chain. Render-prep wraps it in a synthetic `Let { name:
    /// "decompiled", kind: ValidatorEntry, value: <entry-Lambda>,
    /// body: <rest-of-chain> }`. The name is `decompiled` because
    /// `validator` collides with the keyword and renders as
    /// `validator_`. The kind lets the renderer find the entry
    /// without a name pattern, emit it as
    /// `fn decompiled(args) { ... }` instead of
    /// `let decompiled = fn(args) { ... }`, and place it first in the
    /// top-level output instead of last.
    ///
    /// the surface allows forward references between top-level declarations,
    /// so promoting the entry above its helpers keeps the rendered
    /// output well-scoped.
    ValidatorEntry,

    /// A validator-entry ROLE parameter (`datum` / `redeemer`) named by
    /// a validator-param rename. `param_name` is the role name; the
    /// trailing position is enforced at stamp time so a blueprint-named
    /// leading user param (even if coincidentally `datum`/`redeemer`) is
    /// never marked.
    ///
    ///   - `authoritative: true` — stamped by the LATE (post-uncurry)
    ///     rename, which the reverse-walk selector uses to pick the TRUE
    ///     entry. In `assign_names` it CLAIMS its bare role name.
    ///   - `authoritative: false` — stamped by the EARLY (pre-uncurry)
    ///     rename, which can name a NON-entry helper. Such a param
    ///     YIELDS its role name (gets suffixed) when an authoritative
    ///     param claims the same name; otherwise it keeps its name, the
    ///     fallback when the late rename found no entry.
    ///
    /// The marker — not VarId or fold order — is the entry-vs-helper
    /// discriminator. VarId ordering is NOT sound: a true entry's
    /// redeemer can carry a HIGHER VarId than a helper's, and in another
    /// script a LOWER VarId than a same-named body binder, so any VarId
    /// rule fixes one and regresses the other. Matching competitors by
    /// the (non-authoritative) marker — never by a broad name match —
    /// keeps genuine user `let redeemer = ...` binders (kind `User`)
    /// untouched.
    ///
    /// `script_context` is intentionally NOT marked: it carries
    /// `CardanoContext` (one kind per VarId) and is resolved by the
    /// descending-VarId "live binder wins" path in `candidate_name`.
    ValidatorEntryParam {
        param_name: String,
        authoritative: bool,
    },
}

impl VarKind {
    /// True for any kind the simplifier or pipeline mints itself
    /// rather than receiving from user code.
    pub(crate) fn is_generated_synthetic(&self) -> bool {
        matches!(
            self,
            Self::Synthetic
                | Self::FieldIndexAlias { .. }
                | Self::SliceTailAlias { .. }
                | Self::CallResult { .. }
                | Self::DataLiteralHoist
                | Self::ConstrPayload { .. }
                | Self::UserAdtField { .. }
        )
    }
}

// =============================================================
// Tests
// =============================================================

#[cfg(test)]
mod tests;

pub mod convert;
pub mod fold;
pub mod invariants;
