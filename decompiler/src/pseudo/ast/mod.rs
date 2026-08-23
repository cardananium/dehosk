//! Pseudo-code Abstract Syntax Tree.
//!
//! `PseudoExpr` models decompiled code closer to source than UPLC.

use num_bigint::BigInt;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::rc::Rc;

use crate::builtins::BuiltinId;
use crate::pseudo::type_hint::TypeHintId;

use super::constructor::{ConstructorShape, KnownConstructor};
use super::field_selector::FieldSelector;
use super::var_id::VarId;

/// Binder identity in `PseudoExpr`: a mutable display name, an
/// immutable semantic name, and a stable `VarId`.
///
/// Equality compares by `VarId`. The name-only comparison the
/// simplifier's convergence check needs is inlined at its call sites
/// rather than exposed as a `Binder` method.
///
/// Disambiguation passes such as `helper/hoist` rewrite `name` — e.g.
/// appending a `_<id>` suffix to break a shadow clash — so structural
/// recognizers must key on `semantic_name`, which those passes leave
/// untouched; a suffixed display name defeats their shape checks.
#[derive(Clone)]
pub(crate) struct Binder {
    /// Display name. Mutable; disambiguation passes write here.
    pub name: String,
    /// Semantic name, set at mint, never mutated after.
    /// Structural recognizers should read this rather than `name`.
    pub semantic_name: String,
    pub id: VarId,
}

/// Omits `semantic_name` when it equals `name`, keeping the
/// snapshot shape `Binder { name, id }`; a rename shows both.
impl std::fmt::Debug for Binder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut dbg = f.debug_struct("Binder");
        dbg.field("name", &self.name);
        if self.semantic_name != self.name {
            dbg.field("semantic_name", &self.semantic_name);
        }
        dbg.field("id", &self.id);
        dbg.finish()
    }
}

impl Binder {
    pub(crate) fn new(name: impl Into<String>, id: VarId) -> Self {
        let name = name.into();
        Self {
            semantic_name: name.clone(),
            name,
            id,
        }
    }

    /// Update the display name without touching the semantic name;
    /// used by disambiguation (shadow freshen, render-prep).
    pub(crate) fn set_display_name(&mut self, name: impl Into<String>) {
        self.name = name.into();
    }

    pub(crate) fn semantic_name(&self) -> &str {
        &self.semantic_name
    }

    pub(crate) fn display_name(&self) -> &str {
        &self.name
    }

    /// Create a `Binder` with a fresh authoritative `VarId` from
    /// the global [`VarId::fresh_binding`] counter.
    ///
    /// # Hazard
    ///
    /// Inside a simplify run prefer
    /// `Simplifier::fresh_synthetic_binder`: this global counter
    /// can collide with a per-instance one and orphan the refs.
    /// Use it at a pipeline **boundary**, not inside a walker,
    /// where a fresh id is the intended new anchor.
    #[track_caller]
    pub(crate) fn synthetic(name: impl Into<String>) -> Self {
        Self::new(name, VarId::fresh_binding())
    }

    /// Bulk variant of [`synthetic`]. Same hazards apply.
    #[track_caller]
    pub(crate) fn synthetic_many(names: Vec<String>) -> Vec<Self> {
        names.into_iter().map(Self::synthetic).collect()
    }

    pub(crate) fn as_str(&self) -> &str {
        &self.name
    }

    /// Returns a binder with a new name in BOTH the display and
    /// semantic slots — the "its meaning is now `<new>`" rename
    /// used by naming passes (`improve_variable_names` lifting
    /// `x_3` → `pairs`).
    ///
    /// For display-only disambiguation, which must preserve
    /// semantic intent, use `set_display_name`.
    pub(crate) fn renamed(&self, name: impl Into<String>) -> Self {
        let name = name.into();
        Self {
            semantic_name: name.clone(),
            name,
            id: self.id,
        }
    }

    pub(crate) fn into_name(self) -> String {
        self.name
    }

    pub(crate) fn var_id(&self) -> VarId {
        self.id
    }

    pub(crate) fn eq_by_var_id(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl PartialEq for Binder {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Binder {}

impl PartialEq<str> for Binder {
    fn eq(&self, other: &str) -> bool {
        self.name == other
    }
}

impl PartialEq<&str> for Binder {
    fn eq(&self, other: &&str) -> bool {
        self.name == *other
    }
}

impl PartialEq<String> for Binder {
    fn eq(&self, other: &String) -> bool {
        self.name == *other
    }
}

impl PartialEq<Binder> for String {
    fn eq(&self, other: &Binder) -> bool {
        *self == other.name
    }
}

impl PartialEq<&Binder> for String {
    fn eq(&self, other: &&Binder) -> bool {
        *self == other.name
    }
}

impl PartialEq<Binder> for &str {
    fn eq(&self, other: &Binder) -> bool {
        *self == other.name
    }
}

impl PartialEq<&Binder> for &str {
    fn eq(&self, other: &&Binder) -> bool {
        *self == other.name
    }
}

impl std::hash::Hash for Binder {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.id, state);
    }
}

impl std::fmt::Display for Binder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name.fmt(f)
    }
}

impl std::ops::Deref for Binder {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl AsRef<str> for Binder {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

// Hazard: these From impls invisibly mint a fresh `VarId` via
// `Binder::synthetic`; that global counter can collide with a
// Simplifier's per-instance allocator. Prefer
// `Simplifier::fresh_synthetic_binder`, or `Binder::new` with an id.
impl From<String> for Binder {
    #[track_caller]
    fn from(value: String) -> Self {
        Self::synthetic(value)
    }
}

impl From<&str> for Binder {
    #[track_caller]
    fn from(value: &str) -> Self {
        Self::synthetic(value)
    }
}

impl From<Binder> for String {
    fn from(value: Binder) -> Self {
        value.name
    }
}

pub(crate) use crate::pseudo::pbox::{Nested, Owned, OwnedVec};

/// A boxed child expression with an iterative destructor.
pub(crate) type PBox = Owned<PseudoExpr>;
/// A list of child expressions with an iterative destructor.
pub(crate) type PVec = OwnedVec<PseudoExpr>;

/// Hands the containers this node's children so they can release a tree
/// without recursing. Order matches [`PseudoExpr::child_refs_into`].
impl Nested for PseudoExpr {
    fn take_children(&mut self) -> Vec<PseudoExpr> {
        // A childless stand-in, so the emptied node drops shallowly.
        fn take(slot: &mut PseudoExpr) -> PseudoExpr {
            std::mem::replace(slot, PseudoExpr::Unit)
        }

        let mut out = Vec::new();
        match self {
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                out.push(take(body));
            }
            PseudoExpr::Apply { function, args } => {
                out.push(take(function));
                out.append(&mut args.take());
            }
            PseudoExpr::Let { value, body, .. } => {
                out.push(take(value));
                out.push(take(body));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                out.push(take(condition));
                out.push(take(then_branch));
                out.push(take(else_branch));
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                out.push(take(subject));
                for clause in clauses.iter_mut() {
                    if let WhenPattern::Literal(lit) = &mut clause.pattern {
                        out.push(take(lit));
                    }
                    if let Some(guard) = clause.guard.as_mut() {
                        out.push(take(guard));
                    }
                    out.push(take(&mut clause.body));
                }
            }
            PseudoExpr::List { elements, tail } => {
                out.append(&mut elements.take());
                if let Some(tail) = tail.as_mut() {
                    out.push(take(tail));
                }
            }
            PseudoExpr::Tuple(elements) => out.append(&mut std::mem::take(elements)),
            PseudoExpr::Pair(first, second) => {
                out.push(take(first));
                out.push(take(second));
            }
            PseudoExpr::Constr { fields, .. } => out.append(&mut std::mem::take(fields)),
            PseudoExpr::FieldAccess { record, .. } => out.push(take(record)),
            PseudoExpr::IndexAccess { collection, .. } => out.push(take(collection)),
            PseudoExpr::BinOp { left, right, .. } => {
                out.push(take(left));
                out.push(take(right));
            }
            PseudoExpr::UnOp { operand, .. } => out.push(take(operand)),
            PseudoExpr::BuiltinCall { args, .. } => out.append(&mut std::mem::take(args)),
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => out.push(take(inner)),
            PseudoExpr::Trace { message, value } => {
                out.push(take(message));
                out.push(take(value));
            }
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Var { .. }
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
        }
        out
    }
}

/// A high-level expression representing decompiled code — the
/// decompiler's main output type.
///
/// `Clone` is a heap walk — see the `impl` below. Nesting depth is
/// script-controlled, so it must not sit on the call stack.
#[derive(Debug)]
pub(crate) enum PseudoExpr {
    // ========== Literals ==========
    /// Integer literal (arbitrary precision).
    Int(BigInt),

    /// Byte array literal.
    ByteArray(Vec<u8>),

    /// String literal.
    String(String),

    /// Boolean literal.
    Bool(bool),

    /// Unit value (Void).
    Unit,

    // ========== Variables ==========
    /// Variable reference.
    Var {
        /// Variable name (may be generated if original name is unknown).
        name: String,
        /// Unique variable identity, or `None` for unresolved/symbolic refs
        /// (helper symbols like `expect!`/`fix`, or refs minted before
        /// resolution wires up the authoritative binder).
        id: Option<VarId>,
    },

    // ========== Functions ==========
    /// Lambda/anonymous function.
    Lambda {
        /// Parameter names.
        params: Vec<Binder>,
        /// Function body.
        body: PBox,
    },

    /// Recursive function (from Y-combinator application).
    /// `rec fn name(params) { body }`
    RecFn {
        /// Function name.
        name: Binder,
        /// Parameter names (excluding self-reference).
        params: Vec<Binder>,
        /// Function body (with self-calls using `name`).
        body: PBox,
    },

    /// Function application.
    Apply {
        /// Function being called.
        function: PBox,
        /// Arguments.
        args: PVec,
    },

    // ========== Bindings ==========
    /// Let binding.
    Let {
        /// Variable name.
        name: String,
        /// Unique variable identity, or `None` for compat-only let bindings
        /// (legacy `compat_let_bind` paths that lack an authoritative id).
        id: Option<VarId>,
        /// Value being bound.
        value: PBox,
        /// Body where binding is in scope.
        body: PBox,
    },

    // ========== Control Flow ==========
    /// If-then-else expression.
    If {
        /// Condition (should be Bool).
        condition: PBox,
        /// Then branch.
        then_branch: PBox,
        /// Else branch.
        else_branch: PBox,
    },

    /// Pattern matching expression (`when`).
    When {
        /// Subject being matched.
        subject: PBox,
        /// Optional subject name for use in clauses.
        subject_name: Option<Binder>,
        /// Match clauses.
        clauses: Vec<WhenClause>,
    },

    // ========== Data Structures ==========
    /// List literal.
    List {
        /// List elements.
        elements: PVec,
        /// Optional tail (for [head, ..tail] patterns).
        tail: Option<PBox>,
    },

    /// Tuple literal.
    Tuple(PVec),

    /// Pair literal.
    Pair(PBox, PBox),

    /// Constructor application (ADT value).
    Constr {
        /// Optional user-ADT hint keyed into [`BlueprintHintRegistry`].
        /// Populated by `adt_disambiguation` for `Unknown` shapes whose
        /// blueprint-sourced type name should drive rendering; render sites
        /// resolve it via `registry.resolve(shape, type_hint.as_ref())`.
        type_hint: Option<TypeHintId>,
        /// Constructor tag (index).
        tag: usize,
        /// Constructor fields.
        fields: PVec,
        /// Structural shape. Construct via the [`PseudoExpr::constr`] /
        /// [`PseudoExpr::constr_known`] factories so `tag` and `arity`
        /// stay in sync.
        shape: ConstructorShape,
    },

    // ========== Field Access ==========
    /// Field access on a record/constructor.
    FieldAccess {
        /// Record expression.
        record: PBox,
        /// Typed selector — closed-set `PairFst`/`PairSnd`/`ListHead`
        /// for the three structural accessors, `ContextField`/`NamedField`
        /// for everything else. Construct via
        /// [`PseudoExpr::field_access_typed`] or the legacy-string shim
        /// [`PseudoExpr::field_access`].
        selector: FieldSelector,
    },

    /// Tuple/list index access.
    IndexAccess {
        /// Collection expression.
        collection: PBox,
        /// Index.
        index: usize,
    },

    // ========== Operators ==========
    /// Binary operation.
    BinOp {
        /// Operator.
        op: BinaryOp,
        /// Left operand.
        left: PBox,
        /// Right operand.
        right: PBox,
    },

    /// Unary operation.
    UnOp {
        /// Operator.
        op: UnaryOp,
        /// Operand.
        operand: PBox,
    },

    /// Builtin function call (when not converted to operator).
    BuiltinCall {
        /// Canonical builtin identity.
        name: BuiltinId,
        /// Arguments.
        args: PVec,
    },

    // ========== Special ==========
    /// Error/fail expression.
    Error {
        /// Optional error message.
        message: Option<String>,
    },

    /// Delayed computation (lazy evaluation).
    Delay(PBox),

    /// Force evaluation of delayed computation.
    Force(PBox),

    /// Trace expression (for debugging).
    Trace {
        /// Message to trace.
        message: PBox,
        /// Value to return.
        value: PBox,
    },

    /// Raw UPLC term (when pattern not recognized).
    Raw {
        /// Pretty-printed UPLC representation.
        uplc: String,
        /// Description of why it wasn't decompiled.
        reason: String,
    },

    // ========== Cardano-specific ==========
    /// Plutus Data literal.
    Data(Box<PseudoData>),

    // ========== Intrinsic markers ==========
    /// Opaque intrinsic helper symbol. Leaf node — when applied, use
    /// the normal [`PseudoExpr::Apply`] wrapper. Simplification passes
    /// treat it as opaque: no inlining, no strip, no substitution.
    ///
    /// Gives the Y-combinator marker a structurally distinguishable
    /// form instead of the ambiguous `Var{name:"fix", id:None}`, which
    /// still occurs and is caught by the `flag_orphan_fix` backstop.
    HelperSymbol(HelperIntrinsic),
}

/// One step of [`PseudoExpr`]'s clone.
enum CloneStep<'a> {
    /// Clone this node's children first.
    Visit(&'a PseudoExpr),
    /// Rebuild this node from the `usize` children already on the result stack.
    Build(&'a PseudoExpr, usize),
}

impl PseudoExpr {
    /// This node's direct `PseudoExpr` children, in traversal order.
    ///
    /// The single place that knows a node's child order —
    /// [`Self::clone_with_children`] consumes them in exactly this order, and
    /// the two must agree or a clone would silently rewire the tree.
    fn child_refs_into<'a>(&'a self, out: &mut Vec<&'a PseudoExpr>) {
        match self {
            PseudoExpr::Lambda { body, .. } => out.push(body.as_ref()),
            PseudoExpr::RecFn { body, .. } => out.push(body.as_ref()),
            PseudoExpr::Apply { function, args } => {
                out.push(function.as_ref());
                out.extend(args.iter());
            }
            PseudoExpr::Let { value, body, .. } => {
                out.push(value.as_ref());
                out.push(body.as_ref());
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
                for clause in clauses {
                    // A literal pattern carries an expression of its own.
                    if let WhenPattern::Literal(lit) = &clause.pattern {
                        out.push(lit);
                    }
                    if let Some(guard) = &clause.guard {
                        out.push(guard);
                    }
                    out.push(&clause.body);
                }
            }
            PseudoExpr::List { elements, tail } => {
                out.extend(elements.iter());
                if let Some(tail) = tail {
                    out.push(tail.as_ref());
                }
            }
            PseudoExpr::Tuple(elements) => out.extend(elements.iter()),
            PseudoExpr::Pair(first, second) => {
                out.push(first.as_ref());
                out.push(second.as_ref());
            }
            PseudoExpr::Constr { fields, .. } => out.extend(fields.iter()),
            PseudoExpr::FieldAccess { record, .. } => out.push(record.as_ref()),
            PseudoExpr::IndexAccess { collection, .. } => out.push(collection.as_ref()),
            PseudoExpr::BinOp { left, right, .. } => {
                out.push(left.as_ref());
                out.push(right.as_ref());
            }
            PseudoExpr::UnOp { operand, .. } => out.push(operand.as_ref()),
            PseudoExpr::BuiltinCall { args, .. } => out.extend(args.iter()),
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => out.push(inner.as_ref()),
            PseudoExpr::Trace { message, value } => {
                out.push(message.as_ref());
                out.push(value.as_ref());
            }
            // Leaves. `Data` holds a `PseudoData`, not a `PseudoExpr`.
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Var { .. }
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
        }
    }

    /// Rebuild this node around already-cloned children.
    ///
    /// Non-child fields (names, binders, tags, shapes, selectors) hold no
    /// `PseudoExpr` and are copied here.
    fn clone_with_children(&self, children: impl Iterator<Item = PseudoExpr>) -> PseudoExpr {
        let mut children = children;
        let mut next = |what: &str| {
            children
                .next()
                .unwrap_or_else(|| panic!("clone_with_children: missing {what}"))
        };
        match self {
            PseudoExpr::Lambda { params, .. } => PseudoExpr::Lambda {
                params: params.clone(),
                body: PBox::new(next("lambda body")),
            },
            PseudoExpr::RecFn { name, params, .. } => PseudoExpr::RecFn {
                name: name.clone(),
                params: params.clone(),
                body: PBox::new(next("recfn body")),
            },
            PseudoExpr::Apply { args, .. } => {
                let function = PBox::new(next("apply callee"));
                PseudoExpr::Apply {
                    function,
                    args: (0..args.len()).map(|_| next("apply arg")).collect(),
                }
            }
            PseudoExpr::Let { name, id, .. } => {
                let value = PBox::new(next("let value"));
                let body = PBox::new(next("let body"));
                PseudoExpr::Let {
                    name: name.clone(),
                    id: *id,
                    value,
                    body,
                }
            }
            PseudoExpr::If { .. } => {
                let condition = PBox::new(next("if condition"));
                let then_branch = PBox::new(next("if then-branch"));
                let else_branch = PBox::new(next("if else-branch"));
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                }
            }
            PseudoExpr::When {
                subject_name,
                clauses,
                ..
            } => {
                let subject = PBox::new(next("when subject"));
                let clauses = clauses
                    .iter()
                    .map(|clause| {
                        // Same order as `child_refs`: literal, guard, body.
                        let pattern = match &clause.pattern {
                            WhenPattern::Literal(_) => WhenPattern::Literal(next("clause literal")),
                            // The other patterns hold only binders.
                            other => other.clone(),
                        };
                        let guard = clause.guard.as_ref().map(|_| next("clause guard"));
                        let body = next("clause body");
                        WhenClause {
                            pattern,
                            guard,
                            body,
                        }
                    })
                    .collect();
                PseudoExpr::When {
                    subject,
                    subject_name: subject_name.clone(),
                    clauses,
                }
            }
            PseudoExpr::List { elements, tail } => {
                let elements = (0..elements.len()).map(|_| next("list element")).collect();
                let tail = tail.as_ref().map(|_| PBox::new(next("list tail")));
                PseudoExpr::List { elements, tail }
            }
            PseudoExpr::Tuple(elements) => {
                PseudoExpr::Tuple((0..elements.len()).map(|_| next("tuple element")).collect())
            }
            PseudoExpr::Pair(..) => {
                let first = PBox::new(next("pair first"));
                let second = PBox::new(next("pair second"));
                PseudoExpr::Pair(first, second)
            }
            PseudoExpr::Constr {
                type_hint,
                tag,
                fields,
                shape,
            } => PseudoExpr::Constr {
                type_hint: type_hint.clone(),
                tag: *tag,
                fields: (0..fields.len()).map(|_| next("constr field")).collect(),
                shape: shape.clone(),
            },
            PseudoExpr::FieldAccess { selector, .. } => PseudoExpr::FieldAccess {
                record: PBox::new(next("field-access record")),
                selector: selector.clone(),
            },
            PseudoExpr::IndexAccess { index, .. } => PseudoExpr::IndexAccess {
                collection: PBox::new(next("index-access collection")),
                index: *index,
            },
            PseudoExpr::BinOp { op, .. } => {
                let left = PBox::new(next("binop left"));
                let right = PBox::new(next("binop right"));
                PseudoExpr::BinOp {
                    op: *op,
                    left,
                    right,
                }
            }
            PseudoExpr::UnOp { op, .. } => PseudoExpr::UnOp {
                op: *op,
                operand: PBox::new(next("unop operand")),
            },
            PseudoExpr::BuiltinCall { name, args } => PseudoExpr::BuiltinCall {
                name: *name,
                args: (0..args.len()).map(|_| next("builtin arg")).collect(),
            },
            PseudoExpr::Delay(_) => PseudoExpr::Delay(PBox::new(next("delay body"))),
            PseudoExpr::Force(_) => PseudoExpr::Force(PBox::new(next("force body"))),
            PseudoExpr::Trace { .. } => {
                let message = PBox::new(next("trace message"));
                let value = PBox::new(next("trace value"));
                PseudoExpr::Trace { message, value }
            }
            PseudoExpr::Int(value) => PseudoExpr::Int(value.clone()),
            PseudoExpr::ByteArray(value) => PseudoExpr::ByteArray(value.clone()),
            PseudoExpr::String(value) => PseudoExpr::String(value.clone()),
            PseudoExpr::Bool(value) => PseudoExpr::Bool(*value),
            PseudoExpr::Unit => PseudoExpr::Unit,
            PseudoExpr::Var { name, id } => PseudoExpr::Var {
                name: name.clone(),
                id: *id,
            },
            PseudoExpr::Error { message } => PseudoExpr::Error {
                message: message.clone(),
            },
            PseudoExpr::Raw { uplc, reason } => PseudoExpr::Raw {
                uplc: uplc.clone(),
                reason: reason.clone(),
            },
            PseudoExpr::Data(data) => PseudoExpr::Data(data.clone()),
            PseudoExpr::HelperSymbol(intrinsic) => PseudoExpr::HelperSymbol(*intrinsic),
        }
    }
}

/// Deep clone on a heap stack.
///
/// Nesting depth is script-controlled, and on `wasm32` the engine's call
/// stack cannot be grown to match. Do not replace this with `#[derive(Clone)]`.
impl Clone for PseudoExpr {
    fn clone(&self) -> Self {
        let mut steps: Vec<CloneStep<'_>> = vec![CloneStep::Visit(self)];
        let mut done: Vec<PseudoExpr> = Vec::new();
        // One buffer for the whole clone: `child_refs_into` would otherwise
        // allocate per node, and cloning is hot enough for that to show.
        let mut scratch: Vec<&PseudoExpr> = Vec::new();

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

/// Identifier for a canonical helper intrinsic.
///
/// Holds only markers with no surface syntax —
/// decompiler-side canonical names for UPLC patterns. The
/// string-based `Var("expect!")` helper stays out of this enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum HelperIntrinsic {
    /// Y/Z fixed-point combinator: the leaf that replaces
    /// Y-combinator-shaped UPLC. Surface rendering: `"fix"`.
    Fix,
}

/// Pattern matching clause for When expressions.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct WhenClause {
    /// Pattern to match.
    pub pattern: WhenPattern,
    /// Optional guard condition.
    pub guard: Option<PseudoExpr>,
    /// Body expression if pattern matches.
    pub body: PseudoExpr,
}

/// Pattern for when/case matching.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum WhenPattern {
    /// Constructor pattern: Some(x), None, Ok(value), etc.
    Constructor {
        /// Optional user-ADT hint keyed into [`BlueprintHintRegistry`].
        /// Populated by `adt_disambiguation` for `Unknown` shapes whose
        /// blueprint-sourced type name should drive rendering.
        type_hint: Option<TypeHintId>,
        tag: usize,
        fields: Vec<Binder>,
        /// Structural shape. Construct via [`WhenPattern::constructor`] /
        /// [`WhenPattern::constructor_known`] so `tag` and `arity` stay in
        /// sync.
        shape: ConstructorShape,
    },
    /// List pattern: [], [x], [x, y], [x, ..rest]
    List {
        elements: Vec<Binder>,
        tail: Option<Binder>,
    },
    /// Tuple pattern: (x, y, z)
    Tuple(Vec<Binder>),
    /// Pair pattern: Pair(x, y)
    Pair(Binder, Binder),
    /// Wildcard pattern: _
    Wildcard,
    /// Variable pattern: x
    Var(Binder),
    /// Literal pattern (for comparing against constants)
    Literal(PseudoExpr),
}

/// Binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // Comparison
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,

    // Logical
    And,
    Or,

    // ByteString/String
    Concat,

    // List
    Cons,
}

impl BinaryOp {
    pub(crate) fn symbol(&self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Mod => "%",
            Self::Eq => "==",
            Self::Neq => "!=",
            Self::Lt => "<",
            Self::Lte => "<=",
            Self::Gt => ">",
            Self::Gte => ">=",
            Self::And => "&&",
            Self::Or => "||",
            Self::Concat => "<>",
            Self::Cons => "::",
        }
    }

    /// Get operator precedence for proper parenthesization.
    pub(crate) fn precedence(&self) -> u8 {
        match self {
            Self::Or => 1,
            Self::And => 2,
            Self::Eq | Self::Neq => 3,
            Self::Lt | Self::Lte | Self::Gt | Self::Gte => 4,
            Self::Cons => 5,
            Self::Concat => 6,
            Self::Add | Self::Sub => 7,
            Self::Mul | Self::Div | Self::Mod => 8,
        }
    }

    /// Check if operator is right-associative.
    pub(crate) fn is_right_assoc(&self) -> bool {
        matches!(self, Self::Cons)
    }
}

/// Unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnaryOp {
    /// Logical negation: !x
    Not,
    /// Arithmetic negation: -x
    Negate,
    /// Length: length(x)
    Length,
}

impl UnaryOp {
    pub(crate) fn symbol(&self) -> &'static str {
        match self {
            Self::Not => "!",
            Self::Negate => "-",
            Self::Length => "length",
        }
    }
}

/// Pseudo-type representing inferred types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PseudoType {
    /// Integer type.
    Int,
    /// ByteArray type.
    ByteArray,
    /// String type.
    String,
    /// Boolean type.
    Bool,
    /// Unit/Void type.
    Unit,
    /// List type.
    List(Rc<PseudoType>),
    /// Tuple type.
    Tuple(Vec<Rc<PseudoType>>),
    /// Pair type.
    Pair(Rc<PseudoType>, Rc<PseudoType>),
    /// Option type.
    Option(Rc<PseudoType>),
    /// Result type.
    Result(Rc<PseudoType>, Rc<PseudoType>),
    /// Function type.
    Function {
        params: Vec<Rc<PseudoType>>,
        ret: Rc<PseudoType>,
    },
    /// Data type (Plutus Data).
    Data,
    /// BLS12-381 G1 element.
    G1Element,
    /// BLS12-381 G2 element.
    G2Element,
    /// BLS12-381 Miller loop result.
    MillerLoopResult,
    /// Named type (user-defined or unknown).
    Named(String),
    /// Unknown type (couldn't infer).
    Unknown,
    /// Type variable (for polymorphic functions).
    Var(String),
}

/// Explicit result of type recovery.
///
/// Kept separate from the storage shape inside `PseudoExpr` so type logic
/// never smuggles "missing type" through a raw `Option`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) enum TypeResolution {
    /// No type could be proven yet.
    #[default]
    Unknown,
    /// A concrete type is known.
    Known(Rc<PseudoType>),
}

impl TypeResolution {
    pub(crate) fn unknown() -> Self {
        Self::Unknown
    }

    pub(crate) fn known(tipo: impl Into<Rc<PseudoType>>) -> Self {
        Self::Known(tipo.into())
    }

    pub(crate) fn as_known(&self) -> Option<&Rc<PseudoType>> {
        match self {
            Self::Known(tipo) => Some(tipo),
            Self::Unknown => None,
        }
    }

    pub(crate) fn as_ref(&self) -> Option<&Rc<PseudoType>> {
        self.as_known()
    }

    pub(crate) fn cloned(&self) -> Option<Rc<PseudoType>> {
        self.as_known().cloned()
    }

    pub(crate) fn as_deref(&self) -> Option<&PseudoType> {
        self.as_known().map(|tipo| tipo.as_ref())
    }

    pub(crate) fn into_option(self) -> Option<Rc<PseudoType>> {
        match self {
            Self::Known(tipo) => Some(tipo),
            Self::Unknown => None,
        }
    }

    pub(crate) fn is_known(&self) -> bool {
        matches!(self, Self::Known(_))
    }

    pub(crate) fn is_some(&self) -> bool {
        self.is_known()
    }

    pub(crate) fn expect(self, msg: &str) -> Rc<PseudoType> {
        match self {
            Self::Known(tipo) => tipo,
            Self::Unknown => panic!("{msg}"),
        }
    }

    pub(crate) fn unwrap_or(self, default: Rc<PseudoType>) -> Rc<PseudoType> {
        match self {
            Self::Known(tipo) => tipo,
            Self::Unknown => default,
        }
    }

    pub(crate) fn unwrap_or_else(self, default: impl FnOnce() -> Rc<PseudoType>) -> Rc<PseudoType> {
        match self {
            Self::Known(tipo) => tipo,
            Self::Unknown => default(),
        }
    }

    pub(crate) fn or_else(self, fallback: impl FnOnce() -> Self) -> Self {
        match self {
            Self::Known(_) => self,
            Self::Unknown => fallback(),
        }
    }
}

impl From<Option<Rc<PseudoType>>> for TypeResolution {
    fn from(value: Option<Rc<PseudoType>>) -> Self {
        match value {
            Some(tipo) => Self::Known(tipo),
            None => Self::Unknown,
        }
    }
}

impl From<TypeResolution> for Option<Rc<PseudoType>> {
    fn from(value: TypeResolution) -> Self {
        value.into_option()
    }
}

impl From<Rc<PseudoType>> for TypeResolution {
    fn from(value: Rc<PseudoType>) -> Self {
        Self::Known(value)
    }
}

impl From<PseudoType> for TypeResolution {
    fn from(value: PseudoType) -> Self {
        Self::Known(Rc::new(value))
    }
}

impl PartialEq<Option<Rc<PseudoType>>> for TypeResolution {
    fn eq(&self, other: &Option<Rc<PseudoType>>) -> bool {
        match (self, other) {
            (Self::Unknown, None) => true,
            (Self::Known(left), Some(right)) => left == right,
            _ => false,
        }
    }
}

impl std::fmt::Display for PseudoType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int => f.write_str("Int"),
            Self::ByteArray => f.write_str("ByteArray"),
            Self::String => f.write_str("String"),
            Self::Bool => f.write_str("Bool"),
            Self::Unit => f.write_str("Void"),
            Self::List(t) => write!(f, "List<{}>", t),
            Self::Tuple(ts) => {
                f.write_str("(")?;
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}", t)?;
                }
                f.write_str(")")
            }
            Self::Pair(a, b) => write!(f, "Pair<{}, {}>", a, b),
            Self::Option(t) => write!(f, "Option<{}>", t),
            Self::Result(ok, err) => write!(f, "Result<{}, {}>", ok, err),
            Self::Function { params, ret } => {
                f.write_str("fn(")?;
                for (i, t) in params.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}", t)?;
                }
                write!(f, ") -> {}", ret)
            }
            Self::Data => f.write_str("Data"),
            Self::G1Element => f.write_str("G1Element"),
            Self::G2Element => f.write_str("G2Element"),
            Self::MillerLoopResult => f.write_str("MillerLoopResult"),
            Self::Named(name) => f.write_str(name),
            Self::Unknown => f.write_str("Data"),
            Self::Var(name) => f.write_str(name),
        }
    }
}

/// Plutus Data representation.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum PseudoData {
    /// Integer data.
    Integer(BigInt),
    /// ByteString data.
    ByteString(Vec<u8>),
    /// List of data.
    List(Vec<PseudoData>),
    /// Map of data pairs.
    Map(Vec<(PseudoData, PseudoData)>),
    /// Constructor data.
    Constr(usize, Vec<PseudoData>),
}

/// Stable node identifier for pseudo AST provenance graph.
pub type PseudoNodeId = u64;

/// Link from pseudo AST node to original UPLC term.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PseudoOriginLink {
    /// `uniq_id` of source UPLC term.
    pub uplc_uniq_id: isize,
    /// Role of this term in reconstruction.
    pub role: String,
    /// Confidence score in range `[0.0, 1.0]`.
    pub confidence: f32,
}

/// Optional origin mapping keyed by stable pseudo node id.
pub type PseudoOriginMap = HashMap<PseudoNodeId, Vec<PseudoOriginLink>>;

/// Provenance record for one pseudo AST node.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PseudoNodeProvenance {
    /// Stable identifier computed from structural path.
    pub id: PseudoNodeId,
    /// Parent node id in pseudo AST graph.
    pub parent_id: Option<PseudoNodeId>,
    /// Node kind, e.g. `let`, `apply`, `force`.
    pub kind: String,
    /// Child node ids in source order.
    pub child_ids: Vec<PseudoNodeId>,
    /// Optional links to original UPLC terms.
    pub origins: Vec<PseudoOriginLink>,
}

/// Provenance graph for pseudo AST.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PseudoProvenanceGraph {
    /// Root pseudo node id.
    pub root_id: PseudoNodeId,
    /// Flat node list.
    pub nodes: Vec<PseudoNodeProvenance>,
}

// ========== Structural equality (ignores VarId) ==========

impl PseudoExpr {
    /// Root-level type attached to this node, if it is self-evident from the literal kind.
    pub(crate) fn type_resolution(&self) -> TypeResolution {
        match self {
            Self::Int(_) => TypeResolution::from(PseudoType::Int),
            Self::ByteArray(_) => TypeResolution::from(PseudoType::ByteArray),
            Self::String(_) => TypeResolution::from(PseudoType::String),
            Self::Bool(_) => TypeResolution::from(PseudoType::Bool),
            Self::Unit => TypeResolution::from(PseudoType::Unit),
            Self::Data(_) => TypeResolution::from(PseudoType::Data),
            _ => TypeResolution::Unknown,
        }
    }

    /// Compare two `PseudoExpr` trees structurally, ignoring `VarId` fields,
    /// so nodes differing only in id assignment are equal. Used by the
    /// simplifier's fixed-point loop to detect convergence.
    pub(crate) fn structural_eq(&self, other: &Self) -> bool {
        structural_eq_no_clone(self, other)
    }
}

impl PartialEq for PseudoExpr {
    fn eq(&self, other: &Self) -> bool {
        crate::stack::grow_deep(|| structural_eq_no_clone(self, other))
    }
}

/// Compare two Binder slices by name (ignoring VarId) for structural equality.
fn binders_eq_by_name(a: &[Binder], b: &[Binder]) -> bool {
    a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.name == y.name)
}

/// Compare two optional Binders by name (ignoring VarId) for structural equality.
fn opt_binder_eq_by_name(a: &Option<Binder>, b: &Option<Binder>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => a.name == b.name,
        (None, None) => true,
        _ => false,
    }
}

/// Compare two WhenPatterns structurally; binders compare by name, not VarId.
fn when_pattern_structural_eq(a: &WhenPattern, b: &WhenPattern) -> bool {
    match (a, b) {
        (WhenPattern::Literal(l1), WhenPattern::Literal(l2)) => structural_eq_no_clone(l1, l2),
        (
            WhenPattern::Constructor {
                shape: s1,
                fields: f1,
                ..
            },
            WhenPattern::Constructor {
                shape: s2,
                fields: f2,
                ..
            },
        ) => s1 == s2 && binders_eq_by_name(f1, f2),
        (
            WhenPattern::List {
                elements: e1,
                tail: t1,
            },
            WhenPattern::List {
                elements: e2,
                tail: t2,
            },
        ) => {
            binders_eq_by_name(e1, e2)
                && match (t1, t2) {
                    (Some(a), Some(b)) => a.name == b.name,
                    (None, None) => true,
                    _ => false,
                }
        }
        (WhenPattern::Tuple(a), WhenPattern::Tuple(b)) => binders_eq_by_name(a, b),
        (WhenPattern::Pair(a1, b1), WhenPattern::Pair(a2, b2)) => {
            a1.name == a2.name && b1.name == b2.name
        }
        (WhenPattern::Wildcard, WhenPattern::Wildcard) => true,
        (WhenPattern::Var(a), WhenPattern::Var(b)) => a.name == b.name,
        _ => false,
    }
}

/// Compare two PseudoExpr trees structurally without cloning: VarId fields
/// (Var.id, Let.id, Binder.id) are ignored and binders compare by name.
fn structural_eq_no_clone(a: &PseudoExpr, b: &PseudoExpr) -> bool {
    use std::mem::discriminant;
    if discriminant(a) != discriminant(b) {
        return false;
    }
    match (a, b) {
        (PseudoExpr::Var { name: n1, .. }, PseudoExpr::Var { name: n2, .. }) => {
            n1 == n2 // skip id
        }
        (
            PseudoExpr::Let {
                name: n1,
                value: v1,
                body: b1,
                ..
            },
            PseudoExpr::Let {
                name: n2,
                value: v2,
                body: b2,
                ..
            },
        ) => n1 == n2 && structural_eq_no_clone(v1, v2) && structural_eq_no_clone(b1, b2),
        (
            PseudoExpr::Lambda {
                params: p1,
                body: b1,
            },
            PseudoExpr::Lambda {
                params: p2,
                body: b2,
            },
        ) => binders_eq_by_name(p1, p2) && structural_eq_no_clone(b1, b2),
        (
            PseudoExpr::RecFn {
                name: n1,
                params: p1,
                body: b1,
            },
            PseudoExpr::RecFn {
                name: n2,
                params: p2,
                body: b2,
            },
        ) => n1.name == n2.name && binders_eq_by_name(p1, p2) && structural_eq_no_clone(b1, b2),
        (
            PseudoExpr::Apply {
                function: f1,
                args: a1,
            },
            PseudoExpr::Apply {
                function: f2,
                args: a2,
            },
        ) => {
            a1.len() == a2.len()
                && structural_eq_no_clone(f1, f2)
                && a1
                    .iter()
                    .zip(a2.iter())
                    .all(|(x, y)| structural_eq_no_clone(x, y))
        }
        (
            PseudoExpr::If {
                condition: c1,
                then_branch: t1,
                else_branch: e1,
            },
            PseudoExpr::If {
                condition: c2,
                then_branch: t2,
                else_branch: e2,
            },
        ) => {
            structural_eq_no_clone(c1, c2)
                && structural_eq_no_clone(t1, t2)
                && structural_eq_no_clone(e1, e2)
        }
        (
            PseudoExpr::When {
                subject: s1,
                subject_name: sn1,
                clauses: c1,
            },
            PseudoExpr::When {
                subject: s2,
                subject_name: sn2,
                clauses: c2,
            },
        ) => {
            opt_binder_eq_by_name(sn1, sn2)
                && c1.len() == c2.len()
                && structural_eq_no_clone(s1, s2)
                && c1.iter().zip(c2.iter()).all(|(x, y)| {
                    when_pattern_structural_eq(&x.pattern, &y.pattern)
                        && match (&x.guard, &y.guard) {
                            (Some(g1), Some(g2)) => structural_eq_no_clone(g1, g2),
                            (None, None) => true,
                            _ => false,
                        }
                        && structural_eq_no_clone(&x.body, &y.body)
                })
        }
        (
            PseudoExpr::List {
                elements: e1,
                tail: t1,
            },
            PseudoExpr::List {
                elements: e2,
                tail: t2,
            },
        ) => {
            e1.len() == e2.len()
                && e1
                    .iter()
                    .zip(e2.iter())
                    .all(|(x, y)| structural_eq_no_clone(x, y))
                && match (t1, t2) {
                    (Some(a), Some(b)) => structural_eq_no_clone(a, b),
                    (None, None) => true,
                    _ => false,
                }
        }
        (PseudoExpr::Tuple(e1), PseudoExpr::Tuple(e2)) => {
            e1.len() == e2.len()
                && e1
                    .iter()
                    .zip(e2.iter())
                    .all(|(x, y)| structural_eq_no_clone(x, y))
        }
        (PseudoExpr::Pair(a1, b1), PseudoExpr::Pair(a2, b2)) => {
            structural_eq_no_clone(a1, a2) && structural_eq_no_clone(b1, b2)
        }
        (
            PseudoExpr::Constr {
                shape: s1,
                fields: f1,
                ..
            },
            PseudoExpr::Constr {
                shape: s2,
                fields: f2,
                ..
            },
        ) => {
            s1 == s2
                && f1.len() == f2.len()
                && f1
                    .iter()
                    .zip(f2.iter())
                    .all(|(x, y)| structural_eq_no_clone(x, y))
        }
        (
            PseudoExpr::FieldAccess {
                record: r1,
                selector: s1,
                ..
            },
            PseudoExpr::FieldAccess {
                record: r2,
                selector: s2,
                ..
            },
        ) => s1 == s2 && structural_eq_no_clone(r1, r2),
        (
            PseudoExpr::IndexAccess {
                collection: c1,
                index: i1,
            },
            PseudoExpr::IndexAccess {
                collection: c2,
                index: i2,
            },
        ) => i1 == i2 && structural_eq_no_clone(c1, c2),
        (
            PseudoExpr::BinOp {
                op: o1,
                left: l1,
                right: r1,
            },
            PseudoExpr::BinOp {
                op: o2,
                left: l2,
                right: r2,
            },
        ) => o1 == o2 && structural_eq_no_clone(l1, l2) && structural_eq_no_clone(r1, r2),
        (
            PseudoExpr::UnOp {
                op: o1,
                operand: a1,
            },
            PseudoExpr::UnOp {
                op: o2,
                operand: a2,
            },
        ) => o1 == o2 && structural_eq_no_clone(a1, a2),
        (
            PseudoExpr::BuiltinCall { name: n1, args: a1 },
            PseudoExpr::BuiltinCall { name: n2, args: a2 },
        ) => {
            n1 == n2
                && a1.len() == a2.len()
                && a1
                    .iter()
                    .zip(a2.iter())
                    .all(|(x, y)| structural_eq_no_clone(x, y))
        }
        (PseudoExpr::Delay(i1), PseudoExpr::Delay(i2)) => structural_eq_no_clone(i1, i2),
        (PseudoExpr::Force(i1), PseudoExpr::Force(i2)) => structural_eq_no_clone(i1, i2),
        (
            PseudoExpr::Trace {
                message: m1,
                value: v1,
            },
            PseudoExpr::Trace {
                message: m2,
                value: v2,
            },
        ) => structural_eq_no_clone(m1, m2) && structural_eq_no_clone(v1, v2),
        (PseudoExpr::Int(a), PseudoExpr::Int(b)) => a == b,
        (PseudoExpr::ByteArray(a), PseudoExpr::ByteArray(b)) => a == b,
        (PseudoExpr::String(a), PseudoExpr::String(b)) => a == b,
        (PseudoExpr::Bool(a), PseudoExpr::Bool(b)) => a == b,
        (PseudoExpr::Unit, PseudoExpr::Unit) => true,
        (PseudoExpr::Error { message: a }, PseudoExpr::Error { message: b }) => a == b,
        (
            PseudoExpr::Raw {
                uplc: uplc_a,
                reason: reason_a,
            },
            PseudoExpr::Raw {
                uplc: uplc_b,
                reason: reason_b,
            },
        ) => uplc_a == uplc_b && reason_a == reason_b,
        (PseudoExpr::Data(a), PseudoExpr::Data(b)) => a == b,
        (PseudoExpr::HelperSymbol(a), PseudoExpr::HelperSymbol(b)) => a == b,
        _ => unreachable!("discriminants matched but structural_eq_no_clone missed a variant"),
    }
}

// ========== Constructors ==========

impl PseudoExpr {
    const STABLE_NODE_ID_SEED: u64 = 0xcbf29ce484222325;
    const STABLE_NODE_ID_PRIME: u64 = 0x100000001b3;

    #[inline]
    fn stable_hash_byte(hash: u64, byte: u8) -> u64 {
        (hash ^ byte as u64).wrapping_mul(Self::STABLE_NODE_ID_PRIME)
    }

    fn stable_path_hash(path: &[u32]) -> u64 {
        let mut hash = Self::STABLE_NODE_ID_SEED;
        for index in path {
            hash = Self::stable_child_path_hash(hash, *index);
        }
        hash
    }

    /// Seed for a rolling path hash — the hash of the empty (root) path.
    ///
    /// Together with [`Self::extend_path_hash`] this lets a caller carry a
    /// path as a single `u64` that it extends as it descends, instead of an
    /// absolute `Vec<u32>` per node. See `mid::lower::PathArena`.
    pub(crate) const fn root_path_hash() -> u64 {
        Self::STABLE_NODE_ID_SEED
    }

    /// Extend a rolling path hash by one child step.
    #[inline]
    pub(crate) fn extend_path_hash(path_hash: u64, child_index: u32) -> u64 {
        Self::stable_child_path_hash(path_hash, child_index)
    }

    /// The node id this expression would get at a path with the given rolling
    /// hash — the `&[u32]`-free form of
    /// [`Self::provenance_node_id_for_path`].
    pub(crate) fn provenance_node_id_for_path_hash(&self, path_hash: u64) -> PseudoNodeId {
        Self::stable_node_id_from_path_hash(path_hash, self.provenance_kind_tag())
    }

    #[inline]
    fn stable_child_path_hash(mut path_hash: u64, child_index: u32) -> u64 {
        for byte in child_index.to_le_bytes() {
            path_hash = Self::stable_hash_byte(path_hash, byte);
        }
        path_hash
    }

    #[inline]
    fn stable_node_id_from_path_hash(path_hash: u64, kind_tag: u8) -> PseudoNodeId {
        Self::stable_hash_byte(path_hash, kind_tag)
    }

    pub(crate) fn provenance_graph(&self) -> PseudoProvenanceGraph {
        self.provenance_graph_with_origins(&HashMap::new())
    }

    pub(crate) fn provenance_graph_with_origins(
        &self,
        origins: &PseudoOriginMap,
    ) -> PseudoProvenanceGraph {
        let mut nodes = Vec::new();
        let mut path = Vec::new();
        let root_id = self.collect_provenance_nodes(
            &mut nodes,
            None,
            &mut path,
            Self::STABLE_NODE_ID_SEED,
            origins,
        );
        PseudoProvenanceGraph { root_id, nodes }
    }

    fn collect_provenance_nodes(
        &self,
        nodes: &mut Vec<PseudoNodeProvenance>,
        parent_id: Option<PseudoNodeId>,
        path: &mut Vec<u32>,
        path_hash: u64,
        origins: &PseudoOriginMap,
    ) -> PseudoNodeId {
        let node_id = Self::stable_node_id_from_path_hash(path_hash, self.provenance_kind_tag());
        let mut child_ids = Vec::new();

        for (idx, child) in self.provenance_children().into_iter().enumerate() {
            path.push(idx as u32);
            let child_id = child.collect_provenance_nodes(
                nodes,
                Some(node_id),
                path,
                Self::stable_child_path_hash(path_hash, idx as u32),
                origins,
            );
            path.pop();
            child_ids.push(child_id);
        }

        nodes.push(PseudoNodeProvenance {
            id: node_id,
            parent_id,
            kind: self.provenance_kind().to_string(),
            child_ids,
            origins: origins.get(&node_id).cloned().unwrap_or_default(),
        });

        node_id
    }

    pub(crate) fn provenance_children(&self) -> Vec<&PseudoExpr> {
        match self {
            PseudoExpr::Lambda { body, .. } => vec![body.as_ref()],
            PseudoExpr::RecFn { body, .. } => vec![body.as_ref()],
            PseudoExpr::Apply { function, args } => {
                let mut children = Vec::with_capacity(args.len() + 1);
                children.push(function.as_ref());
                children.extend(args.iter());
                children
            }
            PseudoExpr::Let { value, body, .. } => vec![value.as_ref(), body.as_ref()],
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => vec![
                condition.as_ref(),
                then_branch.as_ref(),
                else_branch.as_ref(),
            ],
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                let mut children = Vec::with_capacity(1 + clauses.len() * 3);
                children.push(subject.as_ref());
                for clause in clauses {
                    if let WhenPattern::Literal(lit) = &clause.pattern {
                        children.push(lit);
                    }
                    if let Some(guard) = &clause.guard {
                        children.push(guard);
                    }
                    children.push(&clause.body);
                }
                children
            }
            PseudoExpr::List { elements, tail } => {
                let mut children = Vec::with_capacity(elements.len() + usize::from(tail.is_some()));
                children.extend(elements.iter());
                if let Some(tail) = tail {
                    children.push(tail.as_ref());
                }
                children
            }
            PseudoExpr::Tuple(elements) => elements.iter().collect(),
            PseudoExpr::Pair(first, second) => vec![first.as_ref(), second.as_ref()],
            PseudoExpr::Constr { fields, .. } => fields.iter().collect(),
            PseudoExpr::FieldAccess { record, .. } => vec![record.as_ref()],
            PseudoExpr::IndexAccess { collection, .. } => vec![collection.as_ref()],
            PseudoExpr::BinOp { left, right, .. } => vec![left.as_ref(), right.as_ref()],
            PseudoExpr::UnOp { operand, .. } => vec![operand.as_ref()],
            PseudoExpr::BuiltinCall { args, .. } => args.iter().collect(),
            PseudoExpr::Delay(inner) => vec![inner.as_ref()],
            PseudoExpr::Force(inner) => vec![inner.as_ref()],
            PseudoExpr::Trace { message, value } => vec![message.as_ref(), value.as_ref()],
            _ => vec![],
        }
    }

    fn provenance_kind(&self) -> &'static str {
        match self {
            PseudoExpr::Int(_) => "int",
            PseudoExpr::ByteArray(_) => "byte_array",
            PseudoExpr::String(_) => "string",
            PseudoExpr::Bool(_) => "bool",
            PseudoExpr::Unit => "unit",
            PseudoExpr::Var { .. } => "var",
            PseudoExpr::Lambda { .. } => "lambda",
            PseudoExpr::RecFn { .. } => "rec_fn",
            PseudoExpr::Apply { .. } => "apply",
            PseudoExpr::Let { .. } => "let",
            PseudoExpr::If { .. } => "if",
            PseudoExpr::When { .. } => "when",
            PseudoExpr::List { .. } => "list",
            PseudoExpr::Tuple(_) => "tuple",
            PseudoExpr::Pair(..) => "pair",
            PseudoExpr::Constr { .. } => "constr",
            PseudoExpr::FieldAccess { .. } => "field_access",
            PseudoExpr::IndexAccess { .. } => "index_access",
            PseudoExpr::BinOp { .. } => "bin_op",
            PseudoExpr::UnOp { .. } => "un_op",
            PseudoExpr::BuiltinCall { .. } => "builtin_call",
            PseudoExpr::Error { .. } => "error",
            PseudoExpr::Delay(_) => "delay",
            PseudoExpr::Force(_) => "force",
            PseudoExpr::Trace { .. } => "trace",
            PseudoExpr::Raw { .. } => "raw",
            PseudoExpr::Data(_) => "data",
            PseudoExpr::HelperSymbol(_) => "helper_symbol",
        }
    }

    fn provenance_kind_tag(&self) -> u8 {
        match self {
            PseudoExpr::Int(_) => 1,
            PseudoExpr::ByteArray(_) => 2,
            PseudoExpr::String(_) => 3,
            PseudoExpr::Bool(_) => 4,
            PseudoExpr::Unit => 5,
            PseudoExpr::Var { .. } => 6,
            PseudoExpr::Lambda { .. } => 7,
            PseudoExpr::RecFn { .. } => 8,
            PseudoExpr::Apply { .. } => 9,
            PseudoExpr::Let { .. } => 10,
            PseudoExpr::If { .. } => 11,
            PseudoExpr::When { .. } => 12,
            PseudoExpr::List { .. } => 13,
            PseudoExpr::Tuple(_) => 14,
            PseudoExpr::Pair(..) => 15,
            PseudoExpr::Constr { .. } => 16,
            PseudoExpr::FieldAccess { .. } => 17,
            PseudoExpr::IndexAccess { .. } => 18,
            PseudoExpr::BinOp { .. } => 19,
            PseudoExpr::UnOp { .. } => 20,
            PseudoExpr::BuiltinCall { .. } => 21,
            PseudoExpr::Error { .. } => 22,
            PseudoExpr::Delay(_) => 23,
            PseudoExpr::Force(_) => 24,
            PseudoExpr::Trace { .. } => 25,
            PseudoExpr::Raw { .. } => 26,
            PseudoExpr::Data(_) => 27,
            PseudoExpr::HelperSymbol(_) => 28,
        }
    }

    fn stable_node_id(path: &[u32], kind_tag: u8) -> PseudoNodeId {
        Self::stable_node_id_from_path_hash(Self::stable_path_hash(path), kind_tag)
    }

    #[inline]
    pub(crate) fn provenance_root_path_hash() -> u64 {
        Self::STABLE_NODE_ID_SEED
    }

    #[inline]
    pub(crate) fn provenance_path_hash(path: &[u32]) -> u64 {
        Self::stable_path_hash(path)
    }

    #[inline]
    pub(crate) fn provenance_child_path_hash(path_hash: u64, child_index: u32) -> u64 {
        Self::stable_child_path_hash(path_hash, child_index)
    }

    #[inline]
    pub(crate) fn provenance_node_id_from_path_hash(&self, path_hash: u64) -> PseudoNodeId {
        Self::stable_node_id_from_path_hash(path_hash, self.provenance_kind_tag())
    }

    pub(crate) fn provenance_node_id_for_path(&self, path: &[u32]) -> PseudoNodeId {
        Self::stable_node_id(path, self.provenance_kind_tag())
    }

    /// Create an integer literal.
    pub(crate) fn int(value: impl Into<BigInt>) -> Self {
        Self::Int(value.into())
    }

    pub(crate) fn bool(value: bool) -> Self {
        Self::Bool(value)
    }

    pub(crate) fn string(value: impl Into<String>) -> Self {
        Self::String(value.into())
    }

    pub(crate) fn byte_array(value: impl Into<Vec<u8>>) -> Self {
        Self::ByteArray(value.into())
    }

    pub(crate) fn unit() -> Self {
        Self::Unit
    }

    /// Create a variable reference with no stable identity
    /// (`id: None`).
    ///
    /// # Hazard
    ///
    /// The ref is not anchored to a binder: naming transforms
    /// resolve it by NAME lookup, so if the expected binder is not in
    /// scope at the emit site the ref is effectively free. Prefer
    /// [`var_with_id`] when the caller knows the target binder's id;
    /// matching otherwise falls back to `refs_match`'s name path.
    #[track_caller]
    pub(crate) fn compat_var(name: impl Into<String>) -> Self {
        Self::Var {
            name: name.into(),
            id: None,
        }
    }

    /// Create a pseudo-symbol reference for decompiler helper heads such as
    /// `expect!`, `fix`, or internal recursion helpers. Stored as
    /// `Var { name, id: None }`; matchers identify them by name only.
    #[track_caller]
    pub(crate) fn helper_symbol(name: impl Into<String>) -> Self {
        Self::Var {
            name: name.into(),
            id: None,
        }
    }

    #[track_caller]
    pub(crate) fn expect_helper() -> Self {
        Self::helper_symbol("expect!")
    }

    /// Returns the canonical Y-combinator marker: the
    /// structurally-distinguishable `HelperSymbol(Fix)` leaf, not the
    /// `Var{name:"fix", id:None}` placeholder — matchers keyed on the
    /// bare-Var form do not see it. `flag_orphan_fix` catches stray
    /// `Var("fix")` refs that still reach render.
    #[track_caller]
    pub(crate) fn fix_helper() -> Self {
        Self::HelperSymbol(HelperIntrinsic::Fix)
    }

    /// Legacy compatibility alias for [`compat_var`].
    #[track_caller]
    pub(crate) fn var(name: impl Into<String>) -> Self {
        Self::compat_var(name)
    }

    /// Unlike [`compat_var`], the id is required.
    pub(crate) fn var_with_id(name: impl Into<String>, id: VarId) -> Self {
        Self::Var {
            name: name.into(),
            id: Some(id),
        }
    }

    pub(crate) fn lambda(params: Vec<String>, body: PseudoExpr) -> Self {
        Self::Lambda {
            params: Binder::synthetic_many(params),
            body: PBox::new(body),
        }
    }

    pub(crate) fn lambda_with_binders(params: Vec<Binder>, body: PseudoExpr) -> Self {
        Self::Lambda {
            params,
            body: PBox::new(body),
        }
    }

    pub(crate) fn apply(function: PseudoExpr, args: Vec<PseudoExpr>) -> Self {
        Self::Apply {
            function: PBox::new(function),
            args: args.into(),
        }
    }

    /// Compat placeholder `VarId` (`id: None`).
    pub(crate) fn compat_let_bind(
        name: impl Into<String>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> Self {
        Self::Let {
            name: name.into(),
            id: None,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }

    /// Legacy compatibility alias for [`compat_let_bind`].
    pub(crate) fn let_bind(name: impl Into<String>, value: PseudoExpr, body: PseudoExpr) -> Self {
        Self::compat_let_bind(name, value, body)
    }

    pub(crate) fn let_bind_with_id(
        name: impl Into<String>,
        id: VarId,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> Self {
        Self::Let {
            name: name.into(),
            id: Some(id),
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }

    pub(crate) fn if_then_else(
        condition: PseudoExpr,
        then_branch: PseudoExpr,
        else_branch: PseudoExpr,
    ) -> Self {
        Self::If {
            condition: PBox::new(condition),
            then_branch: PBox::new(then_branch),
            else_branch: PBox::new(else_branch),
        }
    }

    pub(crate) fn binop(op: BinaryOp, left: PseudoExpr, right: PseudoExpr) -> Self {
        Self::BinOp {
            op,
            left: PBox::new(left),
            right: PBox::new(right),
        }
    }

    pub(crate) fn unop(op: UnaryOp, operand: PseudoExpr) -> Self {
        Self::UnOp {
            op,
            operand: PBox::new(operand),
        }
    }

    pub(crate) fn builtin(name: impl AsRef<str>, args: Vec<PseudoExpr>) -> Self {
        Self::BuiltinCall {
            name: BuiltinId::expect_known(name.as_ref()),
            args: args.into(),
        }
    }

    pub(crate) fn builtin_id(name: BuiltinId, args: Vec<PseudoExpr>) -> Self {
        Self::BuiltinCall {
            name,
            args: args.into(),
        }
    }

    pub(crate) fn error() -> Self {
        Self::Error { message: None }
    }

    pub(crate) fn error_with_message(msg: impl Into<String>) -> Self {
        Self::Error {
            message: Some(msg.into()),
        }
    }

    pub(crate) fn raw(uplc: impl Into<String>, reason: impl Into<String>) -> Self {
        Self::Raw {
            uplc: uplc.into(),
            reason: reason.into(),
        }
    }

    pub(crate) fn list(elements: Vec<PseudoExpr>) -> Self {
        Self::List {
            elements: elements.into(),
            tail: None,
        }
    }

    pub(crate) fn tuple(elements: Vec<PseudoExpr>) -> Self {
        Self::Tuple(elements.into())
    }

    pub(crate) fn pair(first: PseudoExpr, second: PseudoExpr) -> Self {
        Self::Pair(PBox::new(first), PBox::new(second))
    }

    /// Create a field-access expression from a legacy string.
    ///
    /// Shim over [`PseudoExpr::field_access_typed`] for callers that still
    /// carry the stringly field name (tests, legacy naming passes).
    pub(crate) fn field_access(record: PseudoExpr, field: impl Into<String>) -> Self {
        let selector = FieldSelector::from_display_name(&field.into());
        Self::field_access_typed(record, selector)
    }

    /// Create a field-access expression from a typed [`FieldSelector`].
    ///
    /// Preferred construction path: callers that already hold a
    /// selector (UPLC lowering, AST rebuilds) skip the string
    /// round-trip.
    pub(crate) fn field_access_typed(record: PseudoExpr, selector: FieldSelector) -> Self {
        Self::FieldAccess {
            record: PBox::new(record),
            selector,
        }
    }

    /// Create a constructor whose identity is already in the closed set.
    ///
    /// `shape` is pinned to `Known(kc)` so pretty-printing anchors on it;
    /// use this once disambiguation has resolved the `KnownConstructor`.
    pub(crate) fn constr_known(kc: KnownConstructor, fields: Vec<PseudoExpr>) -> Self {
        Self::Constr {
            type_hint: None,
            tag: kc.expected_tag(),
            fields: fields.into(),
            shape: ConstructorShape::Known(kc),
        }
    }

    /// Create a constructor from a [`ConstructorShape`] (shape-first API).
    ///
    /// Tag comes from `shape.tag()`; `fields.len()` is checked against
    /// `shape.arity()` by `debug_assert_eq!`. Pretty-printing anchors on
    /// `shape.pretty_name()` for `Known` and on the
    /// [`BlueprintHintRegistry`] via `type_hint` for `Unknown` user ADTs.
    /// Prefer [`Self::constr_known`] for a statically known closed-set
    /// constructor; this factory also accepts `Unknown` shapes.
    pub(crate) fn constr(shape: ConstructorShape, fields: Vec<PseudoExpr>) -> Self {
        Self::constr_with_hint(shape, fields, None)
    }

    /// Create a constructor from a [`ConstructorShape`] with an optional
    /// [`TypeHintId`] for [`BlueprintHintRegistry`] lookup at render time.
    ///
    /// Pass a hint for `Unknown` shapes carrying a blueprint-sourced type
    /// name; `Known` shapes need none — `shape.pretty_name()` is already
    /// the canonical render name.
    pub(crate) fn constr_with_hint(
        shape: ConstructorShape,
        fields: Vec<PseudoExpr>,
        type_hint: Option<TypeHintId>,
    ) -> Self {
        debug_assert_eq!(
            shape.arity(),
            fields.len(),
            "ConstructorShape::arity ({}) does not match fields.len() ({})",
            shape.arity(),
            fields.len(),
        );
        Self::Constr {
            type_hint,
            tag: shape.tag(),
            fields: fields.into(),
            shape,
        }
    }

    /// Create Option::Some (`Constr 0`, one field).
    pub(crate) fn some(value: PseudoExpr) -> Self {
        Self::constr_known(KnownConstructor::Some, vec![value])
    }

    /// Create Option::None (`Constr 1`, nullary).
    pub(crate) fn none() -> Self {
        Self::constr_known(KnownConstructor::None, vec![])
    }

    pub(crate) fn ok(value: PseudoExpr) -> Self {
        Self::constr_known(KnownConstructor::Ok, vec![value])
    }

    pub(crate) fn err(value: PseudoExpr) -> Self {
        Self::constr_known(KnownConstructor::Error, vec![value])
    }
}

impl WhenClause {
    pub(crate) fn new(pattern: WhenPattern, body: PseudoExpr) -> Self {
        Self {
            pattern,
            guard: None,
            body,
        }
    }

    pub(crate) fn with_guard(pattern: WhenPattern, guard: PseudoExpr, body: PseudoExpr) -> Self {
        Self {
            pattern,
            guard: Some(guard),
            body,
        }
    }
}

impl WhenPattern {
    /// Create a constructor pattern whose identity is already in the
    /// closed set.
    ///
    /// The `shape` is pinned to `Known(kc)` so pretty-printing anchors on
    /// the shape. Mirror of [`PseudoExpr::constr_known`].
    pub(crate) fn constructor_known(kc: KnownConstructor, fields: Vec<Binder>) -> Self {
        Self::Constructor {
            type_hint: None,
            tag: kc.expected_tag(),
            fields,
            shape: ConstructorShape::Known(kc),
        }
    }

    /// Create a constructor pattern from a [`ConstructorShape`]
    /// (shape-first API).
    ///
    /// Mirror of [`PseudoExpr::constr`]: tag derives from `shape.tag()`;
    /// arity is asserted against `fields.len()`; rendering anchors on
    /// shape / registry / type_hint.
    pub(crate) fn constructor(shape: ConstructorShape, fields: Vec<Binder>) -> Self {
        Self::constructor_with_hint(shape, fields, None)
    }

    /// Create a constructor pattern from a [`ConstructorShape`] with an
    /// optional [`TypeHintId`] for [`BlueprintHintRegistry`] lookup.
    ///
    /// Mirror of [`PseudoExpr::constr_with_hint`].
    pub(crate) fn constructor_with_hint(
        shape: ConstructorShape,
        fields: Vec<Binder>,
        type_hint: Option<TypeHintId>,
    ) -> Self {
        debug_assert_eq!(
            shape.arity(),
            fields.len(),
            "ConstructorShape::arity ({}) does not match fields.len() ({})",
            shape.arity(),
            fields.len(),
        );
        Self::Constructor {
            type_hint,
            tag: shape.tag(),
            fields,
            shape,
        }
    }

    pub(crate) fn wildcard() -> Self {
        Self::Wildcard
    }

    pub(crate) fn var(name: impl Into<String>) -> Self {
        Self::Var(name.into().into())
    }

    /// Returns every binder VarId introduced by this pattern.
    ///
    /// Call this rather than redefining the walk locally.
    pub(crate) fn bound_ids(&self) -> Vec<VarId> {
        match self {
            WhenPattern::Constructor { fields, .. } => {
                fields.iter().map(|binder| binder.id).collect()
            }
            WhenPattern::List { elements, tail } => {
                let mut ids: Vec<VarId> = elements.iter().map(|binder| binder.id).collect();
                if let Some(tail) = tail {
                    ids.push(tail.id);
                }
                ids
            }
            WhenPattern::Tuple(fields) => fields.iter().map(|binder| binder.id).collect(),
            WhenPattern::Pair(left, right) => vec![left.id, right.id],
            WhenPattern::Var(binder) => vec![binder.id],
            WhenPattern::Wildcard | WhenPattern::Literal(_) => Vec::new(),
        }
    }

    /// Returns every binder name introduced by this pattern.
    ///
    /// Mirror of [`Self::bound_ids`] for name-based access.
    pub(crate) fn bound_names(&self) -> Vec<String> {
        match self {
            WhenPattern::Constructor { fields, .. } => {
                fields.iter().map(|binder| binder.name.clone()).collect()
            }
            WhenPattern::List { elements, tail } => {
                let mut names: Vec<String> =
                    elements.iter().map(|binder| binder.name.clone()).collect();
                if let Some(tail) = tail {
                    names.push(tail.name.clone());
                }
                names
            }
            WhenPattern::Tuple(fields) => fields.iter().map(|binder| binder.name.clone()).collect(),
            WhenPattern::Pair(left, right) => vec![left.name.clone(), right.name.clone()],
            WhenPattern::Var(binder) => vec![binder.name.clone()],
            WhenPattern::Wildcard | WhenPattern::Literal(_) => Vec::new(),
        }
    }
}

impl std::fmt::Display for WhenPattern {
    /// Registry-FREE rendering: a constructor shows the name its
    /// `ConstructorShape` already carries, else `Constr<tag>`.
    ///
    /// User-ADT names live in the `BlueprintHintRegistry`, which is a
    /// render-layer concern; `decompile::render::pattern::pattern_to_string`
    /// is the registry-aware form and is what the printer calls.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Constructor {
                tag, fields, shape, ..
            } => {
                let name = shape
                    .pretty_name()
                    .map(str::to_string)
                    .unwrap_or_else(|| format!("Constr{tag}"));
                if fields.is_empty() {
                    f.write_str(&name)
                } else {
                    let args: Vec<String> = fields.iter().map(ToString::to_string).collect();
                    write!(f, "{name}({})", args.join(", "))
                }
            }
            Self::List { elements, tail } => {
                let mut parts: Vec<String> = elements.iter().map(ToString::to_string).collect();
                if let Some(t) = tail {
                    parts.push(format!("..{t}"));
                }
                write!(f, "[{}]", parts.join(", "))
            }
            Self::Tuple(fields) => {
                let parts: Vec<String> = fields.iter().map(ToString::to_string).collect();
                write!(f, "({})", parts.join(", "))
            }
            Self::Pair(a, b) => write!(f, "Pair({a}, {b})"),
            Self::Wildcard => f.write_str("_"),
            Self::Var(name) => write!(f, "{name}"),
            Self::Literal(expr) => write!(f, "{expr:?}"),
        }
    }
}

#[cfg(test)]
mod tests;
