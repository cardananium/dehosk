//! Round-trip converters between `PseudoExpr` and [`NamelessExpr`].
//!
//! **Lossless on already-named PseudoExpr**:
//! ```text
//! nameless_to_pseudo(pseudo_to_nameless(expr)) ≡ expr
//! ```
//! provided every `Var.id` in `expr` has a corresponding binder
//! in lexical scope (i.e. no orphans). Var names survive in
//! [`VarTable`] as `name_hint` on the way down, read back through
//! `render_name_hint()` on the way up.

use super::super::ast::{
    BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause as PseudoWhenClause,
    WhenPattern as PseudoWhenPattern,
};
use super::super::constructor::ConstructorShape;
use super::super::field_selector::FieldSelector;
use super::super::type_hint::TypeHintId;
use super::super::var_id::VarId;
use super::{
    NamelessClause, NamelessExpr, NamelessPattern, VarKind, VarMetadata, VarOrigin, VarTable,
};
use crate::builtins::BuiltinId;
use crate::pseudo::ast::PBox;

// =============================================================
// pseudo_to_nameless
// =============================================================

/// Convert a `PseudoExpr` to a [`NamelessExpr`], stashing every
/// var name as a `name_hint` in the returned [`VarTable`].
///
/// Structural: node shapes are preserved and variable identity
/// is carried by `VarId`. Each first-seen `VarId` gets a table
/// entry with its original name and `origin: UserBinder`.
pub(crate) fn pseudo_to_nameless(expr: &PseudoExpr) -> (NamelessExpr, VarTable) {
    let mut table = VarTable::new();
    let nameless = lower(expr, &mut table);
    (nameless, table)
}

fn record_binder(table: &mut VarTable, binder: &Binder) {
    if !table.contains(binder.id) {
        table.insert(
            binder.id,
            VarMetadata {
                origin: VarOrigin::UserBinder,
                name_hint: Some(binder.name.clone()),
                display_name_hint: None,
                kind: VarKind::User,
            },
        );
    }
}

fn record_var_id_with_hint(table: &mut VarTable, id: VarId, hint: Option<String>) {
    if !table.contains(id) {
        table.insert(
            id,
            VarMetadata {
                origin: VarOrigin::UserBinder,
                name_hint: hint,
                display_name_hint: None,
                kind: VarKind::User,
            },
        );
    }
}

fn lower(expr: &PseudoExpr, table: &mut VarTable) -> NamelessExpr {
    enum Step<'e> {
        /// Visit a node: run its pre-descent side effects, then either
        /// emit a leaf directly or push a `Build` marker plus children.
        Expr(&'e PseudoExpr),
        /// A `when` clause: pattern binders are recorded (and a literal
        /// pattern's embedded expr descended) before guard/body.
        Clause(&'e PseudoWhenClause),
        /// All of a node's children are on `results` (and, for `When`,
        /// `clause_results`) — reassemble it.
        Build(Build<'e>),
        /// A clause's guard/body (and literal pattern, if any) are on
        /// `results` — reassemble the `NamelessClause`.
        BuildClause {
            /// `None` when the pattern was `Literal` and its lowered form
            /// is the bottom-most of this clause's `results` entries;
            /// `Some` when the pattern needed no further descent.
            pattern: Option<NamelessPattern>,
            has_guard: bool,
        },
    }

    enum Build<'e> {
        Lambda {
            params: &'e [Binder],
        },
        RecFn {
            name: &'e Binder,
            params: &'e [Binder],
        },
        Apply {
            nargs: usize,
        },
        Let {
            id: VarId,
        },
        If,
        When {
            subject_name: Option<VarId>,
            nclauses: usize,
        },
        List {
            nelements: usize,
            has_tail: bool,
        },
        Tuple(usize),
        Pair,
        Constr {
            type_hint: Option<TypeHintId>,
            tag: usize,
            nfields: usize,
            shape: ConstructorShape,
        },
        FieldAccess {
            selector: FieldSelector,
        },
        IndexAccess {
            index: usize,
        },
        BinOp {
            op: BinaryOp,
        },
        UnOp {
            op: UnaryOp,
        },
        BuiltinCall {
            name: BuiltinId,
            nargs: usize,
        },
        Delay,
        Force,
        Trace,
    }

    fn take_n(results: &mut Vec<NamelessExpr>, n: usize) -> Vec<NamelessExpr> {
        let at = results.len() - n;
        results.split_off(at)
    }

    let mut steps: Vec<Step> = vec![Step::Expr(expr)];
    let mut results: Vec<NamelessExpr> = Vec::new();
    let mut clause_results: Vec<NamelessClause> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Expr(e) => match e {
                PseudoExpr::Int(n) => results.push(NamelessExpr::Int(n.clone())),
                PseudoExpr::ByteArray(b) => results.push(NamelessExpr::ByteArray(b.clone())),
                PseudoExpr::String(s) => results.push(NamelessExpr::String(s.clone())),
                PseudoExpr::Bool(b) => results.push(NamelessExpr::Bool(*b)),
                PseudoExpr::Unit => results.push(NamelessExpr::Unit),
                PseudoExpr::Var { name, id } => {
                    let vid = id.unwrap_or_else(VarId::fresh_compat_placeholder);
                    record_var_id_with_hint(table, vid, Some(name.clone()));
                    results.push(NamelessExpr::Var(vid));
                }
                PseudoExpr::Lambda { params, body } => {
                    for p in params {
                        record_binder(table, p);
                    }
                    steps.push(Step::Build(Build::Lambda { params }));
                    steps.push(Step::Expr(body));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    record_binder(table, name);
                    for p in params {
                        record_binder(table, p);
                    }
                    steps.push(Step::Build(Build::RecFn { name, params }));
                    steps.push(Step::Expr(body));
                }
                PseudoExpr::Apply { function, args } => {
                    steps.push(Step::Build(Build::Apply { nargs: args.len() }));
                    for a in args.iter().rev() {
                        steps.push(Step::Expr(a));
                    }
                    steps.push(Step::Expr(function));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    let vid = id.unwrap_or_else(VarId::fresh_compat_placeholder);
                    record_var_id_with_hint(table, vid, Some(name.clone()));
                    steps.push(Step::Build(Build::Let { id: vid }));
                    steps.push(Step::Expr(body));
                    steps.push(Step::Expr(value));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(Step::Build(Build::If));
                    steps.push(Step::Expr(else_branch));
                    steps.push(Step::Expr(then_branch));
                    steps.push(Step::Expr(condition));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    if let Some(sn) = subject_name {
                        record_binder(table, sn);
                    }
                    steps.push(Step::Build(Build::When {
                        subject_name: subject_name.as_ref().map(|b| b.id),
                        nclauses: clauses.len(),
                    }));
                    for c in clauses.iter().rev() {
                        steps.push(Step::Clause(c));
                    }
                    steps.push(Step::Expr(subject));
                }
                PseudoExpr::List { elements, tail } => {
                    steps.push(Step::Build(Build::List {
                        nelements: elements.len(),
                        has_tail: tail.is_some(),
                    }));
                    if let Some(t) = tail {
                        steps.push(Step::Expr(t));
                    }
                    for e in elements.iter().rev() {
                        steps.push(Step::Expr(e));
                    }
                }
                PseudoExpr::Tuple(items) => {
                    steps.push(Step::Build(Build::Tuple(items.len())));
                    for i in items.iter().rev() {
                        steps.push(Step::Expr(i));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    steps.push(Step::Build(Build::Pair));
                    steps.push(Step::Expr(b));
                    steps.push(Step::Expr(a));
                }
                PseudoExpr::Constr {
                    type_hint,
                    tag,
                    fields,
                    shape,
                } => {
                    steps.push(Step::Build(Build::Constr {
                        type_hint: type_hint.clone(),
                        tag: *tag,
                        nfields: fields.len(),
                        shape: *shape,
                    }));
                    for f in fields.iter().rev() {
                        steps.push(Step::Expr(f));
                    }
                }
                PseudoExpr::FieldAccess { record, selector } => {
                    steps.push(Step::Build(Build::FieldAccess {
                        selector: selector.clone(),
                    }));
                    steps.push(Step::Expr(record));
                }
                PseudoExpr::IndexAccess { collection, index } => {
                    steps.push(Step::Build(Build::IndexAccess { index: *index }));
                    steps.push(Step::Expr(collection));
                }
                PseudoExpr::BinOp { op, left, right } => {
                    steps.push(Step::Build(Build::BinOp { op: *op }));
                    steps.push(Step::Expr(right));
                    steps.push(Step::Expr(left));
                }
                PseudoExpr::UnOp { op, operand } => {
                    steps.push(Step::Build(Build::UnOp { op: *op }));
                    steps.push(Step::Expr(operand));
                }
                PseudoExpr::BuiltinCall { name, args } => {
                    steps.push(Step::Build(Build::BuiltinCall {
                        name: *name,
                        nargs: args.len(),
                    }));
                    for a in args.iter().rev() {
                        steps.push(Step::Expr(a));
                    }
                }
                PseudoExpr::Error { message } => results.push(NamelessExpr::Error {
                    message: message.clone(),
                }),
                PseudoExpr::Delay(inner) => {
                    steps.push(Step::Build(Build::Delay));
                    steps.push(Step::Expr(inner));
                }
                PseudoExpr::Force(inner) => {
                    steps.push(Step::Build(Build::Force));
                    steps.push(Step::Expr(inner));
                }
                PseudoExpr::Trace { message, value } => {
                    steps.push(Step::Build(Build::Trace));
                    steps.push(Step::Expr(value));
                    steps.push(Step::Expr(message));
                }
                PseudoExpr::Raw { uplc, reason } => results.push(NamelessExpr::Raw {
                    uplc: uplc.clone(),
                    reason: reason.clone(),
                }),
                PseudoExpr::Data(d) => results.push(NamelessExpr::Data(d.clone())),
                PseudoExpr::HelperSymbol(intrinsic) => {
                    results.push(NamelessExpr::HelperSymbol(*intrinsic))
                }
            },
            Step::Clause(c) => {
                if let PseudoWhenPattern::Literal(lit) = &c.pattern {
                    steps.push(Step::BuildClause {
                        pattern: None,
                        has_guard: c.guard.is_some(),
                    });
                    steps.push(Step::Expr(&c.body));
                    if let Some(g) = &c.guard {
                        steps.push(Step::Expr(g));
                    }
                    steps.push(Step::Expr(lit));
                } else {
                    // Not `Literal`, so `lower_pattern` only records binders
                    // and never recurses — safe to call directly.
                    let pattern = lower_pattern(&c.pattern, table);
                    steps.push(Step::BuildClause {
                        pattern: Some(pattern),
                        has_guard: c.guard.is_some(),
                    });
                    steps.push(Step::Expr(&c.body));
                    if let Some(g) = &c.guard {
                        steps.push(Step::Expr(g));
                    }
                }
            }
            Step::BuildClause { pattern, has_guard } => {
                let body = results.pop().expect("clause body");
                let guard = if has_guard {
                    Some(results.pop().expect("clause guard"))
                } else {
                    None
                };
                let pattern = match pattern {
                    Some(p) => p,
                    None => NamelessPattern::Literal(results.pop().expect("clause literal")),
                };
                clause_results.push(NamelessClause {
                    pattern,
                    guard,
                    body,
                });
            }
            Step::Build(b) => {
                let node = match b {
                    Build::Lambda { params } => {
                        let body = results.pop().expect("lambda body");
                        NamelessExpr::Lambda {
                            params: params.iter().map(|p| p.id).collect(),
                            body: Box::new(body),
                        }
                    }
                    Build::RecFn { name, params } => {
                        let body = results.pop().expect("recfn body");
                        NamelessExpr::RecFn {
                            name: name.id,
                            params: params.iter().map(|p| p.id).collect(),
                            body: Box::new(body),
                        }
                    }
                    Build::Apply { nargs } => {
                        let args = take_n(&mut results, nargs);
                        let function = results.pop().expect("apply function");
                        NamelessExpr::Apply {
                            function: Box::new(function),
                            args,
                        }
                    }
                    Build::Let { id } => {
                        let body = results.pop().expect("let body");
                        let value = results.pop().expect("let value");
                        NamelessExpr::Let {
                            binder: id,
                            value: Box::new(value),
                            body: Box::new(body),
                        }
                    }
                    Build::If => {
                        let else_branch = results.pop().expect("if else");
                        let then_branch = results.pop().expect("if then");
                        let condition = results.pop().expect("if condition");
                        NamelessExpr::If {
                            condition: Box::new(condition),
                            then_branch: Box::new(then_branch),
                            else_branch: Box::new(else_branch),
                        }
                    }
                    Build::When {
                        subject_name,
                        nclauses,
                    } => {
                        let at = clause_results.len() - nclauses;
                        let clauses = clause_results.split_off(at);
                        let subject = results.pop().expect("when subject");
                        NamelessExpr::When {
                            subject: Box::new(subject),
                            subject_name,
                            clauses,
                        }
                    }
                    Build::List {
                        nelements,
                        has_tail,
                    } => {
                        let tail = if has_tail {
                            Some(Box::new(results.pop().expect("list tail")))
                        } else {
                            None
                        };
                        let elements = take_n(&mut results, nelements);
                        NamelessExpr::List { elements, tail }
                    }
                    Build::Tuple(n) => NamelessExpr::Tuple(take_n(&mut results, n)),
                    Build::Pair => {
                        let b = results.pop().expect("pair second");
                        let a = results.pop().expect("pair first");
                        NamelessExpr::Pair(Box::new(a), Box::new(b))
                    }
                    Build::Constr {
                        type_hint,
                        tag,
                        nfields,
                        shape,
                    } => {
                        let fields = take_n(&mut results, nfields);
                        NamelessExpr::Constr {
                            type_hint,
                            tag,
                            fields,
                            shape,
                        }
                    }
                    Build::FieldAccess { selector } => {
                        let record = results.pop().expect("field access record");
                        NamelessExpr::FieldAccess {
                            record: Box::new(record),
                            selector,
                        }
                    }
                    Build::IndexAccess { index } => {
                        let collection = results.pop().expect("index access collection");
                        NamelessExpr::IndexAccess {
                            collection: Box::new(collection),
                            index,
                        }
                    }
                    Build::BinOp { op } => {
                        let right = results.pop().expect("binop right");
                        let left = results.pop().expect("binop left");
                        NamelessExpr::BinOp {
                            op,
                            left: Box::new(left),
                            right: Box::new(right),
                        }
                    }
                    Build::UnOp { op } => {
                        let operand = results.pop().expect("unop operand");
                        NamelessExpr::UnOp {
                            op,
                            operand: Box::new(operand),
                        }
                    }
                    Build::BuiltinCall { name, nargs } => {
                        let args = take_n(&mut results, nargs);
                        NamelessExpr::BuiltinCall { name, args }
                    }
                    Build::Delay => {
                        let inner = results.pop().expect("delay inner");
                        NamelessExpr::Delay(Box::new(inner))
                    }
                    Build::Force => {
                        let inner = results.pop().expect("force inner");
                        NamelessExpr::Force(Box::new(inner))
                    }
                    Build::Trace => {
                        let value = results.pop().expect("trace value");
                        let message = results.pop().expect("trace message");
                        NamelessExpr::Trace {
                            message: Box::new(message),
                            value: Box::new(value),
                        }
                    }
                };
                results.push(node);
            }
        }
    }

    debug_assert_eq!(results.len(), 1, "the lower machine must leave one result");
    debug_assert!(clause_results.is_empty(), "all clauses must be consumed");
    results.pop().expect("lower result")
}

fn lower_pattern(pattern: &PseudoWhenPattern, table: &mut VarTable) -> NamelessPattern {
    match pattern {
        PseudoWhenPattern::Wildcard => NamelessPattern::Wildcard,
        PseudoWhenPattern::Var(b) => {
            record_binder(table, b);
            NamelessPattern::Var(b.id)
        }
        PseudoWhenPattern::Literal(lit) => NamelessPattern::Literal(lower(lit, table)),
        PseudoWhenPattern::Constructor {
            type_hint,
            tag,
            fields,
            shape,
        } => {
            for f in fields {
                record_binder(table, f);
            }
            NamelessPattern::Constructor {
                type_hint: type_hint.clone(),
                tag: *tag,
                fields: fields.iter().map(|b| b.id).collect(),
                shape: *shape,
            }
        }
        PseudoWhenPattern::List { elements, tail } => {
            for e in elements {
                record_binder(table, e);
            }
            if let Some(t) = tail {
                record_binder(table, t);
            }
            NamelessPattern::List {
                elements: elements.iter().map(|b| b.id).collect(),
                tail: tail.as_ref().map(|b| b.id),
            }
        }
        PseudoWhenPattern::Tuple(fields) => {
            for f in fields {
                record_binder(table, f);
            }
            NamelessPattern::Tuple(fields.iter().map(|b| b.id).collect())
        }
        PseudoWhenPattern::Pair(a, b) => {
            record_binder(table, a);
            record_binder(table, b);
            NamelessPattern::Pair(a.id, b.id)
        }
    }
}

// =============================================================
// nameless_to_pseudo
// =============================================================

/// Convert a [`NamelessExpr`] back to `PseudoExpr`, reading render
/// names from the [`VarTable`].
///
/// A `VarId` with no table entry renders as synthetic `v_<id>` —
/// a degraded bridge for hand-built or corrupt nameless trees.
/// `pseudo_to_nameless` records every id raising needs, so the
/// canonical path never hits it.
pub(crate) fn nameless_to_pseudo(expr: &NamelessExpr, table: &VarTable) -> PseudoExpr {
    raise(expr, table)
}

/// Resolve the display name for a nameless id while raising back to
/// `PseudoExpr`.
///
/// A missing table entry renders as `v_<id>` rather than panicking, so a
/// corrupt tree stays inspectable.
fn name_for(id: VarId, table: &VarTable) -> String {
    table
        .get(id)
        .and_then(|m| m.render_name_hint().map(str::to_string))
        .unwrap_or_else(|| format!("v_{}", id_raw(id)))
}

fn id_raw(id: VarId) -> u32 {
    // VarId(u32). Stable raw value used only for synthesizing
    // a placeholder name when the table has no hint.
    let s = format!("{:?}", id);

    s.trim_start_matches("VarId(")
        .trim_end_matches(')')
        .parse::<u32>()
        .unwrap_or(0)
}

fn raise(expr: &NamelessExpr, table: &VarTable) -> PseudoExpr {
    enum Step<'e> {
        Expr(&'e NamelessExpr),
        Clause(&'e NamelessClause),
        Build(Build<'e>),
        BuildClause {
            /// `None` when the pattern was `Literal`, whose raised form is
            /// the bottom-most of this clause's `results` entries.
            pattern: Option<PseudoWhenPattern>,
            has_guard: bool,
        },
    }

    enum Build<'e> {
        Lambda {
            params: &'e [VarId],
        },
        RecFn {
            name: VarId,
            params: &'e [VarId],
        },
        Apply {
            nargs: usize,
        },
        Let {
            binder: VarId,
        },
        If,
        When {
            subject_name: Option<VarId>,
            nclauses: usize,
        },
        List {
            nelements: usize,
            has_tail: bool,
        },
        Tuple(usize),
        Pair,
        Constr {
            type_hint: Option<TypeHintId>,
            tag: usize,
            nfields: usize,
            shape: ConstructorShape,
        },
        FieldAccess {
            selector: FieldSelector,
        },
        IndexAccess {
            index: usize,
        },
        BinOp {
            op: BinaryOp,
        },
        UnOp {
            op: UnaryOp,
        },
        BuiltinCall {
            name: BuiltinId,
            nargs: usize,
        },
        Delay,
        Force,
        Trace,
    }

    fn take_n(results: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
        let at = results.len() - n;
        results.split_off(at)
    }

    let mut steps: Vec<Step> = vec![Step::Expr(expr)];
    let mut results: Vec<PseudoExpr> = Vec::new();
    let mut clause_results: Vec<PseudoWhenClause> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Expr(e) => match e {
                NamelessExpr::Int(n) => results.push(PseudoExpr::Int(n.clone())),
                NamelessExpr::ByteArray(b) => results.push(PseudoExpr::ByteArray(b.clone())),
                NamelessExpr::String(s) => results.push(PseudoExpr::String(s.clone())),
                NamelessExpr::Bool(b) => results.push(PseudoExpr::Bool(*b)),
                NamelessExpr::Unit => results.push(PseudoExpr::Unit),
                NamelessExpr::Var(id) => results.push(PseudoExpr::Var {
                    name: name_for(*id, table),
                    id: Some(*id),
                }),
                NamelessExpr::Lambda { params, body } => {
                    steps.push(Step::Build(Build::Lambda { params }));
                    steps.push(Step::Expr(body));
                }
                NamelessExpr::RecFn { name, params, body } => {
                    steps.push(Step::Build(Build::RecFn {
                        name: *name,
                        params,
                    }));
                    steps.push(Step::Expr(body));
                }
                NamelessExpr::Apply { function, args } => {
                    steps.push(Step::Build(Build::Apply { nargs: args.len() }));
                    for a in args.iter().rev() {
                        steps.push(Step::Expr(a));
                    }
                    steps.push(Step::Expr(function));
                }
                NamelessExpr::Let {
                    binder,
                    value,
                    body,
                } => {
                    steps.push(Step::Build(Build::Let { binder: *binder }));
                    steps.push(Step::Expr(body));
                    steps.push(Step::Expr(value));
                }
                NamelessExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(Step::Build(Build::If));
                    steps.push(Step::Expr(else_branch));
                    steps.push(Step::Expr(then_branch));
                    steps.push(Step::Expr(condition));
                }
                NamelessExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    steps.push(Step::Build(Build::When {
                        subject_name: *subject_name,
                        nclauses: clauses.len(),
                    }));
                    for c in clauses.iter().rev() {
                        steps.push(Step::Clause(c));
                    }
                    steps.push(Step::Expr(subject));
                }
                NamelessExpr::List { elements, tail } => {
                    steps.push(Step::Build(Build::List {
                        nelements: elements.len(),
                        has_tail: tail.is_some(),
                    }));
                    if let Some(t) = tail {
                        steps.push(Step::Expr(t));
                    }
                    for e in elements.iter().rev() {
                        steps.push(Step::Expr(e));
                    }
                }
                NamelessExpr::Tuple(items) => {
                    steps.push(Step::Build(Build::Tuple(items.len())));
                    for i in items.iter().rev() {
                        steps.push(Step::Expr(i));
                    }
                }
                NamelessExpr::Pair(a, b) => {
                    steps.push(Step::Build(Build::Pair));
                    steps.push(Step::Expr(b));
                    steps.push(Step::Expr(a));
                }
                NamelessExpr::Constr {
                    type_hint,
                    tag,
                    fields,
                    shape,
                } => {
                    steps.push(Step::Build(Build::Constr {
                        type_hint: type_hint.clone(),
                        tag: *tag,
                        nfields: fields.len(),
                        shape: *shape,
                    }));
                    for f in fields.iter().rev() {
                        steps.push(Step::Expr(f));
                    }
                }
                NamelessExpr::FieldAccess { record, selector } => {
                    steps.push(Step::Build(Build::FieldAccess {
                        selector: selector.clone(),
                    }));
                    steps.push(Step::Expr(record));
                }
                NamelessExpr::IndexAccess { collection, index } => {
                    steps.push(Step::Build(Build::IndexAccess { index: *index }));
                    steps.push(Step::Expr(collection));
                }
                NamelessExpr::BinOp { op, left, right } => {
                    steps.push(Step::Build(Build::BinOp { op: *op }));
                    steps.push(Step::Expr(right));
                    steps.push(Step::Expr(left));
                }
                NamelessExpr::UnOp { op, operand } => {
                    steps.push(Step::Build(Build::UnOp { op: *op }));
                    steps.push(Step::Expr(operand));
                }
                NamelessExpr::BuiltinCall { name, args } => {
                    steps.push(Step::Build(Build::BuiltinCall {
                        name: *name,
                        nargs: args.len(),
                    }));
                    for a in args.iter().rev() {
                        steps.push(Step::Expr(a));
                    }
                }
                NamelessExpr::Error { message } => results.push(PseudoExpr::Error {
                    message: message.clone(),
                }),
                NamelessExpr::Delay(inner) => {
                    steps.push(Step::Build(Build::Delay));
                    steps.push(Step::Expr(inner));
                }
                NamelessExpr::Force(inner) => {
                    steps.push(Step::Build(Build::Force));
                    steps.push(Step::Expr(inner));
                }
                NamelessExpr::Trace { message, value } => {
                    steps.push(Step::Build(Build::Trace));
                    steps.push(Step::Expr(value));
                    steps.push(Step::Expr(message));
                }
                NamelessExpr::Raw { uplc, reason } => results.push(PseudoExpr::Raw {
                    uplc: uplc.clone(),
                    reason: reason.clone(),
                }),
                NamelessExpr::Data(d) => results.push(PseudoExpr::Data(d.clone())),
                NamelessExpr::HelperSymbol(intrinsic) => {
                    results.push(PseudoExpr::HelperSymbol(*intrinsic))
                }
            },
            Step::Clause(c) => {
                if let NamelessPattern::Literal(lit) = &c.pattern {
                    steps.push(Step::BuildClause {
                        pattern: None,
                        has_guard: c.guard.is_some(),
                    });
                    steps.push(Step::Expr(&c.body));
                    if let Some(g) = &c.guard {
                        steps.push(Step::Expr(g));
                    }
                    steps.push(Step::Expr(lit));
                } else {
                    // Not `Literal`, so `raise_pattern` never recurses —
                    // safe to call directly.
                    let pattern = raise_pattern(&c.pattern, table);
                    steps.push(Step::BuildClause {
                        pattern: Some(pattern),
                        has_guard: c.guard.is_some(),
                    });
                    steps.push(Step::Expr(&c.body));
                    if let Some(g) = &c.guard {
                        steps.push(Step::Expr(g));
                    }
                }
            }
            Step::BuildClause { pattern, has_guard } => {
                let body = results.pop().expect("clause body");
                let guard = if has_guard {
                    Some(results.pop().expect("clause guard"))
                } else {
                    None
                };
                let pattern = match pattern {
                    Some(p) => p,
                    None => PseudoWhenPattern::Literal(results.pop().expect("clause literal")),
                };
                clause_results.push(PseudoWhenClause {
                    pattern,
                    guard,
                    body,
                });
            }
            Step::Build(b) => {
                let node = match b {
                    Build::Lambda { params } => {
                        let body = results.pop().expect("lambda body");
                        PseudoExpr::Lambda {
                            params: params
                                .iter()
                                .map(|id| Binder::new(name_for(*id, table), *id))
                                .collect(),
                            body: PBox::new(body),
                        }
                    }
                    Build::RecFn { name, params } => {
                        let body = results.pop().expect("recfn body");
                        PseudoExpr::RecFn {
                            name: Binder::new(name_for(name, table), name),
                            params: params
                                .iter()
                                .map(|id| Binder::new(name_for(*id, table), *id))
                                .collect(),
                            body: PBox::new(body),
                        }
                    }
                    Build::Apply { nargs } => {
                        let args = take_n(&mut results, nargs);
                        let function = results.pop().expect("apply function");
                        PseudoExpr::Apply {
                            function: PBox::new(function),
                            args: args.into(),
                        }
                    }
                    Build::Let { binder } => {
                        let body = results.pop().expect("let body");
                        let value = results.pop().expect("let value");
                        PseudoExpr::Let {
                            name: name_for(binder, table),
                            id: Some(binder),
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    Build::If => {
                        let else_branch = results.pop().expect("if else");
                        let then_branch = results.pop().expect("if then");
                        let condition = results.pop().expect("if condition");
                        PseudoExpr::If {
                            condition: PBox::new(condition),
                            then_branch: PBox::new(then_branch),
                            else_branch: PBox::new(else_branch),
                        }
                    }
                    Build::When {
                        subject_name,
                        nclauses,
                    } => {
                        let at = clause_results.len() - nclauses;
                        let clauses = clause_results.split_off(at);
                        let subject = results.pop().expect("when subject");
                        PseudoExpr::When {
                            subject: PBox::new(subject),
                            subject_name: subject_name
                                .map(|id| Binder::new(name_for(id, table), id)),
                            clauses,
                        }
                    }
                    Build::List {
                        nelements,
                        has_tail,
                    } => {
                        let tail = if has_tail {
                            Some(PBox::new(results.pop().expect("list tail")))
                        } else {
                            None
                        };
                        let elements = take_n(&mut results, nelements);
                        PseudoExpr::List {
                            elements: elements.into(),
                            tail,
                        }
                    }
                    Build::Tuple(n) => PseudoExpr::Tuple((take_n(&mut results, n)).into()),
                    Build::Pair => {
                        let b = results.pop().expect("pair second");
                        let a = results.pop().expect("pair first");
                        PseudoExpr::Pair(PBox::new(a), PBox::new(b))
                    }
                    Build::Constr {
                        type_hint,
                        tag,
                        nfields,
                        shape,
                    } => {
                        let fields = take_n(&mut results, nfields);
                        PseudoExpr::Constr {
                            type_hint,
                            tag,
                            fields: fields.into(),
                            shape,
                        }
                    }
                    Build::FieldAccess { selector } => {
                        let record = results.pop().expect("field access record");
                        PseudoExpr::FieldAccess {
                            record: PBox::new(record),
                            selector,
                        }
                    }
                    Build::IndexAccess { index } => {
                        let collection = results.pop().expect("index access collection");
                        PseudoExpr::IndexAccess {
                            collection: PBox::new(collection),
                            index,
                        }
                    }
                    Build::BinOp { op } => {
                        let right = results.pop().expect("binop right");
                        let left = results.pop().expect("binop left");
                        PseudoExpr::BinOp {
                            op,
                            left: PBox::new(left),
                            right: PBox::new(right),
                        }
                    }
                    Build::UnOp { op } => {
                        let operand = results.pop().expect("unop operand");
                        PseudoExpr::UnOp {
                            op,
                            operand: PBox::new(operand),
                        }
                    }
                    Build::BuiltinCall { name, nargs } => {
                        let args = take_n(&mut results, nargs);
                        PseudoExpr::BuiltinCall {
                            name,
                            args: args.into(),
                        }
                    }
                    Build::Delay => {
                        let inner = results.pop().expect("delay inner");
                        PseudoExpr::Delay(PBox::new(inner))
                    }
                    Build::Force => {
                        let inner = results.pop().expect("force inner");
                        PseudoExpr::Force(PBox::new(inner))
                    }
                    Build::Trace => {
                        let value = results.pop().expect("trace value");
                        let message = results.pop().expect("trace message");
                        PseudoExpr::Trace {
                            message: PBox::new(message),
                            value: PBox::new(value),
                        }
                    }
                };
                results.push(node);
            }
        }
    }

    debug_assert_eq!(results.len(), 1, "the raise machine must leave one result");
    debug_assert!(clause_results.is_empty(), "all clauses must be consumed");
    results.pop().expect("raise result")
}

fn raise_pattern(pattern: &NamelessPattern, table: &VarTable) -> PseudoWhenPattern {
    match pattern {
        NamelessPattern::Wildcard => PseudoWhenPattern::Wildcard,
        NamelessPattern::Var(id) => PseudoWhenPattern::Var(Binder::new(name_for(*id, table), *id)),
        NamelessPattern::Literal(lit) => PseudoWhenPattern::Literal(raise(lit, table)),
        NamelessPattern::Constructor {
            type_hint,
            tag,
            fields,
            shape,
        } => PseudoWhenPattern::Constructor {
            type_hint: type_hint.clone(),
            tag: *tag,
            fields: fields
                .iter()
                .map(|id| Binder::new(name_for(*id, table), *id))
                .collect(),
            shape: *shape,
        },
        NamelessPattern::List { elements, tail } => PseudoWhenPattern::List {
            elements: elements
                .iter()
                .map(|id| Binder::new(name_for(*id, table), *id))
                .collect(),
            tail: tail.map(|id| Binder::new(name_for(id, table), id)),
        },
        NamelessPattern::Tuple(fields) => PseudoWhenPattern::Tuple(
            fields
                .iter()
                .map(|id| Binder::new(name_for(*id, table), *id))
                .collect(),
        ),
        NamelessPattern::Pair(a, b) => PseudoWhenPattern::Pair(
            Binder::new(name_for(*a, table), *a),
            Binder::new(name_for(*b, table), *b),
        ),
    }
}

// =============================================================
// Tests
// =============================================================

#[cfg(test)]
mod tests;
