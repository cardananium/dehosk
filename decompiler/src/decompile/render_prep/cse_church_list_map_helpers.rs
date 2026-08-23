//! CSE for alpha-equivalent church-list-map rec-fn helpers.
//!
//! After `lift_list_fold_to_when` rewrites the 4-arg CPS-identity
//! `List.fold` form, a let-bound church-list-map helper is a 1-param
//! `RecFn` whose `when` has `[] -> church_true` and
//! `church_cons(F(xs.head), self(xs[1..]))` in the cons arm. A
//! single let chain can hold several of these differing only in
//! synthesized binder names — structurally alpha-equivalent.
//!
//! Helpers in the same consecutive let chain that share a canonical
//! signature (cons-arm let chain, head op, and nil-arm name, with
//! `VarId`s replaced by placeholders) collapse onto the first: later
//! ones record a redirect `dup_id → canonical_id`, refs are rewritten
//! to the canonical name, and the redundant lets are dropped.
//!
//! Only that specific shape fires. Local-chain only — cross-scope
//! CSE would require lexical-scope analysis. The canonical helper's
//! binder name is preserved unchanged; only refs to the duplicates
//! are rewritten.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::BuiltinId;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

pub(super) fn cse_church_list_map_helpers(expr: PseudoExpr) -> PseudoExpr {
    let mut redirects: HashMap<VarId, (VarId, String)> = HashMap::new();
    collect_redirects(&expr, &mut redirects);
    if redirects.is_empty() {
        return expr;
    }
    apply_redirects(expr, &redirects)
}

/// In each consecutive Let chain, group church-list-map helpers
/// by signature and record a redirect for every duplicate.
fn collect_redirects(expr: &PseudoExpr, redirects: &mut HashMap<VarId, (VarId, String)>) {
    // Chains are scanned only at their head (parent is not a Let),
    // so descending into a Let body never re-processes a chain.
    process_chain(expr, redirects, true);
}

fn process_chain(
    expr: &PseudoExpr,
    redirects: &mut HashMap<VarId, (VarId, String)>,
    is_chain_head: bool,
) {
    let mut stack: Vec<(&PseudoExpr, bool)> = vec![(expr, is_chain_head)];
    while let Some((expr, is_chain_head)) = stack.pop() {
        match expr {
            PseudoExpr::Let { value, body, .. } => {
                if is_chain_head {
                    let mut helpers: Vec<(VarId, String, Signature)> = Vec::new();
                    let mut cur = expr;
                    while let PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } = cur
                    {
                        if let Some(vid) = id {
                            if let Some(sig) = church_list_map_signature(value) {
                                helpers.push((*vid, name.clone(), sig));
                            }
                        }
                        cur = body;
                    }
                    // Group by signature, redirect duplicates.
                    let mut by_sig: HashMap<Signature, (VarId, String)> = HashMap::new();
                    for (vid, name, sig) in helpers {
                        match by_sig.get(&sig) {
                            Some((canonical_vid, canonical_name)) => {
                                redirects.insert(vid, (*canonical_vid, canonical_name.clone()));
                            }
                            None => {
                                by_sig.insert(sig, (vid, name));
                            }
                        }
                    }
                }
                // The value subtree starts a fresh chain; the body
                // continues this one.
                stack.push((body, false));
                stack.push((value, true));
            }
            PseudoExpr::Lambda { body, .. } => stack.push((body, true)),
            PseudoExpr::RecFn { body, .. } => stack.push((body, true)),
            PseudoExpr::Apply { function, args } => {
                let mut seq: Vec<(&PseudoExpr, bool)> = vec![(function, true)];
                seq.extend(args.iter().map(|a| (a, true)));
                stack.extend(seq.into_iter().rev());
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                let mut seq: Vec<(&PseudoExpr, bool)> = vec![(subject, true)];
                for c in clauses {
                    if let Some(g) = &c.guard {
                        seq.push((g, true));
                    }
                    seq.push((&c.body, true));
                }
                stack.extend(seq.into_iter().rev());
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                stack.extend(
                    [
                        (condition.as_ref(), true),
                        (then_branch.as_ref(), true),
                        (else_branch.as_ref(), true),
                    ]
                    .into_iter()
                    .rev(),
                );
            }
            PseudoExpr::BinOp { left, right, .. } => {
                stack.push((right, true));
                stack.push((left, true));
            }
            PseudoExpr::UnOp { operand, .. } => stack.push((operand, true)),
            PseudoExpr::Constr { fields, .. } => {
                stack.extend(fields.iter().map(|f| (f, true)).rev());
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                stack.extend(args.iter().map(|a| (a, true)).rev());
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    stack.push((t, true));
                }
                stack.extend(elements.iter().map(|e| (e, true)).rev());
            }
            PseudoExpr::Tuple(elements) => {
                stack.extend(elements.iter().map(|e| (e, true)).rev());
            }
            PseudoExpr::Pair(a, b) => {
                stack.push((b, true));
                stack.push((a, true));
            }
            PseudoExpr::FieldAccess { record, .. } => stack.push((record, true)),
            PseudoExpr::IndexAccess { collection, .. } => stack.push((collection, true)),
            PseudoExpr::Trace { message, value } => {
                stack.push((value, true));
                stack.push((message, true));
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => stack.push((inner, true)),
            _ => {}
        }
    }
}

/// Signature key grouping alpha-equivalent church-list-map helpers:
/// the cons arm rendered with VarIds replaced by placeholders.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Signature(String);

/// Canonical signature if `value` is a church-list-map RecFn.
fn church_list_map_signature(value: &PseudoExpr) -> Option<Signature> {
    let PseudoExpr::RecFn { name, params, body } = value else {
        return None;
    };
    if params.len() != 1 {
        return None;
    }
    let arg_id = params[0].id;
    let self_id = name.id;
    let PseudoExpr::When {
        subject, clauses, ..
    } = body.as_ref()
    else {
        return None;
    };
    if !var_matches(subject, arg_id) {
        return None;
    }
    if clauses.len() != 2 {
        return None;
    }
    let (nil_idx, cons_idx) = match (
        is_nil_pattern(&clauses[0].pattern),
        is_nil_pattern(&clauses[1].pattern),
    ) {
        (true, false) => (0, 1),
        (false, true) => (1, 0),
        _ => return None,
    };
    let nil_arm = &clauses[nil_idx];
    let cons_arm = &clauses[cons_idx];
    // Nil arm must be a Var (typically `church_true`). Capture name.
    let nil_name = match &nil_arm.body {
        PseudoExpr::Var { name, .. } => name.clone(),
        _ => return None,
    };
    // Cons arm pattern must be `[_, ..]` (anonymous head + tail).
    let WhenPattern::List {
        elements: cons_els,
        tail: Some(_),
    } = &cons_arm.pattern
    else {
        return None;
    };
    if cons_els.len() != 1 {
        return None;
    }
    // Cons arm body: peel any leading Let bindings, then expect
    // `Apply(Var("church_cons"), [F, self_call])`.
    let mut let_chain: Vec<(VarId, &PseudoExpr)> = Vec::new();
    let mut cur = &cons_arm.body;
    while let PseudoExpr::Let {
        id: Some(vid),
        value,
        body,
        ..
    } = cur
    {
        let_chain.push((*vid, value.as_ref()));
        cur = body.as_ref();
    }
    let (cons_name, cons_args) = match cur {
        PseudoExpr::Apply { function, args } => match strip_forces(function) {
            PseudoExpr::Var { name, .. } => (name.clone(), args),
            _ => return None,
        },
        _ => return None,
    };
    if cons_name != "church_cons" {
        return None;
    }
    if cons_args.len() != 2 {
        return None;
    }
    // Recursive call: self(arg[1..])
    let PseudoExpr::Apply {
        function: rfn,
        args: rargs,
    } = &cons_args[1]
    else {
        return None;
    };
    if !var_matches(rfn, self_id) {
        return None;
    }
    if rargs.len() != 1 {
        return None;
    }
    if !is_list_tail_of(&rargs[0], arg_id) {
        return None;
    }
    // One Canonicaliser for every let binding and the final head-op,
    // so VarId placeholders stay consistent across the arm.
    let mut canon = Canonicaliser::new(arg_id, self_id);
    for (let_id, let_value) in &let_chain {
        canon.declare_let(*let_id);
        let placeholder = canon.placeholder_for_local(*let_id).to_string();
        canon.out.push_str("Let(");
        canon.out.push_str(&placeholder);
        canon.out.push_str(" = ");
        canon.visit(let_value);
        canon.out.push_str("); ");
    }
    canon.out.push_str("head_op=");
    canon.visit(&cons_args[0]);
    Some(Signature(format!("{} | nil={}", canon.out, nil_name)))
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

/// `arg[1..]` is `BuiltinCall { ListTail, [Var(arg)] }` OR
/// `Apply { function: BuiltinCall{ListTail,[]}, args: [Var(arg)] }`.
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

/// Stable string rendering of an expression with VarIds replaced
/// by deterministic placeholders: param and self get
/// `<ARG>`/`<SELF>`, let-bound ids sequential `<L0>`, `<L1>`, ….
/// Free VarIds keep their numeric id — outer-scope refs must be
/// identical across helpers to count as equivalent.
struct Canonicaliser {
    out: String,
    arg_id: VarId,
    self_id: VarId,
    /// Local let-binder VarIds → `<LN>` placeholders.
    locals: HashMap<VarId, String>,
}

impl Canonicaliser {
    fn new(arg_id: VarId, self_id: VarId) -> Self {
        Self {
            out: String::new(),
            arg_id,
            self_id,
            locals: HashMap::new(),
        }
    }

    fn declare_let(&mut self, vid: VarId) {
        let next = self.locals.len();
        self.locals
            .entry(vid)
            .or_insert_with(|| format!("<L{}>", next));
    }

    fn placeholder_for_local(&self, vid: VarId) -> &str {
        self.locals
            .get(&vid)
            .expect("local must be declared before lookup")
    }

    fn visit(&mut self, expr: &PseudoExpr) {
        use std::fmt::Write;

        enum VisitTask<'a> {
            Node(&'a PseudoExpr),
            Str(&'static str),
            Owned(String),
        }

        let mut pending: Vec<VisitTask> = vec![VisitTask::Node(expr)];
        while let Some(task) = pending.pop() {
            let expr = match task {
                VisitTask::Str(s) => {
                    self.out.push_str(s);
                    continue;
                }
                VisitTask::Owned(s) => {
                    self.out.push_str(&s);
                    continue;
                }
                VisitTask::Node(expr) => expr,
            };
            match expr {
                PseudoExpr::Var { id, name } => match id {
                    Some(v) if *v == self.arg_id => self.out.push_str("<ARG>"),
                    Some(v) if *v == self.self_id => self.out.push_str("<SELF>"),
                    Some(v) => {
                        if let Some(p) = self.locals.get(v).cloned() {
                            self.out.push_str(&p);
                        } else {
                            write!(self.out, "Var({:?})", v).unwrap();
                        }
                    }
                    None => write!(self.out, "VarN({})", name).unwrap(),
                },
                PseudoExpr::Apply { function, args } => {
                    let mut seq = vec![VisitTask::Str("Apply("), VisitTask::Node(function)];
                    seq.push(VisitTask::Str(", ["));
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            seq.push(VisitTask::Str(", "));
                        }
                        seq.push(VisitTask::Node(a));
                    }
                    seq.push(VisitTask::Str("])"));
                    pending.extend(seq.into_iter().rev());
                }
                PseudoExpr::BuiltinCall { name, args } => {
                    let mut seq = vec![VisitTask::Owned(format!("BC({:?}, [", name))];
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            seq.push(VisitTask::Str(", "));
                        }
                        seq.push(VisitTask::Node(a));
                    }
                    seq.push(VisitTask::Str("])"));
                    pending.extend(seq.into_iter().rev());
                }
                PseudoExpr::FieldAccess { record, selector } => {
                    let seq = vec![
                        VisitTask::Str("FA("),
                        VisitTask::Node(record),
                        VisitTask::Owned(format!(", {:?})", selector_tag(selector))),
                    ];
                    pending.extend(seq.into_iter().rev());
                }
                PseudoExpr::IndexAccess { collection, index } => {
                    let seq = vec![
                        VisitTask::Str("IA("),
                        VisitTask::Node(collection),
                        VisitTask::Owned(format!(", {})", index)),
                    ];
                    pending.extend(seq.into_iter().rev());
                }
                PseudoExpr::ByteArray(b) => write!(self.out, "BA({:?})", b).unwrap(),
                PseudoExpr::Int(n) => write!(self.out, "Int({})", n).unwrap(),
                PseudoExpr::Unit => self.out.push_str("Unit"),
                PseudoExpr::Bool(b) => write!(self.out, "Bool({})", b).unwrap(),
                other => write!(self.out, "OTHER({:?})", other).unwrap(),
            }
        }
    }
}

fn selector_tag(s: &FieldSelector) -> &'static str {
    match s {
        FieldSelector::PairFst => "fst",
        FieldSelector::PairSnd => "snd",
        FieldSelector::ListHead => "head",
        FieldSelector::ContextField(_) => "ctx",
        FieldSelector::NamedField(_) => "named",
    }
}

/// Walk the tree applying redirects: rewrite `Var { id: dup_id }` to
/// canonical, drop let-bindings whose id is in the redirect map.
fn apply_redirects(expr: PseudoExpr, redirects: &HashMap<VarId, (VarId, String)>) -> PseudoExpr {
    struct Redirector<'a> {
        redirects: &'a HashMap<VarId, (VarId, String)>,
    }

    impl ExprFolder for Redirector<'_> {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
            if let Some(v) = id {
                if let Some((canonical_id, canonical_name)) = self.redirects.get(&v) {
                    return PseudoExpr::Var {
                        name: canonical_name.clone(),
                        id: Some(*canonical_id),
                    };
                }
            }
            PseudoExpr::Var { name, id }
        }

        fn post_let(
            &mut self,
            name: String,
            id: Option<VarId>,
            value: PseudoExpr,
            body: PseudoExpr,
        ) -> PseudoExpr {
            // If this let's id is in the redirect map, drop it (the
            // body's refs to id were already rewritten to canonical
            // by `post_var`).
            if let Some(vid) = id {
                if self.redirects.contains_key(&vid) {
                    return body;
                }
            }
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }
    }

    Redirector { redirects }.fold(expr)
}

#[allow(dead_code)]
fn _unused_imports_placeholder(_b: Binder) {}
