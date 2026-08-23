//! CSE for alpha-equivalent let-bound helpers.
//!
//! Eligible values: `Lambda`, `RecFn`, `Pair`, `Tuple`, `Constr`,
//! `List`, `FieldAccess`, `IndexAccess`. `Apply` and effectful nodes
//! are excluded — dropping a duplicate would remove an evaluation
//! point.
//!
//! PlutusTx/GHC often duplicates one helper; naming then suffixes
//! copies `_N`. Signature: binders under the value become positional
//! placeholders; outer-scope `Var`s keep their VarId so helpers over
//! different captures do not merge. First of each group is canonical;
//! duplicate lets drop.
//!
//! Only let-bound values. A binder that re-binds a redirect key
//! shadows it, so a param sharing a dropped helper's VarId is not
//! redirected.

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::BuiltinId;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::type_hint::TypeHintId;
use crate::pseudo::var_id::VarId;

use super::purity::is_pure_value;
use super::scope_recurse::children;

pub(super) fn cse_alpha_equivalent_lambda_helpers(expr: PseudoExpr) -> PseudoExpr {
    // Iterate to fixpoint: merging one round's helpers makes
    // their outer-Var references identical, exposing further
    // alpha-equivalences in helpers that referenced the merged
    // duplicates. The cap bounds runtime.
    let mut cur = expr;
    for _ in 0..MAX_FIXPOINT_ITERATIONS {
        let mut redirects: HashMap<VarId, (VarId, String)> = HashMap::new();
        let mut drop_ids: HashSet<VarId> = HashSet::new();
        // Re-scanned each round so helpers merged in an earlier
        // round are seen. The arity is load-bearing: an
        // over-applied `pack_helper(a, …, n, k)` is a continuation
        // call — the helper returns `fn(x){x(a,…,n)}` and `k`
        // becomes that continuation — not a constructor literal.
        let mut pack_helpers: HashMap<VarId, usize> = HashMap::new();
        collect_pack_helper_ids(&cur, &mut pack_helpers);
        collect_redirects(&cur, &mut redirects, &mut drop_ids, true, &pack_helpers);
        if redirects.is_empty() {
            return cur;
        }
        cur = apply_redirects(cur, redirects, drop_ids);
    }
    cur
}

const MAX_FIXPOINT_ITERATIONS: usize = 8;

fn collect_redirects(
    expr: &PseudoExpr,
    redirects: &mut HashMap<VarId, (VarId, String)>,
    drop_ids: &mut HashSet<VarId>,
    is_chain_head: bool,
    pack_helpers: &HashMap<VarId, usize>,
) {
    let mut pending: Vec<(&PseudoExpr, bool)> = vec![(expr, is_chain_head)];
    while let Some((cur, chain_head)) = pending.pop() {
        if let PseudoExpr::Let { .. } = cur {
            if chain_head {
                process_chain(cur, redirects, drop_ids, pack_helpers);
            }
            // Each Let value, and the chain tail, is its own chain head.
            let mut chain_items: Vec<&PseudoExpr> = Vec::new();
            let mut chain_cur = cur;
            while let PseudoExpr::Let { value, body, .. } = chain_cur {
                chain_items.push(value);
                chain_cur = body;
            }
            chain_items.push(chain_cur);
            for item in chain_items.into_iter().rev() {
                pending.push((item, true));
            }
            continue;
        }
        // Non-Let: recurse into all children as fresh chain heads.
        for c in children(cur).into_iter().rev() {
            pending.push((c, true));
        }
    }
}

fn process_chain(
    chain_head: &PseudoExpr,
    redirects: &mut HashMap<VarId, (VarId, String)>,
    drop_ids: &mut HashSet<VarId>,
    pack_helpers: &HashMap<VarId, usize>,
) {
    // Collect (VarId, name, signature) for every CSE-eligible let
    // in the chain; `cse_eligible_signature` decides eligibility.
    let mut helpers: Vec<(VarId, String, String)> = Vec::new();
    let mut cur = chain_head;
    while let PseudoExpr::Let {
        name,
        id,
        value,
        body,
    } = cur
    {
        if let Some(vid) = id {
            if let Some(sig) = cse_eligible_signature(value.as_ref(), pack_helpers) {
                helpers.push((*vid, name.clone(), sig));
            }
        }
        cur = body;
    }
    // Group by signature, pick first as canonical, redirect dups.
    let mut canonicals: HashMap<String, (VarId, String)> = HashMap::new();
    for (vid, name, sig) in helpers {
        match canonicals.get(&sig) {
            Some((canonical_vid, canonical_name)) => {
                redirects.insert(vid, (*canonical_vid, canonical_name.clone()));
                drop_ids.insert(vid);
            }
            None => {
                canonicals.insert(sig, (vid, name));
            }
        }
    }
}

/// Classify a let-value as CSE-eligible and return its alpha-canonical
/// signature. Eligible:
///
/// - `Lambda`; `RecFn` too, with the self-name binder declared first
///   in the placeholder pool so internal self-calls compare by
///   position instead of VarId.
/// - `Pair`, `Tuple`, `Constr`, `List` constructions and
///   `FieldAccess` / `IndexAccess` projections.
/// - `Apply { function: Var(pack_helper), args: [pure ..] }` where
///   `pack_helper` is a validated church-pack-N constructor (see
///   `collect_pack_helper_ids`): the Apply yields a Lambda value with
///   no other observable effect, so two identical applications dedupe
///   exactly like a constructor literal.
///
/// Excluded: any other `Apply`, `When`, `If`, `Trace`, `Error`, `Let`,
/// `BuiltinCall`, `BinOp`, `UnOp`, `Force`, `Delay` — these either
/// carry per-occurrence semantics or are not value-shaped.
fn cse_eligible_signature(
    value: &PseudoExpr,
    pack_helpers: &HashMap<VarId, usize>,
) -> Option<String> {
    match value {
        PseudoExpr::Lambda { params, body } => Some(canonical_signature(params, body)),
        PseudoExpr::RecFn { name, params, body } => {
            Some(canonical_recfn_signature(name, params, body))
        }
        PseudoExpr::Pair(_, _)
        | PseudoExpr::Tuple(_)
        | PseudoExpr::Constr { .. }
        | PseudoExpr::List { .. }
        | PseudoExpr::FieldAccess { .. }
        | PseudoExpr::IndexAccess { .. } => {
            let mut canon = Canonicaliser::new();
            canon.visit(value);
            Some(canon.out)
        }
        PseudoExpr::Apply { function, args } => {
            let PseudoExpr::Var { id: Some(v), .. } = function.as_ref() else {
                return None;
            };
            // Exact arity only: `pack_helper(a, …, n, k)` is a
            // continuation call (`k(a, …, n)`), not a constructor
            // literal, so dropping a duplicate would lose an
            // observable evaluation of `k`; under-application is a
            // curried Lambda, not the shape being deduped.
            let arity = pack_helpers.get(v)?;
            if args.len() != *arity {
                return None;
            }
            // Every arg must be discardable: dropping the duplicate
            // Let must not lose an evaluation point.
            if !args.iter().all(is_pure_value) {
                return None;
            }
            let mut canon = Canonicaliser::new();
            canon.visit(value);
            Some(canon.out)
        }
        _ => None,
    }
}

/// Scan `expr` for let-bound helpers whose value matches the
/// church-pack-N constructor shape:
///
/// ```text
/// fn(a1, …, aN) { fn(x) { x(a1, …, aN) } }    // N >= 2
/// ```
///
/// Such a helper is a pure constructor closure: applying it to
/// exactly N arguments produces a Lambda value with no side
/// effects, failure modes, or traces, so those applications CSE
/// like a `Pair(…)` literal — provided the arguments are themselves
/// pure, which `cse_eligible_signature` checks.
///
/// Returns `VarId → exact arity` so the caller can reject
/// over-application (a continuation call) and under-application (a
/// partially applied curried form).
fn collect_pack_helper_ids(expr: &PseudoExpr, out: &mut HashMap<VarId, usize>) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::Let {
            id: Some(vid),
            value,
            ..
        } = cur
        {
            if let Some(arity) = pack_helper_arity(value) {
                out.insert(*vid, arity);
            }
        }
        pending.extend(children(cur));
    }
}

/// Boolean wrapper around [`pack_helper_arity`] for tests.
#[cfg(test)]
fn matches_pack_helper(value: &PseudoExpr) -> bool {
    pack_helper_arity(value).is_some()
}

/// Returns `Some(N)` iff `value` is shaped like a church-pack-N
/// constructor: an outer Lambda of arity N (≥2) whose body is an
/// arity-1 Lambda whose body is `x(a1, …, aN)`, where `x` is the
/// inner param and `a_i` are the outer params in that exact order
/// — a permuted or short arg list is rejected.
fn pack_helper_arity(value: &PseudoExpr) -> Option<usize> {
    let PseudoExpr::Lambda {
        params: outer_params,
        body: outer_body,
    } = value
    else {
        return None;
    };
    if outer_params.len() < 2 {
        return None;
    }
    let PseudoExpr::Lambda {
        params: inner_params,
        body: inner_body,
    } = outer_body.as_ref()
    else {
        return None;
    };
    if inner_params.len() != 1 {
        return None;
    }
    let x_id = inner_params[0].id;
    let PseudoExpr::Apply { function, args } = inner_body.as_ref() else {
        return None;
    };
    match function.as_ref() {
        PseudoExpr::Var { id: Some(v), .. } if *v == x_id => {}
        _ => return None,
    }
    if args.len() != outer_params.len() {
        return None;
    }
    for (arg, param) in args.iter().zip(outer_params.iter()) {
        match arg {
            PseudoExpr::Var { id: Some(v), .. } if *v == param.id => {}
            _ => return None,
        }
    }
    Some(outer_params.len())
}

/// Compute the alpha-canonical signature of a Lambda body: the
/// Lambda's own params become positional placeholders (`<L0>`,
/// `<L1>`, …), binders from inner `Let` / `Lambda` / `RecFn` /
/// `When` patterns take further placeholders in encounter order,
/// and outer Var refs keep their VarId numerically.
fn canonical_signature(params: &[Binder], body: &PseudoExpr) -> String {
    let mut canon = Canonicaliser::new();
    for p in params {
        canon.declare_local(p.id);
    }
    canon.out.push_str("Lambda(");
    canon.out.push_str(&format!("arity={}", params.len()));
    canon.out.push_str(", body=");
    canon.visit(body);
    canon.out.push(')');
    canon.out
}

/// Alpha-canonical signature for a let-bound `RecFn`. The self-name
/// binder is declared first in the placeholder pool so internal
/// self-calls compare positionally; params follow. Equal signatures
/// mean equal arity, equal body shape after alpha-renaming, and
/// equal outer captures — a free `Var` keeps its raw `OV(VarId)` /
/// `VN(name)` token.
///
/// The `RecFn(` prefix keeps these signatures disjoint from
/// `Lambda(`-prefixed ones, so a Lambda never matches a RecFn whose
/// body canonicalises the same way.
fn canonical_recfn_signature(name: &Binder, params: &[Binder], body: &PseudoExpr) -> String {
    let mut canon = Canonicaliser::new();
    canon.declare_local(name.id);
    for p in params {
        canon.declare_local(p.id);
    }
    canon.out.push_str("RecFn(");
    canon.out.push_str(&format!("arity={}", params.len()));
    canon.out.push_str(", body=");
    canon.visit(body);
    canon.out.push(')');
    canon.out
}

struct Canonicaliser {
    out: String,
    locals: HashMap<VarId, String>,
}

impl Canonicaliser {
    fn new() -> Self {
        Self {
            out: String::new(),
            locals: HashMap::new(),
        }
    }

    fn declare_local(&mut self, vid: VarId) -> String {
        let next = self.locals.len();
        let ph = format!("<L{}>", next);
        self.locals.entry(vid).or_insert(ph.clone());
        ph
    }

    /// Emit the alpha-canonical signature of `expr`.
    ///
    /// The literal text a node emits AROUND its children (separators,
    /// closing parens) is queued as its own `Text`/`Owned` instruction
    /// here, and children are
    /// pushed in REVERSE so they pop in source order. `declare_local`
    /// hands out placeholders in encounter order, so every declare stays
    /// on the ENTER side, before the node's children are queued.
    fn visit(&mut self, expr: &PseudoExpr) {
        use std::fmt::Write;

        enum Instr<'a> {
            Text(&'static str),
            Owned(String),
            Visit(&'a PseudoExpr),
            Clause(&'a WhenClause),
            Pattern(&'a WhenPattern),
        }

        let mut stack: Vec<Instr> = vec![Instr::Visit(expr)];
        while let Some(instr) = stack.pop() {
            match instr {
                Instr::Text(s) => self.out.push_str(s),
                Instr::Owned(s) => self.out.push_str(&s),
                Instr::Visit(node) => match node {
                    PseudoExpr::Var { id, name } => match id {
                        Some(v) => {
                            if let Some(p) = self.locals.get(v).cloned() {
                                self.out.push_str(&p);
                            } else {
                                write!(self.out, "OV({:?})", v).unwrap();
                            }
                        }
                        None => write!(self.out, "VN({})", name).unwrap(),
                    },
                    PseudoExpr::Let {
                        id, value, body, ..
                    } => {
                        self.out.push_str("Let(");
                        if let Some(vid) = id {
                            let ph = self.declare_local(*vid);
                            self.out.push_str(&ph);
                        } else {
                            self.out.push_str("<?>");
                        }
                        self.out.push_str(", v=");
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(body));
                        stack.push(Instr::Text(", b="));
                        stack.push(Instr::Visit(value));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        self.out.push_str("Lam([");
                        for (i, p) in params.iter().enumerate() {
                            if i > 0 {
                                self.out.push(',');
                            }
                            let ph = self.declare_local(p.id);
                            self.out.push_str(&ph);
                        }
                        self.out.push_str("],");
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(body));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        self.out.push_str("RFn(");
                        let n_ph = self.declare_local(name.id);
                        self.out.push_str(&n_ph);
                        self.out.push_str(",[");
                        for (i, p) in params.iter().enumerate() {
                            if i > 0 {
                                self.out.push(',');
                            }
                            let ph = self.declare_local(p.id);
                            self.out.push_str(&ph);
                        }
                        self.out.push_str("],");
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(body));
                    }
                    PseudoExpr::Apply { function, args } => {
                        self.out.push_str("Ap(");
                        stack.push(Instr::Text("])"));
                        for (i, a) in args.iter().enumerate().rev() {
                            stack.push(Instr::Visit(a));
                            if i > 0 {
                                stack.push(Instr::Text(","));
                            }
                        }
                        stack.push(Instr::Text(",["));
                        stack.push(Instr::Visit(function));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        self.out.push_str("If(");
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(else_branch));
                        stack.push(Instr::Text(","));
                        stack.push(Instr::Visit(then_branch));
                        stack.push(Instr::Text(","));
                        stack.push(Instr::Visit(condition));
                    }
                    PseudoExpr::When {
                        subject, clauses, ..
                    } => {
                        self.out.push_str("Wh(");
                        stack.push(Instr::Text("])"));
                        for (i, c) in clauses.iter().enumerate().rev() {
                            stack.push(Instr::Clause(c));
                            if i > 0 {
                                stack.push(Instr::Text(","));
                            }
                        }
                        stack.push(Instr::Text(",["));
                        stack.push(Instr::Visit(subject));
                    }
                    PseudoExpr::Constr {
                        tag,
                        fields,
                        shape,
                        type_hint,
                    } => {
                        // Include `shape` and `type_hint`: two same-tag
                        // Constrs whose shapes differ (`Known(Some)` vs
                        // `Unknown { tag: 1, arity: 1 }`) must get
                        // DIFFERENT signatures, or merging collapses a
                        // distinction the renderer still makes.
                        write!(self.out, "Co({},sh={:?},th={:?}", tag, shape, type_hint).unwrap();
                        self.out.push_str(",[");
                        stack.push(Instr::Text("])"));
                        for (i, f) in fields.iter().enumerate().rev() {
                            stack.push(Instr::Visit(f));
                            if i > 0 {
                                stack.push(Instr::Text(","));
                            }
                        }
                    }
                    PseudoExpr::FieldAccess { record, selector } => {
                        self.out.push_str("FA(");
                        stack.push(Instr::Owned(format!(",{:?})", selector)));
                        stack.push(Instr::Visit(record));
                    }
                    PseudoExpr::IndexAccess { collection, index } => {
                        self.out.push_str("IA(");
                        stack.push(Instr::Owned(format!(",{})", index)));
                        stack.push(Instr::Visit(collection));
                    }
                    PseudoExpr::BinOp { op, left, right } => {
                        write!(self.out, "BO({:?},", op).unwrap();
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(right));
                        stack.push(Instr::Text(","));
                        stack.push(Instr::Visit(left));
                    }
                    PseudoExpr::UnOp { op, operand } => {
                        write!(self.out, "UO({:?},", op).unwrap();
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(operand));
                    }
                    PseudoExpr::BuiltinCall { name, args } => {
                        write!(self.out, "BC({:?},[", name).unwrap();
                        stack.push(Instr::Text("])"));
                        for (i, a) in args.iter().enumerate().rev() {
                            stack.push(Instr::Visit(a));
                            if i > 0 {
                                stack.push(Instr::Text(","));
                            }
                        }
                    }
                    PseudoExpr::List { elements, tail } => {
                        self.out.push_str("L([");
                        stack.push(Instr::Text(")"));
                        match tail {
                            Some(t) => stack.push(Instr::Visit(t)),
                            None => stack.push(Instr::Text("nil")),
                        }
                        stack.push(Instr::Text("],"));
                        for (i, e) in elements.iter().enumerate().rev() {
                            stack.push(Instr::Visit(e));
                            if i > 0 {
                                stack.push(Instr::Text(","));
                            }
                        }
                    }
                    PseudoExpr::Tuple(items) => {
                        self.out.push_str("Tup([");
                        stack.push(Instr::Text("])"));
                        for (i, it) in items.iter().enumerate().rev() {
                            stack.push(Instr::Visit(it));
                            if i > 0 {
                                stack.push(Instr::Text(","));
                            }
                        }
                    }
                    PseudoExpr::Pair(a, b) => {
                        self.out.push_str("Pr(");
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(b));
                        stack.push(Instr::Text(","));
                        stack.push(Instr::Visit(a));
                    }
                    PseudoExpr::Delay(inner) => {
                        self.out.push_str("D(");
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(inner));
                    }
                    PseudoExpr::Force(inner) => {
                        self.out.push_str("F(");
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(inner));
                    }
                    PseudoExpr::Trace { message, value } => {
                        self.out.push_str("Tr(");
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(value));
                        stack.push(Instr::Text(","));
                        stack.push(Instr::Visit(message));
                    }
                    PseudoExpr::Int(n) => write!(self.out, "I({})", n).unwrap(),
                    PseudoExpr::ByteArray(b) => write!(self.out, "BA({:?})", b).unwrap(),
                    PseudoExpr::String(s) => write!(self.out, "S({:?})", s).unwrap(),
                    PseudoExpr::Bool(b) => write!(self.out, "B({})", b).unwrap(),
                    PseudoExpr::Unit => self.out.push('U'),
                    PseudoExpr::Error { message } => {
                        write!(self.out, "Err({:?})", message).unwrap()
                    }
                    PseudoExpr::Raw { .. } => self.out.push_str("Raw"),
                    PseudoExpr::Data(_) => self.out.push_str("Data"),
                    PseudoExpr::HelperSymbol(s) => write!(self.out, "Hs({:?})", s).unwrap(),
                },
                // `visit_clause`, unrolled: the pattern's binders are
                // declared before the guard and body are visited.
                Instr::Clause(clause) => {
                    self.out.push('(');
                    stack.push(Instr::Text(")"));
                    stack.push(Instr::Visit(&clause.body));
                    stack.push(Instr::Text(",b="));
                    if let Some(g) = &clause.guard {
                        stack.push(Instr::Visit(g));
                        stack.push(Instr::Text(",g="));
                    }
                    stack.push(Instr::Pattern(&clause.pattern));
                }
                // `visit_pattern`, unrolled. Only `Literal` has a child
                // expression; every other arm is pure declares and text.
                Instr::Pattern(p) => match p {
                    WhenPattern::Constructor { tag, fields, .. } => {
                        write!(self.out, "C{}(", tag).unwrap();
                        for (i, f) in fields.iter().enumerate() {
                            if i > 0 {
                                self.out.push(',');
                            }
                            let ph = self.declare_local(f.id);
                            self.out.push_str(&ph);
                        }
                        self.out.push(')');
                    }
                    WhenPattern::List { elements, tail } => {
                        self.out.push_str("L[");
                        for (i, e) in elements.iter().enumerate() {
                            if i > 0 {
                                self.out.push(',');
                            }
                            let ph = self.declare_local(e.id);
                            self.out.push_str(&ph);
                        }
                        if let Some(t) = tail {
                            self.out.push_str(",..");
                            let ph = self.declare_local(t.id);
                            self.out.push_str(&ph);
                        }
                        self.out.push(']');
                    }
                    WhenPattern::Tuple(fs) => {
                        self.out.push_str("Tup[");
                        for (i, f) in fs.iter().enumerate() {
                            if i > 0 {
                                self.out.push(',');
                            }
                            let ph = self.declare_local(f.id);
                            self.out.push_str(&ph);
                        }
                        self.out.push(']');
                    }
                    WhenPattern::Pair(a, b) => {
                        self.out.push_str("P[");
                        let pa = self.declare_local(a.id);
                        self.out.push_str(&pa);
                        self.out.push(',');
                        let pb = self.declare_local(b.id);
                        self.out.push_str(&pb);
                        self.out.push(']');
                    }
                    WhenPattern::Wildcard => self.out.push('_'),
                    WhenPattern::Literal(e) => {
                        self.out.push_str("Lit(");
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(e));
                    }
                    WhenPattern::Var(b) => {
                        self.out.push_str("Var[");
                        let ph = self.declare_local(b.id);
                        self.out.push_str(&ph);
                        self.out.push(']');
                    }
                },
            }
        }
    }
}

/// When a scope re-binds VarIds that are redirect KEYS (a binder sharing a
/// VarId with a dropped helper), return a copy of `redirects` with those
/// keys removed, so references inside that scope — which denote the NEW
/// binding, not the helper — are left untouched. `None` means reuse the
/// original map: no bound id is a key, the common case.
fn shadow_redirects(
    redirects: &HashMap<VarId, (VarId, String)>,
    bound: impl IntoIterator<Item = VarId>,
) -> Option<HashMap<VarId, (VarId, String)>> {
    let shadowed: Vec<VarId> = bound
        .into_iter()
        .filter(|b| redirects.contains_key(b))
        .collect();
    if shadowed.is_empty() {
        return None;
    }
    let mut m = redirects.clone();
    for b in shadowed {
        m.remove(&b);
    }
    Some(m)
}

fn apply_redirects(
    expr: PseudoExpr,
    redirects: HashMap<VarId, (VarId, String)>,
    drop_ids: HashSet<VarId>,
) -> PseudoExpr {
    type Redirects = Rc<HashMap<VarId, (VarId, String)>>;

    enum PendingPattern {
        Literal,
        Other(WhenPattern),
    }

    enum PostKind {
        Let {
            name: String,
            id: Option<VarId>,
        },
        Lambda {
            params: Vec<Binder>,
        },
        RecFn {
            name: Binder,
            params: Vec<Binder>,
        },
        Apply {
            argc: usize,
        },
        If,
        When {
            subject_name: Option<Binder>,
            clause_count: usize,
        },
        Clause {
            pattern: PendingPattern,
            has_guard: bool,
        },
        List {
            count: usize,
            has_tail: bool,
        },
        Tuple {
            count: usize,
        },
        Pair,
        Constr {
            type_hint: Option<TypeHintId>,
            tag: usize,
            shape: ConstructorShape,
            count: usize,
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
            argc: usize,
        },
        Delay,
        Force,
        Trace,
    }

    enum Step {
        Enter {
            expr: PseudoExpr,
            redirects: Redirects,
        },
        Post(PostKind),
    }

    // Mirrors `shadow_redirects`, but returns an owned `Rc`: `Some` (a
    // binder shadowed a redirect key) allocates a new map; the common `None`
    // case just bumps the refcount on the map already in scope.
    fn child_redirects(redirects: &Redirects, bound: impl IntoIterator<Item = VarId>) -> Redirects {
        match shadow_redirects(redirects, bound) {
            Some(m) => Rc::new(m),
            None => Rc::clone(redirects),
        }
    }

    fn take(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
        let at = done.len() - n;
        done.split_off(at)
    }

    let redirects: Redirects = Rc::new(redirects);
    let drop_ids = Rc::new(drop_ids);

    let mut steps: Vec<Step> = vec![Step::Enter { expr, redirects }];
    let mut done: Vec<PseudoExpr> = Vec::new();
    let mut done_clauses: Vec<WhenClause> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Enter { expr, redirects } => match expr {
                PseudoExpr::Var { name, id } => {
                    let result = if let Some(v) = id
                        && let Some((canonical_id, canonical_name)) = redirects.get(&v)
                    {
                        PseudoExpr::Var {
                            name: canonical_name.clone(),
                            id: Some(*canonical_id),
                        }
                    } else {
                        PseudoExpr::Var { name, id }
                    };
                    done.push(result);
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    // Drop dup helper lets — their value isn't needed anymore.
                    // This is why this walker can't be an `ExprFolder`: the
                    // `Let` node vanishes and `body` takes its place in the
                    // traversal, still under the SAME `redirects` (no push).
                    if let Some(vid) = id
                        && drop_ids.contains(&vid)
                    {
                        steps.push(Step::Enter {
                            expr: body.into_inner(),
                            redirects,
                        });
                        continue;
                    }
                    // A non-dropped let re-binding a redirect KEY shadows the
                    // helper within its body. `process_chain` adds every
                    // redirect key to `drop_ids` as well, so the drop branch
                    // above claims it first — including a NON-helper let
                    // whose id merely COLLIDES with a dropped helper's, which
                    // is then wrongly dropped; telling a collider from the
                    // helper needs value identity.
                    let body_redirects = match id {
                        Some(vid) => child_redirects(&redirects, [vid]),
                        None => Rc::clone(&redirects),
                    };
                    steps.push(Step::Post(PostKind::Let { name, id }));
                    steps.push(Step::Enter {
                        expr: body.into_inner(),
                        redirects: body_redirects,
                    });
                    steps.push(Step::Enter {
                        expr: value.into_inner(),
                        redirects,
                    });
                }
                PseudoExpr::Lambda { params, body } => {
                    // Lambda params re-bind their ids; a same-id helper
                    // reference inside is a distinct binding and must NOT be
                    // redirected.
                    let body_redirects = child_redirects(&redirects, params.iter().map(|p| p.id));
                    steps.push(Step::Post(PostKind::Lambda { params }));
                    steps.push(Step::Enter {
                        expr: body.into_inner(),
                        redirects: body_redirects,
                    });
                }
                PseudoExpr::RecFn { name, params, body } => {
                    let bound = std::iter::once(name.id).chain(params.iter().map(|p| p.id));
                    let body_redirects = child_redirects(&redirects, bound);
                    steps.push(Step::Post(PostKind::RecFn { name, params }));
                    steps.push(Step::Enter {
                        expr: body.into_inner(),
                        redirects: body_redirects,
                    });
                }
                PseudoExpr::Apply { function, args } => {
                    steps.push(Step::Post(PostKind::Apply { argc: args.len() }));
                    for a in args.into_iter().rev() {
                        steps.push(Step::Enter {
                            expr: a,
                            redirects: Rc::clone(&redirects),
                        });
                    }
                    steps.push(Step::Enter {
                        expr: function.into_inner(),
                        redirects,
                    });
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(Step::Post(PostKind::If));
                    steps.push(Step::Enter {
                        expr: else_branch.into_inner(),
                        redirects: Rc::clone(&redirects),
                    });
                    steps.push(Step::Enter {
                        expr: then_branch.into_inner(),
                        redirects: Rc::clone(&redirects),
                    });
                    steps.push(Step::Enter {
                        expr: condition.into_inner(),
                        redirects,
                    });
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let subj_name_id = subject_name.as_ref().map(|b| b.id);
                    steps.push(Step::Post(PostKind::When {
                        subject_name: subject_name.clone(),
                        clause_count: clauses.len(),
                    }));
                    for clause in clauses.into_iter().rev() {
                        // When-pattern binders and the `as` subject_name
                        // re-bind their ids in the clause; shadowing same-id
                        // redirect keys keeps such a binder from being
                        // redirected to the helper. Independent of the
                        // subject's own (not-yet-computed) result, so this
                        // can be done for every clause up front.
                        let bound = clause.pattern.bound_ids().into_iter().chain(subj_name_id);
                        let r = child_redirects(&redirects, bound);
                        let has_guard = clause.guard.is_some();
                        // A `Literal` pattern carries a matched-against
                        // expression whose Var uses must also be redirected
                        // (it binds nothing, so `r == redirects` here).
                        let (pattern, literal) = match clause.pattern {
                            WhenPattern::Literal(e) => (PendingPattern::Literal, Some(e)),
                            other => (PendingPattern::Other(other), None),
                        };
                        steps.push(Step::Post(PostKind::Clause { pattern, has_guard }));
                        steps.push(Step::Enter {
                            expr: clause.body,
                            redirects: Rc::clone(&r),
                        });
                        if let Some(guard) = clause.guard {
                            steps.push(Step::Enter {
                                expr: guard,
                                redirects: Rc::clone(&r),
                            });
                        }
                        if let Some(lit) = literal {
                            steps.push(Step::Enter {
                                expr: lit,
                                redirects: r,
                            });
                        }
                    }
                    steps.push(Step::Enter {
                        expr: subject.into_inner(),
                        redirects,
                    });
                }
                PseudoExpr::List { elements, tail } => {
                    steps.push(Step::Post(PostKind::List {
                        count: elements.len(),
                        has_tail: tail.is_some(),
                    }));
                    if let Some(t) = tail {
                        steps.push(Step::Enter {
                            expr: t.into_inner(),
                            redirects: Rc::clone(&redirects),
                        });
                    }
                    for e in elements.into_iter().rev() {
                        steps.push(Step::Enter {
                            expr: e,
                            redirects: Rc::clone(&redirects),
                        });
                    }
                }
                PseudoExpr::Tuple(items) => {
                    steps.push(Step::Post(PostKind::Tuple { count: items.len() }));
                    for i in items.into_iter().rev() {
                        steps.push(Step::Enter {
                            expr: i,
                            redirects: Rc::clone(&redirects),
                        });
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    steps.push(Step::Post(PostKind::Pair));
                    steps.push(Step::Enter {
                        expr: b.into_inner(),
                        redirects: Rc::clone(&redirects),
                    });
                    steps.push(Step::Enter {
                        expr: a.into_inner(),
                        redirects,
                    });
                }
                PseudoExpr::Constr {
                    tag,
                    shape,
                    fields,
                    type_hint,
                } => {
                    steps.push(Step::Post(PostKind::Constr {
                        type_hint,
                        tag,
                        shape,
                        count: fields.len(),
                    }));
                    for f in fields.into_iter().rev() {
                        steps.push(Step::Enter {
                            expr: f,
                            redirects: Rc::clone(&redirects),
                        });
                    }
                }
                PseudoExpr::FieldAccess { record, selector } => {
                    steps.push(Step::Post(PostKind::FieldAccess { selector }));
                    steps.push(Step::Enter {
                        expr: record.into_inner(),
                        redirects,
                    });
                }
                PseudoExpr::IndexAccess { collection, index } => {
                    steps.push(Step::Post(PostKind::IndexAccess { index }));
                    steps.push(Step::Enter {
                        expr: collection.into_inner(),
                        redirects,
                    });
                }
                PseudoExpr::BinOp { op, left, right } => {
                    steps.push(Step::Post(PostKind::BinOp { op }));
                    steps.push(Step::Enter {
                        expr: right.into_inner(),
                        redirects: Rc::clone(&redirects),
                    });
                    steps.push(Step::Enter {
                        expr: left.into_inner(),
                        redirects,
                    });
                }
                PseudoExpr::UnOp { op, operand } => {
                    steps.push(Step::Post(PostKind::UnOp { op }));
                    steps.push(Step::Enter {
                        expr: operand.into_inner(),
                        redirects,
                    });
                }
                PseudoExpr::BuiltinCall { name, args } => {
                    steps.push(Step::Post(PostKind::BuiltinCall {
                        name,
                        argc: args.len(),
                    }));
                    for a in args.into_iter().rev() {
                        steps.push(Step::Enter {
                            expr: a,
                            redirects: Rc::clone(&redirects),
                        });
                    }
                }
                PseudoExpr::Delay(inner) => {
                    steps.push(Step::Post(PostKind::Delay));
                    steps.push(Step::Enter {
                        expr: inner.into_inner(),
                        redirects,
                    });
                }
                PseudoExpr::Force(inner) => {
                    steps.push(Step::Post(PostKind::Force));
                    steps.push(Step::Enter {
                        expr: inner.into_inner(),
                        redirects,
                    });
                }
                PseudoExpr::Trace { message, value } => {
                    steps.push(Step::Post(PostKind::Trace));
                    steps.push(Step::Enter {
                        expr: value.into_inner(),
                        redirects: Rc::clone(&redirects),
                    });
                    steps.push(Step::Enter {
                        expr: message.into_inner(),
                        redirects,
                    });
                }
                other => done.push(other),
            },
            Step::Post(kind) => match kind {
                PostKind::Let { name, id } => {
                    let body = done.pop().expect("let body");
                    let value = done.pop().expect("let value");
                    done.push(PseudoExpr::Let {
                        name,
                        id,
                        value: PBox::new(value),
                        body: PBox::new(body),
                    });
                }
                PostKind::Lambda { params } => {
                    let body = done.pop().expect("lambda body");
                    done.push(PseudoExpr::Lambda {
                        params,
                        body: PBox::new(body),
                    });
                }
                PostKind::RecFn { name, params } => {
                    let body = done.pop().expect("recfn body");
                    done.push(PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(body),
                    });
                }
                PostKind::Apply { argc } => {
                    let args = take(&mut done, argc);
                    let function = done.pop().expect("apply function");
                    done.push(PseudoExpr::Apply {
                        function: PBox::new(function),
                        args: args.into(),
                    });
                }
                PostKind::If => {
                    let else_branch = done.pop().expect("if else");
                    let then_branch = done.pop().expect("if then");
                    let condition = done.pop().expect("if condition");
                    done.push(PseudoExpr::If {
                        condition: PBox::new(condition),
                        then_branch: PBox::new(then_branch),
                        else_branch: PBox::new(else_branch),
                    });
                }
                PostKind::When {
                    subject_name,
                    clause_count,
                } => {
                    let at = done_clauses.len() - clause_count;
                    let clauses = done_clauses.split_off(at);
                    let subject = done.pop().expect("when subject");
                    done.push(PseudoExpr::When {
                        subject: PBox::new(subject),
                        subject_name,
                        clauses,
                    });
                }
                PostKind::Clause { pattern, has_guard } => {
                    let body = done.pop().expect("clause body");
                    let guard = if has_guard {
                        Some(done.pop().expect("clause guard"))
                    } else {
                        None
                    };
                    let pattern = match pattern {
                        PendingPattern::Literal => {
                            WhenPattern::Literal(done.pop().expect("clause literal"))
                        }
                        PendingPattern::Other(p) => p,
                    };
                    done_clauses.push(WhenClause {
                        pattern,
                        guard,
                        body,
                    });
                }
                PostKind::List { count, has_tail } => {
                    let tail = if has_tail {
                        Some(done.pop().expect("list tail"))
                    } else {
                        None
                    };
                    let elements = take(&mut done, count);
                    done.push(PseudoExpr::List {
                        elements: elements.into(),
                        tail: tail.map(PBox::new),
                    });
                }
                PostKind::Tuple { count } => {
                    let elements = take(&mut done, count);
                    done.push(PseudoExpr::Tuple(elements.into()));
                }
                PostKind::Pair => {
                    let b = done.pop().expect("pair second");
                    let a = done.pop().expect("pair first");
                    done.push(PseudoExpr::Pair(PBox::new(a), PBox::new(b)));
                }
                PostKind::Constr {
                    type_hint,
                    tag,
                    shape,
                    count,
                } => {
                    let fields = take(&mut done, count);
                    done.push(PseudoExpr::Constr {
                        type_hint,
                        tag,
                        fields: fields.into(),
                        shape,
                    });
                }
                PostKind::FieldAccess { selector } => {
                    let record = done.pop().expect("field access record");
                    done.push(PseudoExpr::FieldAccess {
                        record: PBox::new(record),
                        selector,
                    });
                }
                PostKind::IndexAccess { index } => {
                    let collection = done.pop().expect("index access collection");
                    done.push(PseudoExpr::IndexAccess {
                        collection: PBox::new(collection),
                        index,
                    });
                }
                PostKind::BinOp { op } => {
                    let right = done.pop().expect("binop right");
                    let left = done.pop().expect("binop left");
                    done.push(PseudoExpr::BinOp {
                        op,
                        left: PBox::new(left),
                        right: PBox::new(right),
                    });
                }
                PostKind::UnOp { op } => {
                    let operand = done.pop().expect("unop operand");
                    done.push(PseudoExpr::UnOp {
                        op,
                        operand: PBox::new(operand),
                    });
                }
                PostKind::BuiltinCall { name, argc } => {
                    let args = take(&mut done, argc);
                    done.push(PseudoExpr::BuiltinCall {
                        name,
                        args: args.into(),
                    });
                }
                PostKind::Delay => {
                    let inner = done.pop().expect("delay inner");
                    done.push(PseudoExpr::Delay(PBox::new(inner)));
                }
                PostKind::Force => {
                    let inner = done.pop().expect("force inner");
                    done.push(PseudoExpr::Force(PBox::new(inner)));
                }
                PostKind::Trace => {
                    let value = done.pop().expect("trace value");
                    let message = done.pop().expect("trace message");
                    done.push(PseudoExpr::Trace {
                        message: PBox::new(message),
                        value: PBox::new(value),
                    });
                }
            },
        }
    }

    debug_assert_eq!(
        done.len(),
        1,
        "apply_redirects must leave exactly one result"
    );
    done.pop().expect("apply_redirects result")
}

#[cfg(test)]
mod tests;
