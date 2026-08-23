//! Name-orphan audit.
//!
//! Walks a [`PseudoExpr`] tracking binders in scope (let / lambda /
//! recfn params / when-pattern) and classifies every
//! [`PseudoExpr::Var`]: **bound** when the nearest name frame lists
//! the ref's `id`; **shadow confusion** when the `id` binds in an
//! outer frame that a nearer same-name binder shadows (ambiguous
//! render, VarId resolution still works); **name-orphan** when name
//! and `id` come apart (the render looks right because the name
//! resolves; VarId-faithful rewrites break); **true-free** when
//! neither name nor `id` is in scope, usually a root lambda param.
//!
//! Reports counts per category and the top-K offending names.
//! Diagnostic only: nothing here shapes decompiler output. Most
//! helpers run from overlay diagnostic tests and the
//! `DEHOSK_ORPHAN_TRACE` / `DEHOSK_NAME_ORPHAN_TARGET` debug
//! paths, which the lib build does not count as uses — hence the
//! module-level `allow(dead_code)`.
#![allow(dead_code)]

use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Default, Clone)]
pub(crate) struct NameOrphanReport {
    pub bound: usize,
    /// Reference whose `id` is bound in an outer scope but a
    /// nearer binder with the same name shadows it. The render
    /// is ambiguous; VarId resolution still works.
    pub shadow_confusion: usize,
    /// Reference whose `name` and `id` disagree with the
    /// scope chain: a same-name binder carries another `id`,
    /// or the `id` is in scope under another name. The render
    /// looks right because the name resolves; VarId-faithful
    /// rewrites break.
    pub name_orphans: usize,
    pub true_free: usize,
    /// Top offending name-orphan `name_hint`s, sorted by count.
    pub offenders: Vec<(String, usize)>,
    /// Top offending true-free `name_hint`s — refs with no binder
    /// matching name OR id anywhere in scope. Catches a dangling
    /// ref before a downstream rename turns it into a name-orphan.
    pub free_offenders: Vec<(String, usize)>,
}

/// Result of the id-orphan audit.
///
/// A stranded ref is a `Var{_, id=X}` whose `X` binds somewhere
/// in the tree but outside the ref's ancestor scope chain — a
/// structural break that predates naming. A later rename can
/// surface it as a name-orphan by colliding names with an outer
/// binder.
#[derive(Debug, Default, Clone)]
pub(crate) struct IdOrphanReport {
    /// Refs whose id matches exactly one currently-visible binder.
    pub bound: usize,
    /// Refs whose id belongs to some binder in the AST but that
    /// binder is NOT on the current ancestor scope chain.
    pub stranded: usize,
    /// Refs whose id is not any binder's id in the AST and is not
    /// in the root_params allowlist. Legitimately free only if the
    /// caller knows they come from a root lambda param.
    pub truly_free: usize,
    /// Top offending stranded `(name, count)` pairs.
    pub stranded_by_name: Vec<(String, usize)>,
}

/// Walk `expr` and classify every `Var` reference by id alone.
/// `root_params` lists ids that are legitimately free at the root.
///
/// Unlike `audit_name_orphans` this never looks at names, so it
/// catches a ref whose VarId has left its ancestor scope chain
/// before a rename can disguise the break as a name collision.
pub(crate) fn audit_id_orphans(
    expr: &PseudoExpr,
    root_params: &[(String, VarId)],
) -> IdOrphanReport {
    let mut all_binder_ids: HashSet<VarId> = HashSet::new();
    collect_all_binder_ids(expr, &mut all_binder_ids);

    let mut report = IdOrphanReport::default();
    let mut by_name: HashMap<String, usize> = HashMap::new();
    let mut scopes: Vec<HashMap<VarId, ()>> = Vec::new();
    let mut root_scope: HashMap<VarId, ()> = HashMap::new();
    for (_, id) in root_params {
        root_scope.insert(*id, ());
    }
    scopes.push(root_scope);

    visit_id(
        expr,
        &mut scopes,
        &all_binder_ids,
        &mut report,
        &mut by_name,
    );

    let mut pairs: Vec<(String, usize)> = by_name.into_iter().collect();
    pairs.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    pairs.truncate(20);
    report.stranded_by_name = pairs;

    report
}

fn collect_all_binder_ids(expr: &PseudoExpr, out: &mut HashSet<VarId>) {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        match expr {
            PseudoExpr::Var { .. }
            | PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
            PseudoExpr::Lambda { params, body } => {
                for p in params {
                    out.insert(p.var_id());
                }
                stack.push(body);
            }
            PseudoExpr::RecFn { name, params, body } => {
                out.insert(name.var_id());
                for p in params {
                    out.insert(p.var_id());
                }
                stack.push(body);
            }
            PseudoExpr::Let {
                id, value, body, ..
            } => {
                if let Some(vid) = *id {
                    out.insert(vid);
                }
                stack.push(body);
                stack.push(value);
            }
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    stack.push(a);
                }
                stack.push(function);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                stack.push(else_branch);
                stack.push(then_branch);
                stack.push(condition);
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                if let Some(sn) = subject_name {
                    out.insert(sn.var_id());
                }
                for c in clauses.iter().rev() {
                    collect_pattern_binder_ids(&c.pattern, out);
                    if let Some(g) = &c.guard {
                        stack.push(g);
                    }
                    stack.push(&c.body);
                }
                stack.push(subject);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                stack.push(right);
                stack.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => stack.push(operand),
            PseudoExpr::Force(i) | PseudoExpr::Delay(i) => stack.push(i),
            PseudoExpr::Trace { message, value } => {
                stack.push(value);
                stack.push(message);
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    stack.push(t);
                }
                for e in elements.iter().rev() {
                    stack.push(e);
                }
            }
            PseudoExpr::Tuple(items) => {
                for i in items.iter().rev() {
                    stack.push(i);
                }
            }
            PseudoExpr::Pair(a, b) => {
                stack.push(b);
                stack.push(a);
            }
            PseudoExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    stack.push(f);
                }
            }
            PseudoExpr::FieldAccess { record, .. } => stack.push(record),
            PseudoExpr::IndexAccess { collection, .. } => stack.push(collection),
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    stack.push(a);
                }
            }
        }
    }
}

fn collect_pattern_binder_ids(pattern: &WhenPattern, out: &mut HashSet<VarId>) {
    match pattern {
        WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
        WhenPattern::Var(b) => {
            out.insert(b.var_id());
        }
        WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
            for b in fields {
                out.insert(b.var_id());
            }
        }
        WhenPattern::List { elements, tail } => {
            for b in elements {
                out.insert(b.var_id());
            }
            if let Some(t) = tail {
                out.insert(t.var_id());
            }
        }
        WhenPattern::Pair(a, b) => {
            out.insert(a.var_id());
            out.insert(b.var_id());
        }
    }
}

enum IdStep<'a> {
    Visit(&'a PseudoExpr),
    PopScope,
    /// A `let`: the VALUE is walked in the outer scope (already done by the
    /// time this fires), then a fresh scope binds `id` for the body.
    EnterLetBody {
        id: Option<VarId>,
        body: &'a PseudoExpr,
    },
    /// A `when` clause: subject_name + pattern binders are in scope for
    /// guard/body only.
    EnterClause {
        subject_name: Option<&'a Binder>,
        clause: &'a WhenClause,
    },
}

// Iterative: same script-controlled depth / wasm call-stack risk as
// `collect_all_binder_ids` above, but this walk also carries scope state
// (the `scopes` stack), so a plain worklist isn't enough — a `let`'s body
// must see the binding introduced between visiting its value and its body,
// and a scope must be popped only after the whole subtree it covers is
// done. `IdStep::EnterLetBody`/`EnterClause` defer exactly that pop to the
// right point, matching `decompile/mid/free_vars`'s `Step::EnterLetBody`.
fn visit_id(
    expr: &PseudoExpr,
    scopes: &mut Vec<HashMap<VarId, ()>>,
    all_binder_ids: &HashSet<VarId>,
    report: &mut IdOrphanReport,
    by_name: &mut HashMap<String, usize>,
) {
    let id_in_scope = |scopes: &[HashMap<VarId, ()>], id: VarId| {
        scopes.iter().any(|frame| frame.contains_key(&id))
    };

    let mut steps: Vec<IdStep<'_>> = vec![IdStep::Visit(expr)];
    while let Some(step) = steps.pop() {
        match step {
            IdStep::PopScope => {
                scopes.pop();
            }
            IdStep::EnterLetBody { id, body } => {
                scopes.push(HashMap::new());
                if let Some(vid) = id
                    && let Some(top) = scopes.last_mut()
                {
                    top.insert(vid, ());
                }
                steps.push(IdStep::PopScope);
                steps.push(IdStep::Visit(body));
            }
            IdStep::EnterClause {
                subject_name,
                clause,
            } => {
                scopes.push(HashMap::new());
                if let Some(sn) = subject_name
                    && let Some(top) = scopes.last_mut()
                {
                    top.insert(sn.var_id(), ());
                }
                bind_pattern_ids(&clause.pattern, scopes);
                steps.push(IdStep::PopScope);
                steps.push(IdStep::Visit(&clause.body));
                if let Some(g) = &clause.guard {
                    steps.push(IdStep::Visit(g));
                }
            }
            IdStep::Visit(expr) => match expr {
                PseudoExpr::Var { name, id } => {
                    let Some(vid) = id.get() else {
                        continue;
                    };
                    if id_in_scope(scopes, vid) {
                        report.bound += 1;
                    } else if all_binder_ids.contains(&vid) {
                        report.stranded += 1;
                        *by_name.entry(name.clone()).or_insert(0) += 1;
                    } else {
                        report.truly_free += 1;
                    }
                }
                PseudoExpr::Lambda { params, body } => {
                    scopes.push(HashMap::new());
                    for p in params {
                        if let Some(top) = scopes.last_mut() {
                            top.insert(p.var_id(), ());
                        }
                    }
                    steps.push(IdStep::PopScope);
                    steps.push(IdStep::Visit(body));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    scopes.push(HashMap::new());
                    if let Some(top) = scopes.last_mut() {
                        top.insert(name.var_id(), ());
                    }
                    for p in params {
                        if let Some(top) = scopes.last_mut() {
                            top.insert(p.var_id(), ());
                        }
                    }
                    steps.push(IdStep::PopScope);
                    steps.push(IdStep::Visit(body));
                }
                PseudoExpr::Let {
                    id, value, body, ..
                } => {
                    steps.push(IdStep::EnterLetBody { id: *id, body });
                    steps.push(IdStep::Visit(value));
                }
                PseudoExpr::Apply { function, args } => {
                    for a in args.iter().rev() {
                        steps.push(IdStep::Visit(a));
                    }
                    steps.push(IdStep::Visit(function));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(IdStep::Visit(else_branch));
                    steps.push(IdStep::Visit(then_branch));
                    steps.push(IdStep::Visit(condition));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    for c in clauses.iter().rev() {
                        steps.push(IdStep::EnterClause {
                            subject_name: subject_name.as_ref(),
                            clause: c,
                        });
                    }
                    steps.push(IdStep::Visit(subject));
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail {
                        steps.push(IdStep::Visit(t));
                    }
                    for e in elements.iter().rev() {
                        steps.push(IdStep::Visit(e));
                    }
                }
                PseudoExpr::Tuple(items) => {
                    for i in items.iter().rev() {
                        steps.push(IdStep::Visit(i));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    steps.push(IdStep::Visit(b));
                    steps.push(IdStep::Visit(a));
                }
                PseudoExpr::Constr { fields, .. } => {
                    for f in fields.iter().rev() {
                        steps.push(IdStep::Visit(f));
                    }
                }
                PseudoExpr::FieldAccess { record, .. } => steps.push(IdStep::Visit(record)),
                PseudoExpr::IndexAccess { collection, .. } => steps.push(IdStep::Visit(collection)),
                PseudoExpr::BinOp { left, right, .. } => {
                    steps.push(IdStep::Visit(right));
                    steps.push(IdStep::Visit(left));
                }
                PseudoExpr::UnOp { operand, .. } => steps.push(IdStep::Visit(operand)),
                PseudoExpr::BuiltinCall { args, .. } => {
                    for a in args.iter().rev() {
                        steps.push(IdStep::Visit(a));
                    }
                }
                PseudoExpr::Delay(i) | PseudoExpr::Force(i) => steps.push(IdStep::Visit(i)),
                PseudoExpr::Trace { message, value } => {
                    steps.push(IdStep::Visit(value));
                    steps.push(IdStep::Visit(message));
                }
                _ => {}
            },
        }
    }
}

/// Dump each NAME-orphan ref (name, id) along
/// with the nearest same-name binder's id in its ancestor scope
/// chain. Helps diagnose name/id drift across rename transforms.
/// Set DEHOSK_NAME_ORPHAN_TARGET=<name> to filter.
pub(crate) fn dump_name_orphan_refs(
    expr: &PseudoExpr,
    root_params: &[(String, VarId)],
    limit: usize,
) {
    struct Ctx<'a> {
        found: Vec<(String, Option<VarId>, Option<VarId>)>,
        target: &'a str,
    }
    enum Step<'a> {
        Visit(&'a PseudoExpr),
        PopScope,
        /// A `let`: the VALUE is walked outside the binding (already done by
        /// the time this fires), the body inside it.
        EnterLetBody {
            name: &'a str,
            id: Option<VarId>,
            body: &'a PseudoExpr,
        },
        /// A `when` clause: subject_name + pattern binders are in scope for
        /// guard/body only.
        EnterClause {
            subject_name: Option<&'a Binder>,
            clause: &'a WhenClause,
        },
    }
    fn walk(root: &PseudoExpr, scopes: &mut Vec<HashMap<String, VarId>>, ctx: &mut Ctx) {
        let lookup = |scopes: &[HashMap<String, VarId>], n: &str| -> Option<VarId> {
            for f in scopes.iter().rev() {
                if let Some(&id) = f.get(n) {
                    return Some(id);
                }
            }
            None
        };
        let mut steps: Vec<Step<'_>> = vec![Step::Visit(root)];
        while let Some(step) = steps.pop() {
            match step {
                Step::PopScope => {
                    scopes.pop();
                }
                Step::EnterLetBody { name, id, body } => {
                    scopes.push(HashMap::new());
                    if let Some(vid) = id
                        && let Some(top) = scopes.last_mut()
                    {
                        top.insert(name.to_string(), vid);
                    }
                    steps.push(Step::PopScope);
                    steps.push(Step::Visit(body));
                }
                Step::EnterClause {
                    subject_name,
                    clause,
                } => {
                    scopes.push(HashMap::new());
                    if let Some(sn) = subject_name
                        && let Some(top) = scopes.last_mut()
                    {
                        top.insert(sn.as_str().to_string(), sn.var_id());
                    }
                    match &clause.pattern {
                        WhenPattern::Var(b) => {
                            scopes
                                .last_mut()
                                .unwrap()
                                .insert(b.as_str().to_string(), b.var_id());
                        }
                        WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                            for b in fields {
                                scopes
                                    .last_mut()
                                    .unwrap()
                                    .insert(b.as_str().to_string(), b.var_id());
                            }
                        }
                        WhenPattern::List { elements, tail } => {
                            for b in elements {
                                scopes
                                    .last_mut()
                                    .unwrap()
                                    .insert(b.as_str().to_string(), b.var_id());
                            }
                            if let Some(t) = tail {
                                scopes
                                    .last_mut()
                                    .unwrap()
                                    .insert(t.as_str().to_string(), t.var_id());
                            }
                        }
                        WhenPattern::Pair(a, b) => {
                            scopes
                                .last_mut()
                                .unwrap()
                                .insert(a.as_str().to_string(), a.var_id());
                            scopes
                                .last_mut()
                                .unwrap()
                                .insert(b.as_str().to_string(), b.var_id());
                        }
                        _ => {}
                    }
                    steps.push(Step::PopScope);
                    steps.push(Step::Visit(&clause.body));
                    if let Some(g) = &clause.guard {
                        steps.push(Step::Visit(g));
                    }
                }
                Step::Visit(expr) => match expr {
                    PseudoExpr::Var { name, id } => {
                        if ctx.target.is_empty() || name == ctx.target {
                            match lookup(scopes, name) {
                                Some(bid) if Some(bid) != *id => {
                                    ctx.found.push((name.clone(), *id, Some(bid)));
                                }
                                None => {
                                    ctx.found.push((name.clone(), *id, None));
                                }
                                _ => {}
                            }
                        }
                    }
                    PseudoExpr::Lambda { params, body } => {
                        scopes.push(HashMap::new());
                        for p in params {
                            scopes
                                .last_mut()
                                .unwrap()
                                .insert(p.as_str().to_string(), p.var_id());
                        }
                        steps.push(Step::PopScope);
                        steps.push(Step::Visit(body));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        scopes.push(HashMap::new());
                        scopes
                            .last_mut()
                            .unwrap()
                            .insert(name.as_str().to_string(), name.var_id());
                        for p in params {
                            scopes
                                .last_mut()
                                .unwrap()
                                .insert(p.as_str().to_string(), p.var_id());
                        }
                        steps.push(Step::PopScope);
                        steps.push(Step::Visit(body));
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        steps.push(Step::EnterLetBody {
                            name: name.as_str(),
                            id: *id,
                            body,
                        });
                        steps.push(Step::Visit(value));
                    }
                    PseudoExpr::Apply { function, args } => {
                        for a in args.iter().rev() {
                            steps.push(Step::Visit(a));
                        }
                        steps.push(Step::Visit(function));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        steps.push(Step::Visit(else_branch));
                        steps.push(Step::Visit(then_branch));
                        steps.push(Step::Visit(condition));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        for c in clauses.iter().rev() {
                            steps.push(Step::EnterClause {
                                subject_name: subject_name.as_ref(),
                                clause: c,
                            });
                        }
                        steps.push(Step::Visit(subject));
                    }
                    PseudoExpr::BinOp { left, right, .. } => {
                        steps.push(Step::Visit(right));
                        steps.push(Step::Visit(left));
                    }
                    PseudoExpr::UnOp { operand, .. } => steps.push(Step::Visit(operand)),
                    PseudoExpr::BuiltinCall { args, .. } => {
                        for a in args.iter().rev() {
                            steps.push(Step::Visit(a));
                        }
                    }
                    PseudoExpr::List { elements, tail } => {
                        if let Some(t) = tail {
                            steps.push(Step::Visit(t));
                        }
                        for e in elements.iter().rev() {
                            steps.push(Step::Visit(e));
                        }
                    }
                    PseudoExpr::Tuple(items) => {
                        for i in items.iter().rev() {
                            steps.push(Step::Visit(i));
                        }
                    }
                    PseudoExpr::Pair(a, b) => {
                        steps.push(Step::Visit(b));
                        steps.push(Step::Visit(a));
                    }
                    PseudoExpr::Constr { fields, .. } => {
                        for f in fields.iter().rev() {
                            steps.push(Step::Visit(f));
                        }
                    }
                    PseudoExpr::FieldAccess { record, .. } => steps.push(Step::Visit(record)),
                    PseudoExpr::IndexAccess { collection, .. } => {
                        steps.push(Step::Visit(collection))
                    }
                    PseudoExpr::Delay(i) | PseudoExpr::Force(i) => steps.push(Step::Visit(i)),
                    PseudoExpr::Trace { message, value } => {
                        steps.push(Step::Visit(value));
                        steps.push(Step::Visit(message));
                    }
                    _ => {}
                },
            }
        }
    }
    let mut scopes: Vec<HashMap<String, VarId>> = vec![HashMap::new()];
    for (n, id) in root_params {
        scopes[0].insert(n.clone(), *id);
    }
    let target = crate::debug_env::name_orphan_target().to_string();
    let mut ctx = Ctx {
        found: Vec::new(),
        target: &target,
    };
    walk(expr, &mut scopes, &mut ctx);
    let shown = ctx.found.len().min(limit);
    eprintln!(
        "[name-orphan dump] target={:?} total found={} (showing {}):",
        if target.is_empty() { "ALL" } else { &target },
        ctx.found.len(),
        shown
    );
    for (name, id, nearest) in ctx.found.iter().take(limit) {
        let id_display: String = id
            .map(|v| v.to_string())
            .unwrap_or_else(|| "<none>".to_string());
        match nearest {
            Some(nid) => eprintln!(
                "  ref Var{{{}, id={}}} — nearest same-name binder id={} (drift)",
                name, id_display, nid
            ),
            None => eprintln!(
                "  ref Var{{{}, id={}}} — no same-name binder in scope (true-free or id-orphan)",
                name, id_display
            ),
        }
    }
}

/// Dump each stranded ref (name, id) with its binder's kind and
/// name at the binder site, and the AST path to the ref — enough
/// to identify which transform moved ref or binder out of scope.
/// Describe the binding site of `target` — which node binds it and under
/// what name — for the stranded-reference dump.
///
/// Module-level rather than nested inside [`dump_stranded_refs`] so its
/// contract can be pinned by a test: the dump itself only prints, so a
/// nested helper had no way to be checked.
/// One item of the [`find_binder`] search worklist: a plain subexpression,
/// or a `when` clause (whose pattern is checked directly, without
/// recursing, before its guard/body are searched).
enum FindWork<'a> {
    Expr(&'a PseudoExpr),
    Clause(&'a WhenClause),
}

fn find_binder(root: &PseudoExpr, target: VarId) -> Option<String> {
    let mut stack: Vec<FindWork<'_>> = vec![FindWork::Expr(root)];
    while let Some(item) = stack.pop() {
        match item {
            FindWork::Clause(c) => {
                let p_hit = match &c.pattern {
                    WhenPattern::Var(b) if b.var_id() == target => {
                        Some(format!("When Var pattern {}", b.as_str()))
                    }
                    WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                        fields.iter().find_map(|b| {
                            (b.var_id() == target)
                                .then(|| format!("When Constr/Tuple pattern {}", b.as_str()))
                        })
                    }
                    WhenPattern::List { elements, tail } => {
                        let e_hit = elements.iter().find_map(|b| {
                            (b.var_id() == target)
                                .then(|| format!("When List element {}", b.as_str()))
                        });
                        e_hit.or_else(|| {
                            tail.as_ref()
                                .filter(|t| t.var_id() == target)
                                .map(|t| format!("When List tail {}", t.as_str()))
                        })
                    }
                    WhenPattern::Pair(a, b) => {
                        if a.var_id() == target {
                            Some(format!("When Pair a {}", a.as_str()))
                        } else if b.var_id() == target {
                            Some(format!("When Pair b {}", b.as_str()))
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some(p_hit) = p_hit {
                    return Some(p_hit);
                }
                stack.push(FindWork::Expr(&c.body));
                if let Some(g) = &c.guard {
                    stack.push(FindWork::Expr(g));
                }
            }
            FindWork::Expr(expr) => match expr {
                PseudoExpr::Lambda { params, body } => {
                    for p in params {
                        if p.var_id() == target {
                            return Some(format!("Lambda param {}", p.as_str()));
                        }
                    }
                    stack.push(FindWork::Expr(body));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    if name.var_id() == target {
                        return Some(format!("RecFn name {}", name.as_str()));
                    }
                    for p in params {
                        if p.var_id() == target {
                            return Some(format!("RecFn param {}", p.as_str()));
                        }
                    }
                    stack.push(FindWork::Expr(body));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    if *id == Some(target) {
                        return Some(format!("Let {}", name));
                    }
                    stack.push(FindWork::Expr(body));
                    stack.push(FindWork::Expr(value));
                }
                PseudoExpr::Apply { function, args } => {
                    for a in args.iter().rev() {
                        stack.push(FindWork::Expr(a));
                    }
                    stack.push(FindWork::Expr(function));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    stack.push(FindWork::Expr(else_branch));
                    stack.push(FindWork::Expr(then_branch));
                    stack.push(FindWork::Expr(condition));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    if let Some(sn) = subject_name
                        && sn.var_id() == target
                    {
                        return Some(format!("When subject_name {}", sn.as_str()));
                    }
                    for c in clauses.iter().rev() {
                        stack.push(FindWork::Clause(c));
                    }
                    stack.push(FindWork::Expr(subject));
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    stack.push(FindWork::Expr(right));
                    stack.push(FindWork::Expr(left));
                }
                PseudoExpr::UnOp { operand, .. } => stack.push(FindWork::Expr(operand)),
                PseudoExpr::Delay(i) | PseudoExpr::Force(i) => stack.push(FindWork::Expr(i)),
                PseudoExpr::Trace { message, value } => {
                    stack.push(FindWork::Expr(value));
                    stack.push(FindWork::Expr(message));
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail {
                        stack.push(FindWork::Expr(t));
                    }
                    for e in elements.iter().rev() {
                        stack.push(FindWork::Expr(e));
                    }
                }
                PseudoExpr::Tuple(items) => {
                    for i in items.iter().rev() {
                        stack.push(FindWork::Expr(i));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    stack.push(FindWork::Expr(b));
                    stack.push(FindWork::Expr(a));
                }
                PseudoExpr::Constr { fields, .. } => {
                    for f in fields.iter().rev() {
                        stack.push(FindWork::Expr(f));
                    }
                }
                PseudoExpr::FieldAccess { record, .. } => stack.push(FindWork::Expr(record)),
                PseudoExpr::IndexAccess { collection, .. } => {
                    stack.push(FindWork::Expr(collection))
                }
                PseudoExpr::BuiltinCall { args, .. } => {
                    for a in args.iter().rev() {
                        stack.push(FindWork::Expr(a));
                    }
                }
                _ => {}
            },
        }
    }
    None
}

pub(crate) fn dump_stranded_refs(expr: &PseudoExpr, root_params: &[(String, VarId)], limit: usize) {
    let mut all_binder_ids: HashSet<VarId> = HashSet::new();
    collect_all_binder_ids(expr, &mut all_binder_ids);

    // Walk and collect (name, id, path) for stranded refs.
    let mut stranded: Vec<(String, VarId, String)> = Vec::new();

    enum Step<'a> {
        /// Push `label` onto `path`, visit `child`, pop `path` once `child`
        /// (and everything under it) is done — replaces the recursive
        /// `descend` helper's push/recurse/pop wrapping.
        Descend {
            label: String,
            child: &'a PseudoExpr,
        },
        Visit(&'a PseudoExpr),
        PopPath,
        PopScope,
        /// A `let`'s VALUE is walked outside the binding (already done by
        /// the time this fires); this brings `id` into a fresh scope for
        /// the body.
        EnterLetBody {
            name: &'a str,
            id_label: String,
            id: Option<VarId>,
            body: &'a PseudoExpr,
        },
        /// A `when` clause: subject_name + pattern binders are in scope for
        /// guard/body only.
        EnterClause {
            idx: usize,
            subject_name: Option<&'a Binder>,
            clause: &'a WhenClause,
        },
    }

    fn collect_stranded<'a>(
        root: &'a PseudoExpr,
        scopes: &mut Vec<HashMap<VarId, ()>>,
        all: &HashSet<VarId>,
        path: &mut Vec<String>,
        out: &mut Vec<(String, VarId, String)>,
    ) {
        let id_in_scope = |scopes: &[HashMap<VarId, ()>], id: VarId| {
            scopes.iter().any(|frame| frame.contains_key(&id))
        };

        let mut steps: Vec<Step<'a>> = vec![Step::Visit(root)];
        while let Some(step) = steps.pop() {
            match step {
                Step::PopPath => {
                    path.pop();
                }
                Step::PopScope => {
                    scopes.pop();
                }
                Step::Descend { label, child } => {
                    path.push(label);
                    steps.push(Step::PopPath);
                    steps.push(Step::Visit(child));
                }
                Step::EnterLetBody {
                    name,
                    id_label,
                    id,
                    body,
                } => {
                    scopes.push(HashMap::new());
                    if let Some(vid) = id
                        && let Some(top) = scopes.last_mut()
                    {
                        top.insert(vid, ());
                    }
                    steps.push(Step::PopScope);
                    steps.push(Step::Descend {
                        label: format!("Let({name},{id_label}).body"),
                        child: body,
                    });
                }
                Step::EnterClause {
                    idx,
                    subject_name,
                    clause,
                } => {
                    scopes.push(HashMap::new());
                    if let Some(sn) = subject_name
                        && let Some(top) = scopes.last_mut()
                    {
                        top.insert(sn.var_id(), ());
                    }
                    bind_pattern_ids(&clause.pattern, scopes);
                    steps.push(Step::PopScope);
                    steps.push(Step::Descend {
                        label: format!("When.clause[{idx}].body"),
                        child: &clause.body,
                    });
                    if let Some(g) = &clause.guard {
                        steps.push(Step::Descend {
                            label: format!("When.clause[{idx}].guard"),
                            child: g,
                        });
                    }
                }
                Step::Visit(expr) => match expr {
                    PseudoExpr::Var { name, id } => {
                        if let Some(vid) = id.get()
                            && !id_in_scope(scopes, vid)
                            && all.contains(&vid)
                        {
                            out.push((name.clone(), vid, path.join(" -> ")));
                        }
                    }
                    PseudoExpr::Lambda { params, body } => {
                        scopes.push(HashMap::new());
                        for p in params {
                            scopes.last_mut().unwrap().insert(p.var_id(), ());
                        }
                        steps.push(Step::PopScope);
                        steps.push(Step::Descend {
                            label: "Lambda.body".to_string(),
                            child: body,
                        });
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        scopes.push(HashMap::new());
                        scopes.last_mut().unwrap().insert(name.var_id(), ());
                        for p in params {
                            scopes.last_mut().unwrap().insert(p.var_id(), ());
                        }
                        steps.push(Step::PopScope);
                        steps.push(Step::Descend {
                            label: "RecFn.body".to_string(),
                            child: body,
                        });
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        let id_label = id
                            .map(|v| v.to_string())
                            .unwrap_or_else(|| "<none>".to_string());
                        steps.push(Step::EnterLetBody {
                            name: name.as_str(),
                            id_label: id_label.clone(),
                            id: *id,
                            body,
                        });
                        steps.push(Step::Descend {
                            label: format!("Let({name},{id_label}).value"),
                            child: value,
                        });
                    }
                    PseudoExpr::Apply { function, args } => {
                        for (idx, a) in args.iter().enumerate().rev() {
                            steps.push(Step::Descend {
                                label: format!("Apply.arg[{idx}]"),
                                child: a,
                            });
                        }
                        steps.push(Step::Descend {
                            label: "Apply.function".to_string(),
                            child: function,
                        });
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        steps.push(Step::Descend {
                            label: "If.else".to_string(),
                            child: else_branch,
                        });
                        steps.push(Step::Descend {
                            label: "If.then".to_string(),
                            child: then_branch,
                        });
                        steps.push(Step::Descend {
                            label: "If.condition".to_string(),
                            child: condition,
                        });
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        for (idx, c) in clauses.iter().enumerate().rev() {
                            steps.push(Step::EnterClause {
                                idx,
                                subject_name: subject_name.as_ref(),
                                clause: c,
                            });
                        }
                        steps.push(Step::Descend {
                            label: "When.subject".to_string(),
                            child: subject,
                        });
                    }
                    PseudoExpr::List { elements, tail } => {
                        if let Some(t) = tail {
                            steps.push(Step::Descend {
                                label: "List.tail".to_string(),
                                child: t,
                            });
                        }
                        for (idx, e) in elements.iter().enumerate().rev() {
                            steps.push(Step::Descend {
                                label: format!("List.element[{idx}]"),
                                child: e,
                            });
                        }
                    }
                    PseudoExpr::Tuple(items) => {
                        for (idx, i) in items.iter().enumerate().rev() {
                            steps.push(Step::Descend {
                                label: format!("Tuple.item[{idx}]"),
                                child: i,
                            });
                        }
                    }
                    PseudoExpr::Pair(a, b) => {
                        steps.push(Step::Descend {
                            label: "Pair.second".to_string(),
                            child: b,
                        });
                        steps.push(Step::Descend {
                            label: "Pair.first".to_string(),
                            child: a,
                        });
                    }
                    PseudoExpr::Constr { fields, .. } => {
                        for (idx, f) in fields.iter().enumerate().rev() {
                            steps.push(Step::Descend {
                                label: format!("Constr.field[{idx}]"),
                                child: f,
                            });
                        }
                    }
                    PseudoExpr::FieldAccess { record, .. } => steps.push(Step::Descend {
                        label: "FieldAccess.record".to_string(),
                        child: record,
                    }),
                    PseudoExpr::IndexAccess { collection, .. } => steps.push(Step::Descend {
                        label: "IndexAccess.collection".to_string(),
                        child: collection,
                    }),
                    PseudoExpr::BinOp { left, right, .. } => {
                        steps.push(Step::Descend {
                            label: "BinOp.right".to_string(),
                            child: right,
                        });
                        steps.push(Step::Descend {
                            label: "BinOp.left".to_string(),
                            child: left,
                        });
                    }
                    PseudoExpr::UnOp { operand, .. } => steps.push(Step::Descend {
                        label: "UnOp.operand".to_string(),
                        child: operand,
                    }),
                    PseudoExpr::BuiltinCall { name, args } => {
                        for (idx, a) in args.iter().enumerate().rev() {
                            steps.push(Step::Descend {
                                label: format!("BuiltinCall({name}).arg[{idx}]"),
                                child: a,
                            });
                        }
                    }
                    PseudoExpr::Delay(i) => steps.push(Step::Descend {
                        label: "Delay.inner".to_string(),
                        child: i,
                    }),
                    PseudoExpr::Force(i) => steps.push(Step::Descend {
                        label: "Force.inner".to_string(),
                        child: i,
                    }),
                    PseudoExpr::Trace { message, value } => {
                        steps.push(Step::Descend {
                            label: "Trace.value".to_string(),
                            child: value,
                        });
                        steps.push(Step::Descend {
                            label: "Trace.message".to_string(),
                            child: message,
                        });
                    }
                    _ => {}
                },
            }
        }
    }
    let mut scopes: Vec<HashMap<VarId, ()>> = Vec::new();
    let mut root_scope: HashMap<VarId, ()> = HashMap::new();
    for (_, id) in root_params {
        root_scope.insert(*id, ());
    }
    scopes.push(root_scope);
    let mut path = Vec::new();
    collect_stranded(expr, &mut scopes, &all_binder_ids, &mut path, &mut stranded);

    let shown = stranded.len().min(limit);
    eprintln!(
        "[stranded dump] {} total stranded refs (showing {}):",
        stranded.len(),
        shown
    );
    for (name, id, path) in stranded.iter().take(limit) {
        let binder = find_binder(expr, *id).unwrap_or_else(|| "<NO BINDER FOUND>".to_string());
        eprintln!(
            "  ref Var{{{}, id={}}} at {} -> binder: {}",
            name, id, path, binder
        );
    }
}

fn bind_pattern_ids(pattern: &WhenPattern, scopes: &mut [HashMap<VarId, ()>]) {
    let mut bind = |id: VarId| {
        if let Some(top) = scopes.last_mut() {
            top.insert(id, ());
        }
    };
    match pattern {
        WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
        WhenPattern::Var(b) => bind(b.var_id()),
        WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
            for b in fields {
                bind(b.var_id());
            }
        }
        WhenPattern::List { elements, tail } => {
            for b in elements {
                bind(b.var_id());
            }
            if let Some(t) = tail {
                bind(t.var_id());
            }
        }
        WhenPattern::Pair(a, b) => {
            bind(a.var_id());
            bind(b.var_id());
        }
    }
}

/// Walk `expr` and classify every `Var` reference. `root_params`
/// lists the VarIds legitimately free at the root (top-level
/// lambda params). Any other unbound ref is a name-orphan if
/// its name or id still resolves in the scope chain, and
/// true-free if neither does.
pub(crate) fn audit_name_orphans(
    expr: &PseudoExpr,
    root_params: &[(String, VarId)],
) -> NameOrphanReport {
    let mut report = NameOrphanReport::default();
    let mut offender_counts: HashMap<String, usize> = HashMap::new();
    let mut free_counts: HashMap<String, usize> = HashMap::new();

    // Frames are multimaps: one name maps to ALL same-frame binders of
    // that name. A single-value map would let a later sibling evict
    // an earlier one, misclassifying a ref to the first as a name-orphan.
    let mut scopes: Vec<HashMap<String, Vec<VarId>>> = Vec::new();
    let mut root: HashMap<String, Vec<VarId>> = HashMap::new();
    for (name, id) in root_params {
        root.entry(name.clone()).or_default().push(*id);
    }
    scopes.push(root);

    visit(
        expr,
        &mut scopes,
        &mut report,
        &mut offender_counts,
        &mut free_counts,
    );

    let mut offenders: Vec<(String, usize)> = offender_counts.into_iter().collect();
    offenders.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    offenders.truncate(20);
    report.offenders = offenders;

    let mut frees: Vec<(String, usize)> = free_counts.into_iter().collect();
    frees.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    frees.truncate(20);
    report.free_offenders = frees;

    report
}

fn lookup(scopes: &[HashMap<String, VarId>], name: &str) -> Option<VarId> {
    for frame in scopes.iter().rev() {
        if let Some(&id) = frame.get(name) {
            return Some(id);
        }
    }
    None
}

fn id_is_bound_somewhere(scopes: &[HashMap<String, Vec<VarId>>], id: VarId) -> bool {
    scopes
        .iter()
        .any(|frame| frame.values().any(|ids| ids.contains(&id)))
}

fn push_scope(scopes: &mut Vec<HashMap<String, Vec<VarId>>>) {
    scopes.push(HashMap::new());
}

fn pop_scope(scopes: &mut Vec<HashMap<String, Vec<VarId>>>) {
    scopes.pop();
}

fn bind(scopes: &mut [HashMap<String, Vec<VarId>>], name: &str, id: VarId) {
    if let Some(top) = scopes.last_mut() {
        top.entry(name.to_string()).or_default().push(id);
    }
}

/// Target name for orphan tracing. With
/// DEHOSK_ORPHAN_TRACE=<name> set, `classify_var` eprints
/// every name-orphan carrying that name, with its id.
fn trace_name_target() -> Option<String> {
    crate::debug_env::orphan_trace().then_some(String::new())
}

/// Dump every binder and every `Var` ref named `target`, with
/// its id, to separate minted ids from pure refs.
pub(crate) fn dump_name_occurrences(expr: &PseudoExpr, target: &str) {
    struct Dumper<'a> {
        target: &'a str,
    }
    enum WalkItem<'a> {
        Expr(&'a PseudoExpr),
        Clause(&'a WhenClause),
    }
    impl Dumper<'_> {
        fn walk(&self, root: &PseudoExpr) {
            let mut stack: Vec<WalkItem<'_>> = vec![WalkItem::Expr(root)];
            while let Some(item) = stack.pop() {
                match item {
                    WalkItem::Clause(c) => {
                        match &c.pattern {
                            WhenPattern::Var(b) if b.as_str() == self.target => {
                                eprintln!(
                                    "  [binder] When Var pattern {{{}, id={}}}",
                                    b.as_str(),
                                    b.var_id()
                                );
                            }
                            WhenPattern::Constructor { fields, .. }
                            | WhenPattern::Tuple(fields) => {
                                for b in fields {
                                    if b.as_str() == self.target {
                                        eprintln!(
                                            "  [binder] When Constr/Tuple pattern {{{}, id={}}}",
                                            b.as_str(),
                                            b.var_id()
                                        );
                                    }
                                }
                            }
                            WhenPattern::List { elements, tail } => {
                                for b in elements {
                                    if b.as_str() == self.target {
                                        eprintln!(
                                            "  [binder] When List element {{{}, id={}}}",
                                            b.as_str(),
                                            b.var_id()
                                        );
                                    }
                                }
                                if let Some(t) = tail
                                    && t.as_str() == self.target
                                {
                                    eprintln!(
                                        "  [binder] When List tail {{{}, id={}}}",
                                        t.as_str(),
                                        t.var_id()
                                    );
                                }
                            }
                            WhenPattern::Pair(a, b) => {
                                if a.as_str() == self.target {
                                    eprintln!(
                                        "  [binder] When Pair a {{{}, id={}}}",
                                        a.as_str(),
                                        a.var_id()
                                    );
                                }
                                if b.as_str() == self.target {
                                    eprintln!(
                                        "  [binder] When Pair b {{{}, id={}}}",
                                        b.as_str(),
                                        b.var_id()
                                    );
                                }
                            }
                            _ => {}
                        }
                        stack.push(WalkItem::Expr(&c.body));
                        if let Some(g) = &c.guard {
                            stack.push(WalkItem::Expr(g));
                        }
                    }
                    WalkItem::Expr(expr) => match expr {
                        PseudoExpr::Var { name, id } if name == self.target => {
                            let id_label = id
                                .map(|v| v.to_string())
                                .unwrap_or_else(|| "<none>".to_string());
                            eprintln!("  [ref] Var{{{}, id={}}}", name, id_label);
                        }
                        PseudoExpr::Lambda { params, body } => {
                            for p in params {
                                if p.as_str() == self.target {
                                    eprintln!(
                                        "  [binder] Lambda param {{{}, id={}}}",
                                        p.as_str(),
                                        p.var_id()
                                    );
                                }
                            }
                            stack.push(WalkItem::Expr(body));
                        }
                        PseudoExpr::RecFn { name, params, body } => {
                            if name.as_str() == self.target {
                                eprintln!(
                                    "  [binder] RecFn name {{{}, id={}}}",
                                    name.as_str(),
                                    name.var_id()
                                );
                            }
                            for p in params {
                                if p.as_str() == self.target {
                                    eprintln!(
                                        "  [binder] RecFn param {{{}, id={}}}",
                                        p.as_str(),
                                        p.var_id()
                                    );
                                }
                            }
                            stack.push(WalkItem::Expr(body));
                        }
                        PseudoExpr::Let {
                            name,
                            id,
                            value,
                            body,
                        } => {
                            if name == self.target {
                                let id_label = id
                                    .map(|v| v.to_string())
                                    .unwrap_or_else(|| "<none>".to_string());
                                eprintln!("  [binder] Let {{{}, id={}}}", name, id_label);
                            }
                            stack.push(WalkItem::Expr(body));
                            stack.push(WalkItem::Expr(value));
                        }
                        PseudoExpr::Apply { function, args } => {
                            for a in args.iter().rev() {
                                stack.push(WalkItem::Expr(a));
                            }
                            stack.push(WalkItem::Expr(function));
                        }
                        PseudoExpr::If {
                            condition,
                            then_branch,
                            else_branch,
                        } => {
                            stack.push(WalkItem::Expr(else_branch));
                            stack.push(WalkItem::Expr(then_branch));
                            stack.push(WalkItem::Expr(condition));
                        }
                        PseudoExpr::When {
                            subject, clauses, ..
                        } => {
                            for c in clauses.iter().rev() {
                                stack.push(WalkItem::Clause(c));
                            }
                            stack.push(WalkItem::Expr(subject));
                        }
                        PseudoExpr::BinOp { left, right, .. } => {
                            stack.push(WalkItem::Expr(right));
                            stack.push(WalkItem::Expr(left));
                        }
                        PseudoExpr::UnOp { operand, .. } => stack.push(WalkItem::Expr(operand)),
                        PseudoExpr::BuiltinCall { args, .. } => {
                            for a in args.iter().rev() {
                                stack.push(WalkItem::Expr(a));
                            }
                        }
                        PseudoExpr::FieldAccess { record, .. } => {
                            stack.push(WalkItem::Expr(record))
                        }
                        PseudoExpr::IndexAccess { collection, .. } => {
                            stack.push(WalkItem::Expr(collection))
                        }
                        PseudoExpr::Delay(i) | PseudoExpr::Force(i) => {
                            stack.push(WalkItem::Expr(i))
                        }
                        PseudoExpr::Trace { message, value } => {
                            stack.push(WalkItem::Expr(value));
                            stack.push(WalkItem::Expr(message));
                        }
                        PseudoExpr::Constr { fields, .. } => {
                            for f in fields.iter().rev() {
                                stack.push(WalkItem::Expr(f));
                            }
                        }
                        PseudoExpr::List { elements, tail } => {
                            if let Some(t) = tail {
                                stack.push(WalkItem::Expr(t));
                            }
                            for e in elements.iter().rev() {
                                stack.push(WalkItem::Expr(e));
                            }
                        }
                        PseudoExpr::Tuple(items) => {
                            for i in items.iter().rev() {
                                stack.push(WalkItem::Expr(i));
                            }
                        }
                        PseudoExpr::Pair(a, b) => {
                            stack.push(WalkItem::Expr(b));
                            stack.push(WalkItem::Expr(a));
                        }
                        _ => {}
                    },
                }
            }
        }
    }
    Dumper { target }.walk(expr);
}

fn classify_var(
    name: &str,
    id: Option<VarId>,
    scopes: &[HashMap<String, Vec<VarId>>],
    report: &mut NameOrphanReport,
    offenders: &mut HashMap<String, usize>,
    free_counts: &mut HashMap<String, usize>,
) {
    let id_for_scope = match id {
        Some(v) => v,
        None => {
            // Compat-placeholder ids carry no identity; treat by name only.
            if scopes.iter().rev().any(|f| f.contains_key(name)) {
                report.bound += 1;
            } else {
                report.true_free += 1;
                *free_counts.entry(name.to_string()).or_insert(0) += 1;
            }
            return;
        }
    };
    // Find the NEAREST frame binding this name. The ref is BOUND iff its
    // id is among that frame's same-name binders (exact match or a
    // same-frame sibling); an id resolving to an OUTER binder is
    // shadow_confusion, one resolving nowhere is a dangling orphan.
    for frame in scopes.iter().rev() {
        if let Some(ids) = frame.get(name) {
            if ids.contains(&id_for_scope) {
                report.bound += 1;
            } else if id_is_bound_somewhere(scopes, id_for_scope) {
                report.shadow_confusion += 1;
            } else {
                report.name_orphans += 1;
                *offenders.entry(name.to_string()).or_insert(0) += 1;
                if let Some(target) = trace_name_target()
                    && target == name
                {
                    eprintln!(
                        "[orphan trace] {} ref has id={}, nearest same-name binders are {:?}",
                        name, id_for_scope, ids
                    );
                }
            }
            return;
        }
    }
    // No frame binds this name at all.
    if id_is_bound_somewhere(scopes, id_for_scope) {
        report.name_orphans += 1;
        *offenders.entry(name.to_string()).or_insert(0) += 1;
    } else {
        report.true_free += 1;
        *free_counts.entry(name.to_string()).or_insert(0) += 1;
    }
}

enum VisitStep<'a> {
    Visit(&'a PseudoExpr),
    PopScope,
    /// A `let`'s VALUE is walked in the outer scope (already done by the
    /// time this fires); this brings `id` into a fresh scope for the body.
    EnterLetBody {
        name: &'a str,
        id: Option<VarId>,
        body: &'a PseudoExpr,
    },
    /// A `when` clause: subject_name + pattern binders are in scope for
    /// guard/body only. Folds in what `visit_clause` used to do, since
    /// splitting scope setup across a helper call would leave no single
    /// place to defer the matching `pop_scope` to.
    EnterClause {
        subject_name: Option<&'a Binder>,
        clause: &'a WhenClause,
    },
}

// Iterative: same script-controlled depth / wasm call-stack risk as
// `visit_id` above, and the same shape — a `let`'s body must see the
// binding introduced between visiting its value and its body, so
// `VisitStep::EnterLetBody`/`EnterClause` defer the scope pop to right
// after the one subtree it covers, same idiom as `mid/free_vars`.
fn visit(
    expr: &PseudoExpr,
    scopes: &mut Vec<HashMap<String, Vec<VarId>>>,
    report: &mut NameOrphanReport,
    offenders: &mut HashMap<String, usize>,
    free_counts: &mut HashMap<String, usize>,
) {
    let mut steps: Vec<VisitStep<'_>> = vec![VisitStep::Visit(expr)];
    while let Some(step) = steps.pop() {
        match step {
            VisitStep::PopScope => pop_scope(scopes),
            VisitStep::EnterLetBody { name, id, body } => {
                push_scope(scopes);
                if let Some(vid) = id {
                    bind(scopes, name, vid);
                }
                steps.push(VisitStep::PopScope);
                steps.push(VisitStep::Visit(body));
            }
            VisitStep::EnterClause {
                subject_name,
                clause,
            } => {
                push_scope(scopes);
                // The when-subject's binder is in scope for the clause body
                // (it names the scrutinee); the sibling audits
                // (audit_id_orphans / dump) bind it too.
                if let Some(sn) = subject_name {
                    bind(scopes, sn.as_str(), sn.var_id());
                }
                bind_pattern(&clause.pattern, scopes);
                steps.push(VisitStep::PopScope);
                steps.push(VisitStep::Visit(&clause.body));
                if let Some(g) = &clause.guard {
                    steps.push(VisitStep::Visit(g));
                }
            }
            VisitStep::Visit(expr) => match expr {
                PseudoExpr::Var { name, id } => {
                    classify_var(name, *id, scopes, report, offenders, free_counts)
                }
                PseudoExpr::Lambda { params, body } => {
                    push_scope(scopes);
                    for p in params {
                        bind(scopes, p.as_str(), p.var_id());
                    }
                    steps.push(VisitStep::PopScope);
                    steps.push(VisitStep::Visit(body));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    push_scope(scopes);
                    bind(scopes, name.as_str(), name.var_id());
                    for p in params {
                        bind(scopes, p.as_str(), p.var_id());
                    }
                    steps.push(VisitStep::PopScope);
                    steps.push(VisitStep::Visit(body));
                }
                PseudoExpr::Apply { function, args } => {
                    for a in args.iter().rev() {
                        steps.push(VisitStep::Visit(a));
                    }
                    steps.push(VisitStep::Visit(function));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(VisitStep::EnterLetBody {
                        name: name.as_str(),
                        id: *id,
                        body,
                    });
                    steps.push(VisitStep::Visit(value));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(VisitStep::Visit(else_branch));
                    steps.push(VisitStep::Visit(then_branch));
                    steps.push(VisitStep::Visit(condition));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    for clause in clauses.iter().rev() {
                        steps.push(VisitStep::EnterClause {
                            subject_name: subject_name.as_ref(),
                            clause,
                        });
                    }
                    steps.push(VisitStep::Visit(subject));
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail {
                        steps.push(VisitStep::Visit(t));
                    }
                    for e in elements.iter().rev() {
                        steps.push(VisitStep::Visit(e));
                    }
                }
                PseudoExpr::Tuple(items) => {
                    for i in items.iter().rev() {
                        steps.push(VisitStep::Visit(i));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    steps.push(VisitStep::Visit(b));
                    steps.push(VisitStep::Visit(a));
                }
                PseudoExpr::Constr { fields, .. } => {
                    for f in fields.iter().rev() {
                        steps.push(VisitStep::Visit(f));
                    }
                }
                PseudoExpr::FieldAccess { record, .. } => steps.push(VisitStep::Visit(record)),
                PseudoExpr::IndexAccess { collection, .. } => {
                    steps.push(VisitStep::Visit(collection))
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    steps.push(VisitStep::Visit(right));
                    steps.push(VisitStep::Visit(left));
                }
                PseudoExpr::UnOp { operand, .. } => steps.push(VisitStep::Visit(operand)),
                PseudoExpr::BuiltinCall { args, .. } => {
                    for a in args.iter().rev() {
                        steps.push(VisitStep::Visit(a));
                    }
                }
                PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                    steps.push(VisitStep::Visit(inner));
                }
                PseudoExpr::Trace { message, value } => {
                    steps.push(VisitStep::Visit(value));
                    steps.push(VisitStep::Visit(message));
                }
                _ => {}
            },
        }
    }
}

fn bind_pattern(pattern: &WhenPattern, scopes: &mut [HashMap<String, Vec<VarId>>]) {
    match pattern {
        WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
        WhenPattern::Var(b) => bind(scopes, b.as_str(), b.var_id()),
        WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
            for b in fields {
                bind(scopes, b.as_str(), b.var_id());
            }
        }
        WhenPattern::List { elements, tail } => {
            for b in elements {
                bind(scopes, b.as_str(), b.var_id());
            }
            if let Some(t) = tail {
                bind(scopes, t.as_str(), t.var_id());
            }
        }
        WhenPattern::Pair(a, b) => {
            bind(scopes, a.as_str(), a.var_id());
            bind(scopes, b.as_str(), b.var_id());
        }
    }
}

#[cfg(test)]
mod tests;
