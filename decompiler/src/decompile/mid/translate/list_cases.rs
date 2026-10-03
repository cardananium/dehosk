//! Recover `case` on a builtin list.
//!
//! A native `case xs [cons_arm, nil_arm]` on a builtin list hands the cons arm
//! `(head, tail)` and the nil arm nothing. Compilers that thunk the arms'
//! results append one more lambda parameter to each and apply the whole case
//! to `unit`, so `\h \t \u -> …` and `\u -> …` look like a three-field and a
//! one-field constructor.
//!
//! Nothing local tells the two apart, so this pass first proves which
//! variables hold builtin lists. A variable is a list when it is bound to a
//! list-producing builtin or literal, is the tail of a case on a list, or is
//! a parameter of a closure that never escapes and is only ever called with
//! lists in that position. The last two rules are circular, so the set is the
//! greatest fixpoint: start from every candidate and drop any that a call
//! site or scrutinee does not support. A closure that is never called from
//! outside its own recursion therefore needs its entry call to be a list to
//! survive.
//!
//! With the scrutinee proven, the arms' field counts are known: 2 and 0. Any
//! further lambda parameter is the thunk's, so it is dropped together with the
//! `unit` application. The case is then marked [`CaseEncoding::BuiltinList`].

use std::collections::{HashMap, HashSet};

use uplc::builtins::DefaultFunction;

use crate::pseudo::mid::expr::{CaseEncoding, MidBranch, MidExpr, MidLiteral};
use crate::pseudo::mid::rewrite::rewrite_bottom_up;
use crate::pseudo::var_id::VarId;

use super::MidTranslator;

/// A let-bound closure whose every use is a call, so all call sites are known.
struct Callee<'a> {
    params: Vec<VarId>,
    body: &'a MidExpr,
}

struct Facts<'a> {
    /// `let v = value` for every let.
    lets: Vec<(VarId, &'a MidExpr)>,
    /// Every `case` with a variable scrutinee, as (scrutinee, arms).
    cases: Vec<(&'a MidExpr, &'a [MidBranch])>,
    /// Let-bound closures that never escape.
    callees: HashMap<VarId, Callee<'a>>,
    /// `g` of `let g = f(f)` to `f`.
    aliases: HashMap<VarId, VarId>,
    /// Argument lists of calls to each non-escaping closure, keyed by the
    /// closure's let variable.
    /// Each site carries how many leading parameters it does not supply:
    /// 0 for a direct call, 1 for a call through `let g = f(f)`.
    calls: HashMap<VarId, Vec<(usize, &'a [MidExpr])>>,
    builtin_vars: HashMap<VarId, DefaultFunction>,
}

impl MidTranslator {
    pub(super) fn recover_builtin_list_cases(&mut self, root: MidExpr) -> MidExpr {
        let ctx = list_variables(&root);
        let provenance = &mut self.provenance;
        rewrite_bottom_up(root, &mut |node| match node {
            MidExpr::Apply {
                id,
                function,
                args,
            } if is_unit_args(&args)
                && matches!(function.as_ref(), MidExpr::Case { scrutinee, branches, .. }
                    if in_list(scrutinee, &ctx)
                        && has_arities(branches, 1)
                        && branches.iter().all(|b| {
                            b.binders.last().is_some_and(|last| {
                                !crate::decompile::mid::free_vars::free_vars(&b.body)
                                    .contains(last)
                            })
                        })) =>
            {
                let MidExpr::Case {
                    id: case_id,
                    scrutinee,
                    mut branches,
                    ..
                } = *function
                else {
                    unreachable!("case shape checked above");
                };
                for b in &mut branches {
                    b.binders.pop();
                }
                for arg in &args {
                    for uplc_id in provenance.uplc_ids(arg.id()).to_vec() {
                        provenance.absorb_uplc(case_id, uplc_id);
                    }
                }
                let _ = id;
                MidExpr::Case {
                    id: case_id,
                    scrutinee,
                    branches,
                    encoding: CaseEncoding::BuiltinList,
                }
            }
            MidExpr::Case {
                id,
                scrutinee,
                branches,
                encoding: CaseEncoding::Native,
            } if in_list(&scrutinee, &ctx) && has_arities(&branches, 0) => MidExpr::Case {
                id,
                scrutinee,
                branches,
                encoding: CaseEncoding::BuiltinList,
            },
            other => other,
        })
    }
}

/// `[cons, nil]` arms taking `(2 + extra, 0 + extra)` parameters.
fn has_arities(branches: &[MidBranch], extra: usize) -> bool {
    matches!(branches, [cons, nil]
        if cons.binders.len() == 2 + extra && nil.binders.len() == extra)
}

fn is_unit_args(args: &[MidExpr]) -> bool {
    matches!(args, [MidExpr::Constr { tag: 0, fields, .. }] if fields.is_empty())
        || matches!(args, [MidExpr::Lit { value: MidLiteral::Unit, .. }])
}

/// What the fixpoint currently believes.
#[derive(Default)]
struct Ctx {
    /// Variables holding a builtin list.
    lists: HashSet<VarId>,
    /// Non-escaping closures whose result is a builtin list.
    returns_list: HashSet<VarId>,
    /// `g` of `let g = f(f)` to `f`.
    alias_of: HashMap<VarId, VarId>,
    /// Parameter count of each non-escaping closure.
    arity: HashMap<VarId, usize>,
    /// Variables bound to a bare builtin (`(\mkCons tail … -> body) mkCons …`),
    /// so a call through one is a builtin call.
    builtin_vars: HashMap<VarId, DefaultFunction>,
    /// Variables bound to `unConstrData(…)`: a pair whose second half is a
    /// list.
    constr_pairs: HashSet<VarId>,
    /// The `fields` binder of a case on such a pair.
    pair_fields: HashSet<VarId>,
}

/// Builtins whose result is always a builtin list.
fn yields_list(fun: DefaultFunction) -> bool {
    matches!(
        fun,
        DefaultFunction::UnListData
            | DefaultFunction::UnMapData
            | DefaultFunction::TailList
            | DefaultFunction::DropList
            | DefaultFunction::MkCons
            | DefaultFunction::MkNilData
            | DefaultFunction::MkNilPairData
    )
}

impl Ctx {
    /// The closure a call through `head` reaches, and how many leading
    /// parameters that call leaves unsupplied.
    fn callee_of(&self, head: VarId) -> Option<(VarId, usize)> {
        match self.alias_of.get(&head) {
            Some(f) => Some((*f, 1)),
            None => self.arity.contains_key(&head).then_some((head, 0)),
        }
    }
}

/// Whether `expr` is certainly a builtin list.
fn in_list(expr: &MidExpr, ctx: &Ctx) -> bool {
    match expr {
        MidExpr::Var { var, .. } => ctx.lists.contains(var),
        MidExpr::Lit {
            value: MidLiteral::List(_),
            ..
        } => true,
        MidExpr::Builtin { fun, args, .. } => {
            args.len() >= fun.arity()
                && (yields_list(*fun)
                    || (*fun == DefaultFunction::SndPair && is_constr_pair(&args[0], ctx)))
        }
        // An expression that selects between values: a list when every way
        // out is one.
        MidExpr::Case { .. }
        | MidExpr::If { .. }
        | MidExpr::Let { .. }
        | MidExpr::Trace { .. } => closure_returns_list(None, None, expr, ctx),
        MidExpr::Apply { function, args, .. } => match function.as_ref() {
            MidExpr::Var { var, .. } => {
                ctx.builtin_vars.get(var).is_some_and(|fun| {
                    args.len() >= fun.arity()
                        && (yields_list(*fun)
                            || (*fun == DefaultFunction::SndPair
                                && is_constr_pair(&args[0], ctx)))
                })
                    || ctx.callee_of(*var).is_some_and(|(f, shift)| {
                        ctx.returns_list.contains(&f) && ctx.arity[&f] == args.len() + shift
                    })
            }
            _ => false,
        },
        _ => false,
    }
}

/// Whether `expr` is the pair `unConstrData(…)` returns.
fn is_constr_pair(expr: &MidExpr, ctx: &Ctx) -> bool {
    match expr {
        MidExpr::Var { var, .. } => ctx.constr_pairs.contains(var),
        MidExpr::Builtin { fun, args, .. } => {
            *fun == DefaultFunction::UnConstrData && args.len() == 1
        }
        MidExpr::Apply { function, args, .. } => matches!(function.as_ref(),
            MidExpr::Var { var, .. }
                if ctx.builtin_vars.get(var) == Some(&DefaultFunction::UnConstrData)
                    && args.len() == 1),
        _ => false,
    }
}

/// Whether every way out of `body` is a list, a failure, or a recursive call
/// of the closure itself, with at least one genuine list.
fn closure_returns_list(
    name: Option<VarId>,
    self_param: Option<VarId>,
    body: &MidExpr,
    ctx: &Ctx,
) -> bool {
    let mut real = false;
    let mut stack = vec![body];
    while let Some(node) = stack.pop() {
        match node {
            MidExpr::Case { branches, .. } => stack.extend(branches.iter().map(|b| &b.body)),
            MidExpr::If {
                then_branch,
                else_branch,
                ..
            } => stack.extend([then_branch.as_ref(), else_branch.as_ref()]),
            MidExpr::Let { body, .. } | MidExpr::Trace { body, .. } => stack.push(body),
            MidExpr::Error { .. } => {}
            MidExpr::Apply { function, args, .. }
                if matches!(function.as_ref(), MidExpr::Var { var, .. }
                    if Some(*var) == name
                        || name.is_some_and(|n| ctx.alias_of.get(var) == Some(&n))
                        || (Some(*var) == self_param
                            && matches!(args.first(), Some(MidExpr::Var { var: a, .. }) if a == var))) => {}
            other => {
                if in_list(other, ctx) {
                    real = true;
                } else {
                    return false;
                }
            }
        }
    }
    real
}

fn collect(root: &MidExpr) -> (Facts<'_>, HashMap<VarId, usize>) {
    let mut facts = Facts {
        lets: Vec::new(),
        cases: Vec::new(),
        callees: HashMap::new(),
        aliases: HashMap::new(),
        builtin_vars: HashMap::new(),
        calls: HashMap::new(),
    };
    let mut occurrences: HashMap<VarId, usize> = HashMap::new();
    let mut call_heads: Vec<(VarId, &[MidExpr])> = Vec::new();
    // `let g = f(f)`: g is f with its self argument supplied.
    let mut aliases: HashMap<VarId, VarId> = HashMap::new();
    let mut stack = vec![root];
    while let Some(node) = stack.pop() {
        match node {
            MidExpr::Var { var, .. } => *occurrences.entry(*var).or_default() += 1,
            MidExpr::Let { var, value, .. } => {
                facts.lets.push((*var, value));
                if let MidExpr::Builtin { fun, args, .. } = value.as_ref()
                    && args.is_empty()
                {
                    facts.builtin_vars.insert(*var, *fun);
                }
                if let MidExpr::Apply { function, args, .. } = value.as_ref()
                    && let MidExpr::Var { var: f, .. } = function.as_ref()
                    && matches!(args.as_slice(), [MidExpr::Var { var: a, .. }] if a == f)
                {
                    aliases.insert(*var, *f);
                }
                // `let g = (let f = closure in f(f))`
                if let MidExpr::Let {
                    var: f,
                    value: inner_value,
                    body: inner_body,
                    ..
                } = value.as_ref()
                    && matches!(inner_value.as_ref(), MidExpr::Closure { .. })
                    && let MidExpr::Apply { function, args, .. } = inner_body.as_ref()
                    && matches!(function.as_ref(), MidExpr::Var { var: h, .. } if h == f)
                    && matches!(args.as_slice(), [MidExpr::Var { var: a, .. }] if a == f)
                {
                    aliases.insert(*var, *f);
                }
                if let MidExpr::Closure { params, body, .. } = value.as_ref() {
                    facts.callees.insert(
                        *var,
                        Callee {
                            params: params.clone(),
                            body,
                        },
                    );
                }
            }
            MidExpr::Case {
                scrutinee,
                branches,
                ..
            } => facts.cases.push((scrutinee, branches)),
            MidExpr::Apply { function, args, .. } => {
                if let MidExpr::Var { var, .. } = function.as_ref() {
                    call_heads.push((*var, args));
                }
                if let MidExpr::Closure { params, .. } = function.as_ref() {
                    for (param, arg) in params.iter().zip(args.iter()) {
                        if let MidExpr::Builtin { fun, args, .. } = arg
                            && args.is_empty()
                        {
                            facts.builtin_vars.insert(*param, *fun);
                        }
                    }
                }
            }
            _ => {}
        }
        stack.extend(node.children());
    }
    // A closure is only analysable when every occurrence of its name (and of
    // its own first parameter, the self reference, and of each `f(f)` alias)
    // is a call head or the self argument of such a call.
    let mut escaping: HashSet<VarId> = HashSet::new();
    for (name, callee) in &facts.callees {
        let self_param = callee.params.first().copied();
        let alias_names: Vec<VarId> = aliases
            .iter()
            .filter(|(_, f)| *f == name)
            .map(|(g, _)| *g)
            .collect();
        let mut accounted = 0usize;
        let mut self_accounted = 0usize;
        let mut alias_accounted: HashMap<VarId, usize> = HashMap::new();
        let mut alias_defs = 0usize;
        let mut sites: Vec<(usize, &[MidExpr])> = Vec::new();
        for (head, args) in &call_heads {
            let is_outer = head == name;
            let is_inner = self_param == Some(*head);
            let alias = alias_names.iter().find(|g| *g == head).copied();
            if !is_outer && !is_inner && alias.is_none() {
                continue;
            }
            if let Some(g) = alias {
                *alias_accounted.entry(g).or_default() += 1;
                sites.push((1, args));
                continue;
            }
            if is_outer && matches!(args, [MidExpr::Var { var, .. }] if var == name) {
                // The `f(f)` that defines an alias: not a call site.
                accounted += 2;
                alias_defs += 1;
                continue;
            }
            sites.push((0, args));
            if is_outer {
                accounted += 1;
            } else {
                self_accounted += 1;
            }
            match args.first() {
                Some(MidExpr::Var { var, .. }) if var == name => accounted += 1,
                Some(MidExpr::Var { var, .. }) if Some(*var) == self_param => self_accounted += 1,
                _ => {}
            }
        }
        let occ = |v: &VarId| occurrences.get(v).copied().unwrap_or(0);
        let outer_ok = occ(name) == accounted;
        let inner_ok = self_param.is_none_or(|p| occ(&p) == self_accounted);
        let aliases_ok = alias_names
            .iter()
            .all(|g| occ(g) == alias_accounted.get(g).copied().unwrap_or(0))
            && alias_defs == alias_names.len();
        if outer_ok && inner_ok && aliases_ok {
            facts.calls.insert(*name, sites);
        } else {
            escaping.insert(*name);
        }
    }
    facts.callees.retain(|name, _| !escaping.contains(name));
    facts.aliases = aliases
        .into_iter()
        .filter(|(_, f)| facts.callees.contains_key(f))
        .collect();
    (facts, occurrences)
}

/// Greatest fixpoint of "this variable holds a builtin list" and "this
/// closure returns one".
fn list_variables(root: &MidExpr) -> Ctx {
    let (facts, _) = collect(root);
    let mut ctx = Ctx {
        alias_of: facts.aliases.clone(),
        arity: facts
            .callees
            .iter()
            .map(|(n, c)| (*n, c.params.len()))
            .collect(),
        returns_list: facts.callees.keys().copied().collect(),
        builtin_vars: facts.builtin_vars.clone(),
        ..Ctx::default()
    };
    for (var, value) in &facts.lets {
        if is_constr_pair(value, &ctx) {
            ctx.constr_pairs.insert(*var);
        }
    }
    // Optimistic start: every variable a rule could make a list.
    for (var, _) in &facts.lets {
        ctx.lists.insert(*var);
    }
    for callee in facts.callees.values() {
        ctx.lists.extend(callee.params.iter().skip(1).copied());
    }
    for (scrutinee, branches) in &facts.cases {
        if is_constr_pair(scrutinee, &ctx) {
            // `case unConstrData(x) of (\tag \fields -> …)`: fields is a list.
            for b in *branches {
                if let Some(fields) = b.binders.get(1) {
                    ctx.pair_fields.insert(*fields);
                }
            }
        } else if branches.len() == 2 {
            for b in *branches {
                if let Some(tail) = b.binders.get(1) {
                    ctx.lists.insert(*tail);
                }
            }
        }
    }
    ctx.lists.extend(ctx.pair_fields.iter().copied());
    loop {
        let mut doomed: Vec<VarId> = Vec::new();
        let mut doomed_closures: Vec<VarId> = Vec::new();
        for (var, value) in &facts.lets {
            if ctx.lists.contains(var) && !in_list(value, &ctx) {
                doomed.push(*var);
            }
        }
        for (name, callee) in &facts.callees {
            let sites = facts.calls.get(name).map(Vec::as_slice).unwrap_or(&[]);
            for (index, param) in callee.params.iter().enumerate().skip(1) {
                if !ctx.lists.contains(param) {
                    continue;
                }
                let supported = sites.iter().all(|(shift, args)| {
                    index
                        .checked_sub(*shift)
                        .and_then(|i| args.get(i))
                        .is_some_and(|a| in_list(a, &ctx))
                });
                if !supported {
                    doomed.push(*param);
                }
            }
            if ctx.returns_list.contains(name)
                && !closure_returns_list(Some(*name), callee.params.first().copied(), callee.body, &ctx)
            {
                doomed_closures.push(*name);
            }
        }
        for (scrutinee, branches) in &facts.cases {
            if in_list(scrutinee, &ctx) || branches.len() != 2 || is_constr_pair(scrutinee, &ctx) {
                continue;
            }
            for b in *branches {
                if let Some(tail) = b.binders.get(1) {
                    doomed.push(*tail);
                }
            }
        }
        let before = ctx.lists.len() + ctx.returns_list.len();
        for var in doomed {
            ctx.lists.remove(&var);
        }
        for name in doomed_closures {
            ctx.returns_list.remove(&name);
        }
        if ctx.lists.len() + ctx.returns_list.len() == before {
            return ctx;
        }
    }
}
