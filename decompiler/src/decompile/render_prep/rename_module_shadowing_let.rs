//! Rename a `let`/`const` binding that shadows an stdlib module used as a
//! qualifier in its scope (e.g. `const list = …` shadowing `list.map(…)`).
//!
//! The native-list rewrite emits unqualified stdlib calls like `list.map(xs, f)`
//! (a `Var` named `"list.map"`). Independently, the simplifier's name dedup can
//! hand a `Data.un_list`-derived binding the bare name `list`. When that binding
//! is in scope at a `list.map(…)` call, the surface resolves `list` to the value
//! binding, not the `list` module — a hard compile error.
//!
//! When a stdlib module appears as a `module.fn(…)` qualifier anywhere in the
//! program, rename every `Let`/`const` binding whose `name` equals that module
//! to a fresh `name_<N>` and rewire its uses by VarId, unshadowing the bare
//! module name.
//!
//! - Gated on the module actually being used as a `module.fn` qualifier
//!   somewhere in the program (`used`). A program that never qualifies `list.`
//!   leaves a value named `list` alone.
//! - The gate is program-wide "module is qualified", not "the binding's body
//!   uses it", because the qualifier and the colliding top-level `const` render
//!   into sibling top-level positions — the const's own AST `body` does not
//!   lexically nest the qualifier site. That is precise for a top-level const,
//!   which is visible program-wide; a nested `let list` whose own scope has no
//!   `list.` is over-approximated and renamed too, harmlessly.
//! - Only `Let`/`const` bindings are renamed. A function parameter named like a
//!   module (e.g. `fn find(list: List<Data>)`) is untouched — such a param does
//!   not break a `list.` call outside its body, and renaming params is a
//!   riskier, separate concern.
//! - Uses are rewired strictly by the binding's VarId, so a different same-named
//!   binder (a sibling param) keeps its name; the `module.fn` `Var` (name
//!   `"list.map"`, a distinct string) is never matched.

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{PseudoExpr, WhenPattern};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::rename_var_use_by_id_in_expr;

/// stdlib modules that the decompiler can emit as a `module.fn(…)`
/// qualifier and that a value binding could therefore shadow.
const STDLIB_QUALIFIER_MODULES: &[&str] = &[
    "list",
    "option",
    "dict",
    "bytearray",
    "math",
    "pairs",
    "int",
    "string",
];

pub(super) fn rename_module_shadowing_lets(expr: PseudoExpr) -> PseudoExpr {
    // Which stdlib modules actually appear as `module.fn(…)` qualifiers?
    let mut used: HashSet<&'static str> = HashSet::new();
    collect_used_qualifier_modules(&expr, &mut used);
    if used.is_empty() {
        return expr;
    }
    // Names already taken anywhere — so a fresh `name_<N>` collides with nothing.
    let mut taken: HashSet<String> = HashSet::new();
    collect_names(&expr, &mut taken);

    // Candidate bindings: `Let`s named like a used qualifier module.
    let mut candidates: Vec<(VarId, String)> = Vec::new();
    collect_candidates(&expr, &used, &mut candidates);
    // FAIL CLOSED: drop a candidate whose rename could STRAND an authoritative
    // (VarId-tagged) reference the rewrite cannot reach — an id-ref buried in a
    // `WhenPattern::Literal`, which `rename_var_use_by_id_in_expr` does not
    // traverse, leaving a use of the old name un-rewired. Skipping is safe: the
    // binding keeps its original name. The pass relies on the binding's
    // references being VarId-tagged; a bare name-only ref resolving to the const
    // is out of scope, since guarding on it globally would false-skip name-only
    // uses of an unrelated same-named param.
    candidates.retain(|(vid, _old)| !id_ref_in_literal_pattern(&expr, *vid));
    if candidates.is_empty() {
        return expr;
    }

    // Assign fresh non-colliding names.
    let mut renames: HashMap<VarId, String> = HashMap::new();
    for (vid, old) in candidates {
        if renames.contains_key(&vid) {
            continue;
        }
        let fresh = fresh_name(&old, &taken);
        taken.insert(fresh.clone());
        renames.insert(vid, fresh);
    }

    // Apply: rename the `Let` binders, then rewire uses by VarId.
    let mut out = rename_let_binders(expr, &renames);
    for (vid, fresh) in &renames {
        out = rename_var_use_by_id_in_expr(&out, *vid, fresh);
    }
    out
}

/// The stdlib module of a `module.fn` qualifier name, if any.
fn qualifier_module(name: &str) -> Option<&'static str> {
    let prefix = name.split('.').next()?;
    STDLIB_QUALIFIER_MODULES
        .iter()
        .copied()
        .find(|m| *m == prefix && name.len() > prefix.len() + 1)
}

fn collect_used_qualifier_modules(expr: &PseudoExpr, out: &mut HashSet<&'static str>) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::Var { name, .. } = cur
            && let Some(m) = qualifier_module(name)
        {
            out.insert(m);
        }
        let mut kids: Vec<&PseudoExpr> = Vec::new();
        for_each_child(cur, &mut |c| kids.push(c));
        pending.extend(kids.into_iter().rev());
    }
}

fn collect_names(expr: &PseudoExpr, out: &mut HashSet<String>) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Let { name, .. } => {
                out.insert(name.clone());
            }
            PseudoExpr::Var { name, .. } => {
                out.insert(name.clone());
            }
            PseudoExpr::Lambda { params, .. } => {
                out.extend(params.iter().map(|p| p.to_string()));
            }
            PseudoExpr::RecFn { name, params, .. } => {
                out.insert(name.to_string());
                out.extend(params.iter().map(|p| p.to_string()));
            }
            PseudoExpr::When {
                subject_name,
                clauses,
                ..
            } => {
                // `When` subject_name and clause pattern binders are names in scope
                // too, so a fresh `name_<N>` cannot capture a rewired use.
                if let Some(b) = subject_name {
                    out.insert(b.to_string());
                }
                for c in clauses {
                    out.extend(pattern_binder_names(&c.pattern));
                }
            }
            _ => {}
        }
        let mut kids: Vec<&PseudoExpr> = Vec::new();
        for_each_child(cur, &mut |c| kids.push(c));
        pending.extend(kids.into_iter().rev());
    }
}

/// Names bound by a `when`/`expect` pattern.
fn pattern_binder_names(pattern: &crate::pseudo::ast::WhenPattern) -> Vec<String> {
    use crate::pseudo::ast::WhenPattern;
    match pattern {
        WhenPattern::Constructor { fields, .. } => fields.iter().map(|b| b.to_string()).collect(),
        WhenPattern::List { elements, tail } => elements
            .iter()
            .chain(tail.iter())
            .map(|b| b.to_string())
            .collect(),
        WhenPattern::Tuple(items) => items.iter().map(|b| b.to_string()).collect(),
        WhenPattern::Pair(a, b) => vec![a.to_string(), b.to_string()],
        WhenPattern::Var(b) => vec![b.to_string()],
        WhenPattern::Wildcard | WhenPattern::Literal(_) => Vec::new(),
    }
}

fn collect_candidates(
    expr: &PseudoExpr,
    used: &HashSet<&'static str>,
    out: &mut Vec<(VarId, String)>,
) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::Let {
            name,
            id: Some(vid),
            ..
        } = cur
            && used.contains(name.as_str())
        {
            out.push((*vid, name.clone()));
        }
        let mut kids: Vec<&PseudoExpr> = Vec::new();
        for_each_child(cur, &mut |c| kids.push(c));
        pending.extend(kids.into_iter().rev());
    }
}

/// `true` if a `Var{id==Some(vid)}` appears inside a `WhenPattern::Literal` —
/// a reference `rename_var_use_by_id_in_expr` would NOT rewire (it does not
/// descend literal patterns), so renaming the binding would strand it.
fn id_ref_in_literal_pattern(expr: &PseudoExpr, vid: VarId) -> bool {
    let mut found = false;
    fn walk(e: &PseudoExpr, vid: VarId, in_literal: bool, found: &mut bool) {
        let mut pending: Vec<(&PseudoExpr, bool)> = vec![(e, in_literal)];
        while let Some((cur, in_lit)) = pending.pop() {
            if in_lit
                && let PseudoExpr::Var { id: Some(v), .. } = cur
                && *v == vid
            {
                *found = true;
                break;
            }
            if let PseudoExpr::When {
                subject, clauses, ..
            } = cur
            {
                let mut kids: Vec<(&PseudoExpr, bool)> = vec![(subject, in_lit)];
                for c in clauses {
                    if let crate::pseudo::ast::WhenPattern::Literal(lit) = &c.pattern {
                        kids.push((lit, true));
                    }
                    if let Some(g) = &c.guard {
                        kids.push((g, in_lit));
                    }
                    kids.push((&c.body, in_lit));
                }
                pending.extend(kids.into_iter().rev());
                continue;
            }
            let mut kids: Vec<&PseudoExpr> = Vec::new();
            for_each_child(cur, &mut |c| kids.push(c));
            pending.extend(kids.into_iter().rev().map(|c| (c, in_lit)));
        }
    }
    walk(expr, vid, false, &mut found);
    found
}

fn fresh_name(base: &str, taken: &HashSet<String>) -> String {
    let mut n = 2usize;
    loop {
        let candidate = format!("{base}_{n}");
        if !taken.contains(&candidate) {
            return candidate;
        }
        n += 1;
    }
}

fn rename_let_binders(expr: PseudoExpr, renames: &HashMap<VarId, String>) -> PseudoExpr {
    struct BinderRenamer<'a> {
        renames: &'a HashMap<VarId, String>,
    }
    impl ExprFolder for BinderRenamer<'_> {
        fn post_let(
            &mut self,
            name: String,
            id: Option<VarId>,
            value: PseudoExpr,
            body: PseudoExpr,
        ) -> PseudoExpr {
            let name = match id {
                Some(vid) if self.renames.contains_key(&vid) => self.renames[&vid].clone(),
                _ => name,
            };
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }

        fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
            pattern
        }
    }
    BinderRenamer { renames }.fold(expr)
}

/// Visit each direct child expression of `expr`.
fn for_each_child<'a>(expr: &'a PseudoExpr, f: &mut dyn FnMut(&'a PseudoExpr)) {
    match expr {
        PseudoExpr::Let { value, body, .. } => {
            f(value);
            f(body);
        }
        PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => f(body),
        PseudoExpr::Apply { function, args } => {
            f(function);
            args.iter().for_each(f);
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            f(condition);
            f(then_branch);
            f(else_branch);
        }
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            f(subject);
            for c in clauses {
                if let crate::pseudo::ast::WhenPattern::Literal(e) = &c.pattern {
                    f(e);
                }
                if let Some(g) = &c.guard {
                    f(g);
                }
                f(&c.body);
            }
        }
        PseudoExpr::BinOp { left, right, .. } => {
            f(left);
            f(right);
        }
        PseudoExpr::UnOp { operand, .. } => f(operand),
        PseudoExpr::Constr { fields, .. } => fields.iter().for_each(f),
        PseudoExpr::BuiltinCall { args, .. } => args.iter().for_each(f),
        PseudoExpr::List { elements, tail } => {
            elements.iter().for_each(&mut *f);
            if let Some(t) = tail {
                f(t);
            }
        }
        PseudoExpr::Tuple(items) => items.iter().for_each(f),
        PseudoExpr::Pair(a, b) => {
            f(a);
            f(b);
        }
        PseudoExpr::FieldAccess { record, .. } => f(record),
        PseudoExpr::IndexAccess { collection, .. } => f(collection),
        PseudoExpr::Trace { message, value } => {
            f(message);
            f(value);
        }
        PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => f(inner),
        _ => {}
    }
}

#[cfg(test)]
mod tests;
