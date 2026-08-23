//! Rename `helper_N` bindings when the body is a recognized 2-param
//! arithmetic / comparison / church-bool / church-cons / church-pair
//! shape (`add_int`, `church_eq`, …).
//!
//! Only `helper_<digits>` binders match. Operands must be exactly
//! `Var(p0)` / `Var(p1)` in that order. A church-bool match also
//! requires both branches to be distinct outermost-chain zero-arity
//! `Constr` lets named `e`/`b` — a local spelled `e` cannot spoof it.

use crate::pseudo::ast::{BinaryOp, PseudoExpr};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;
use std::collections::HashMap;

pub(super) fn rename_semantic_helpers(expr: PseudoExpr) -> PseudoExpr {
    let mut renames: HashMap<VarId, String> = HashMap::new();
    let mut used: HashMap<String, usize> = HashMap::new();
    // Seed `used` with every existing binder name so a semantic
    // rename never collides with a name the earlier pipeline chose.
    seed_used_from_existing(&expr, &mut used);
    let church_bool_ids = collect_church_bool_const_ids(&expr);
    collect(&expr, &mut renames, &mut used, &church_bool_ids);
    if renames.is_empty() {
        return expr;
    }
    rewrite(expr, &renames)
}

/// Collect every binder name in `expr` (Let, Lambda params, RecFn
/// name + params, When subject-name + pattern binders), each
/// mapped to a count of 1, so `mint_unique_name` bumps it to 2
/// and hands out `<label>_2` for the first colliding rename.
fn seed_used_from_existing(expr: &PseudoExpr, used: &mut HashMap<String, usize>) {
    let record = |name: &str, used: &mut HashMap<String, usize>| {
        used.entry(name.to_string()).or_insert(1);
    };
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr {
            PseudoExpr::Let { name, .. } => record(name, used),
            PseudoExpr::Lambda { params, .. } => {
                for p in params {
                    record(&p.name, used);
                }
            }
            PseudoExpr::RecFn { name, params, .. } => {
                record(&name.name, used);
                for p in params {
                    record(&p.name, used);
                }
            }
            PseudoExpr::When {
                subject_name,
                clauses,
                ..
            } => {
                if let Some(sn) = subject_name {
                    record(&sn.name, used);
                }
                for clause in clauses {
                    seed_pattern_binders(&clause.pattern, used);
                }
            }
            _ => {}
        }
        pending.extend(super::scope_recurse::children(expr));
    }
}

fn seed_pattern_binders(
    pattern: &crate::pseudo::ast::WhenPattern,
    used: &mut HashMap<String, usize>,
) {
    use crate::pseudo::ast::WhenPattern;
    match pattern {
        WhenPattern::Constructor { fields, .. } => {
            for b in fields {
                used.entry(b.name.clone()).or_insert(1);
            }
        }
        WhenPattern::List { elements, tail } => {
            for b in elements {
                used.entry(b.name.clone()).or_insert(1);
            }
            if let Some(t) = tail {
                used.entry(t.name.clone()).or_insert(1);
            }
        }
        WhenPattern::Tuple(binders) => {
            for b in binders {
                used.entry(b.name.clone()).or_insert(1);
            }
        }
        WhenPattern::Pair(a, b) => {
            used.entry(a.name.clone()).or_insert(1);
            used.entry(b.name.clone()).or_insert(1);
        }
        WhenPattern::Var(b) => {
            used.entry(b.name.clone()).or_insert(1);
        }
        WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
    }
}

/// Collect VarIds of **outermost** `Let` bindings named exactly `e`
/// or `b` whose value is a zero-arity `Constr` (e.g.
/// `let e = Unknown_E_0_0`) — the legitimate church-bool tag
/// constants. Restricting to the outer Let-chain, to those two
/// names, and to tags 0/1 stops a domain-named
/// `let e = SomeUnrelatedCtor` in an unrelated scope from spoofing
/// the match.
fn collect_church_bool_const_ids(expr: &PseudoExpr) -> std::collections::HashSet<VarId> {
    let mut ids = std::collections::HashSet::new();
    let mut cursor = expr;
    while let PseudoExpr::Let {
        name,
        id: Some(let_id),
        value,
        body,
    } = cursor
    {
        if (name == "e" || name == "b") && is_zero_arity_constr_with_expected_tag(value, name) {
            ids.insert(*let_id);
        }
        cursor = body;
    }
    ids
}

/// `e` is the church-bool TRUE tag (canonical tag 0). `b` is the
/// FALSE tag (canonical tag 1). Allow either tag for either name
/// (some pipelines may flip on V2/V3) but require zero fields.
fn is_zero_arity_constr_with_expected_tag(expr: &PseudoExpr, _binder_name: &str) -> bool {
    matches!(
        expr,
        PseudoExpr::Constr { fields, tag, .. } if fields.is_empty() && *tag <= 1
    )
}

fn is_helper_binder(name: &str) -> bool {
    let Some(rest) = name.strip_prefix("helper_") else {
        return false;
    };
    !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit())
}

fn collect(
    expr: &PseudoExpr,
    renames: &mut HashMap<VarId, String>,
    used: &mut HashMap<String, usize>,
    church_bool_ids: &std::collections::HashSet<VarId>,
) {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        if let PseudoExpr::Let {
            name,
            id: Some(id),
            value,
            ..
        } = expr
            && is_helper_binder(name)
            && let Some(label) = recognize_helper_shape(value, church_bool_ids)
        {
            let unique = mint_unique_name(label, used);
            renames.insert(*id, unique);
        }
        pending.extend(super::scope_recurse::children(expr).into_iter().rev());
    }
}

fn mint_unique_name(label: &str, used: &mut HashMap<String, usize>) -> String {
    let count = used.entry(label.to_string()).or_insert(0);
    *count += 1;
    if *count == 1 {
        label.to_string()
    } else {
        format!("{label}_{count}")
    }
}

/// Match `Lambda { params: [p0, p1], body }` against known shapes.
fn recognize_helper_shape(
    value: &PseudoExpr,
    church_bool_ids: &std::collections::HashSet<VarId>,
) -> Option<&'static str> {
    let PseudoExpr::Lambda { params, body } = value else {
        return None;
    };
    if params.len() != 2 {
        return None;
    }
    let p0 = params[0].id;
    let p1 = params[1].id;
    // Arithmetic shapes.
    if let PseudoExpr::BinOp { op, left, right } = body.as_ref()
        && is_var(left, p0)
        && is_var(right, p1)
    {
        return Some(match op {
            BinaryOp::Add => "add_int",
            BinaryOp::Sub => "sub_int",
            BinaryOp::Mul => "mul_int",
            _ => return None,
        });
    }
    // Church-bool conditional shapes.
    if let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = body.as_ref()
        && let PseudoExpr::BinOp { op, left, right } = condition.as_ref()
        && is_var(left, p0)
        && is_var(right, p1)
    {
        // Both branches must be distinct KNOWN church-bool
        // Constr consts (from `collect_church_bool_const_ids`),
        // so a local or user-defined name that merely spells
        // `e` / `b` cannot match.
        let then_v = var_with_id(then_branch)?;
        let else_v = var_with_id(else_branch)?;
        if !church_bool_ids.contains(&then_v.1)
            || !church_bool_ids.contains(&else_v.1)
            || then_v.1 == else_v.1
        {
            return None;
        }
        let truthy_then = then_v.0 == "e" && else_v.0 == "b";
        let truthy_else = then_v.0 == "b" && else_v.0 == "e";
        if !truthy_then && !truthy_else {
            return None;
        }
        return Some(match (op, truthy_then) {
            (BinaryOp::Eq, true) => "church_eq",
            (BinaryOp::Eq, false) => "church_neq",
            (BinaryOp::Lt, true) => "church_lt",
            (BinaryOp::Lt, false) => "church_ge",
            (BinaryOp::Lte, true) => "church_le",
            (BinaryOp::Lte, false) => "church_gt",
            _ => return None,
        });
    }
    // `fn(x, y) { fn(_, k) { k(x, y) } }`  — church-cons
    // `fn(x, y) { fn(k)    { k(x, y) } }`  — church-pair (Scott pair)
    if let PseudoExpr::Lambda {
        params: inner_params,
        body: inner_body,
    } = body.as_ref()
        && let PseudoExpr::Apply { function, args } = inner_body.as_ref()
        && args.len() == 2
        && is_var(&args[0], p0)
        && is_var(&args[1], p1)
    {
        let cont_id = match inner_params.len() {
            // Pair: single continuation `k`.
            1 => inner_params[0].id,
            // Cons: ignored first slot + continuation `k`.
            2 => inner_params[1].id,
            _ => return None,
        };
        if is_var(function, cont_id) {
            return Some(if inner_params.len() == 2 {
                "church_cons"
            } else {
                "church_pair"
            });
        }
    }
    None
}

fn is_var(expr: &PseudoExpr, target: VarId) -> bool {
    matches!(expr, PseudoExpr::Var { id: Some(v), .. } if *v == target)
}

fn var_with_id(expr: &PseudoExpr) -> Option<(&str, VarId)> {
    if let PseudoExpr::Var { name, id: Some(id) } = expr {
        Some((name, *id))
    } else {
        None
    }
}

// `renames` is a fixed read-only map, so child order does not matter.
// `post_expr` runs once the node is fully reconstructed.
fn rewrite(expr: PseudoExpr, renames: &HashMap<VarId, String>) -> PseudoExpr {
    struct Renamer<'a> {
        renames: &'a HashMap<VarId, String>,
    }

    impl ExprFolder for Renamer<'_> {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_expr(&mut self, expr: PseudoExpr) -> PseudoExpr {
            match expr {
                PseudoExpr::Let {
                    name,
                    id: Some(id),
                    value,
                    body,
                } => {
                    let name = self.renames.get(&id).cloned().unwrap_or(name);
                    PseudoExpr::Let {
                        name,
                        id: Some(id),
                        value,
                        body,
                    }
                }
                PseudoExpr::Var { name, id: Some(id) } => {
                    let name = self.renames.get(&id).cloned().unwrap_or(name);
                    PseudoExpr::Var { name, id: Some(id) }
                }
                other => other,
            }
        }
    }

    Renamer { renames }.fold(expr)
}

#[cfg(test)]
mod tests;
