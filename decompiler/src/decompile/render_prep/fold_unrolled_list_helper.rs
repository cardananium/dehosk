//! Fold a list-walking helper that was unrolled N levels deep back into a
//! single call:
//!   `when xs is { [] -> NIL   [h, ..t] -> [E(h), ..helper(a, t)] }`
//!     →  `helper(a, xs)`
//! when `helper` is the recursive map `rec fn helper(p, ys) { when ys is
//! { [] -> NIL; [h, ..t] -> [E(h), ..helper(p, t)] } }` and `E` is the
//! helper's element expression with `p := a`. Compilers that unroll a `map`
//! leave N nested copies of this `when`, bottoming out in a call to the
//! helper; bottom-up, the innermost level folds first (its tail is already a
//! helper call), which makes the next level up match, and so on.
//!
//! The identity copy (`E(h) = h`, no extra parameters) is the common case:
//! `helper(xs)` is `xs`, so the whole ladder folds to the list itself.
//!
//! Gated by VarId: the element expression must be the helper's own, modulo
//! the helper parameter ↦ call argument and head ↦ the arm's own binder
//! substitution, and the arguments may not mention the arm's binders. The
//! subject is passed on, so its single evaluation is preserved. The helper's
//! own body is never rewritten (it would become a call to itself); the
//! definition is left for the dead-let sweep once its last call is gone.

use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::rewrite_bottom_up;

/// A recursive map over one list parameter (the last), threading `extra`
/// parameters unchanged.
struct Helper {
    extra: Vec<VarId>,
    list_param: VarId,
    head: VarId,
    elem: PseudoExpr,
    /// The variable-free value the helper returns for the empty list.
    nil: PseudoExpr,
}

impl Helper {
    fn is_identity(&self) -> bool {
        self.extra.is_empty() && is_var(&self.elem, self.head)
    }
}

pub(super) fn fold_unrolled_list_helper(expr: PseudoExpr) -> PseudoExpr {
    let mut helpers = HashMap::new();
    collect_helpers(&expr, &mut helpers);
    rewrite_bottom_up(expr, |node| fold_node(node, &helpers))
}

fn collect_helpers(expr: &PseudoExpr, out: &mut HashMap<VarId, std::rc::Rc<Helper>>) {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if let Some((name, helper)) = parse_helper(node) {
            let helper = std::rc::Rc::new(helper);
            out.insert(name, helper.clone());
        }
        // Call sites outside the helper refer to the enclosing let's id.
        if let PseudoExpr::Let {
            id: Some(let_id),
            value,
            ..
        } = node
            && let Some((_, helper)) = parse_helper(value)
        {
            out.insert(*let_id, std::rc::Rc::new(helper));
        }
        node.child_refs_into(&mut stack);
    }
}

fn parse_helper(expr: &PseudoExpr) -> Option<(VarId, Helper)> {
    let PseudoExpr::RecFn { name, params, body } = expr else {
        return None;
    };
    let (list_param, extra) = params.split_last()?;
    let PseudoExpr::When {
        subject, clauses, ..
    } = body.as_ref()
    else {
        return None;
    };
    if !is_var(subject, list_param.id) {
        return None;
    }
    let (nil, cons) = split_nil_cons(clauses)?;
    if mentions_any_var(&nil.body) {
        return None;
    }
    let (h, t) = cons_binders(&cons.pattern)?;
    let (elem, tail) = cons_parts(&cons.body)?;
    let PseudoExpr::Apply { function, args } = tail else {
        return None;
    };
    if !is_var(function, name.id) || args.len() != params.len() {
        return None;
    }
    let forwards_params = extra
        .iter()
        .zip(args.iter())
        .all(|(p, a)| is_var(a, p.id))
        && is_var(&args[args.len() - 1], t.id);
    if !forwards_params || mentions_any(elem, &[t.id, name.id, list_param.id]) {
        return None;
    }
    Some((
        name.id,
        Helper {
            extra: extra.iter().map(|p| p.id).collect(),
            list_param: list_param.id,
            head: h.id,
            elem: elem.clone(),
            nil: nil.body.clone(),
        },
    ))
}

fn fold_node(expr: PseudoExpr, helpers: &HashMap<VarId, std::rc::Rc<Helper>>) -> PseudoExpr {
    match expr {
        PseudoExpr::Apply { function, args }
            if args.len() == 1
                && helper_for_call(&function, helpers).is_some_and(|h| h.is_identity()) =>
        {
            args.into_iter().next().expect("one argument")
        }
        PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } => match try_fold_level(&subject, &clauses, helpers) {
            Some(folded) => folded,
            None => PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            },
        },
        other => other,
    }
}

fn helper_for_call<'a>(
    function: &PseudoExpr,
    helpers: &'a HashMap<VarId, std::rc::Rc<Helper>>,
) -> Option<&'a Helper> {
    match function {
        PseudoExpr::Var { id: Some(f), .. } => helpers.get(f).map(|h| h.as_ref()),
        _ => None,
    }
}

fn try_fold_level(
    subject: &PseudoExpr,
    clauses: &[WhenClause],
    helpers: &HashMap<VarId, std::rc::Rc<Helper>>,
) -> Option<PseudoExpr> {
    let (nil, cons) = split_nil_cons(clauses)?;
    let (h, t) = cons_binders(&cons.pattern)?;
    let (elem, tail) = cons_parts(&cons.body)?;
    // Plain copy: `[h, ..t]` rebuilt as is. Calls to the identity helper were
    // already rewritten to their argument, so a ladder bottoms out here.
    if is_var(elem, h.id) && is_var(tail, t.id) && is_empty_list_literal(&nil.body) {
        return Some(subject.clone());
    }
    let PseudoExpr::Apply { function, args } = tail else {
        return None;
    };
    let helper = helper_for_call(function, helpers)?;
    // The helper's own body is the one place this shape must stay.
    if is_var(subject, helper.list_param)
        || args.len() != helper.extra.len() + 1
        || nil.body != helper.nil
    {
        return None;
    }
    let (last, call_args) = args.split_last()?;
    if !is_var(last, t.id) || call_args.iter().any(|a| mentions_any(a, &[h.id, t.id])) {
        return None;
    }
    let mut map: HashMap<VarId, Binding> = HashMap::new();
    for (p, a) in helper.extra.iter().zip(call_args) {
        map.insert(*p, Binding::Expr(a));
    }
    map.insert(helper.head, Binding::Id(h.id));
    if !eq_under(&helper.elem, elem, &map) {
        return None;
    }
    let mut new_args: Vec<PseudoExpr> = call_args.to_vec();
    new_args.push(subject.clone());
    Some(PseudoExpr::Apply {
        function: function.clone(),
        args: new_args.into(),
    })
}

enum Binding<'a> {
    Expr(&'a PseudoExpr),
    Id(VarId),
}

/// Structural equality of the helper's element expression (`h`) against a
/// level's (`c`), reading helper-bound variables through `map`.
fn eq_under(h: &PseudoExpr, c: &PseudoExpr, map: &HashMap<VarId, Binding>) -> bool {
    match (h, c) {
        (PseudoExpr::Var { id: Some(hid), .. }, _) if map.contains_key(hid) => match &map[hid] {
            Binding::Expr(e) => *e == c,
            Binding::Id(v) => is_var(c, *v),
        },
        (PseudoExpr::Var { id: Some(a), .. }, PseudoExpr::Var { id: Some(b), .. }) => a == b,
        (PseudoExpr::Int(a), PseudoExpr::Int(b)) => a == b,
        (
            PseudoExpr::BinOp {
                op: oa,
                left: la,
                right: ra,
            },
            PseudoExpr::BinOp {
                op: ob,
                left: lb,
                right: rb,
            },
        ) => oa == ob && eq_under(la, lb, map) && eq_under(ra, rb, map),
        (
            PseudoExpr::BuiltinCall { name: na, args: aa },
            PseudoExpr::BuiltinCall { name: nb, args: ab },
        ) => na == nb && eq_all(aa, ab, map),
        (
            PseudoExpr::Apply {
                function: fa,
                args: aa,
            },
            PseudoExpr::Apply {
                function: fb,
                args: ab,
            },
        ) => eq_under(fa, fb, map) && eq_all(aa, ab, map),
        _ => false,
    }
}

fn eq_all(a: &[PseudoExpr], b: &[PseudoExpr], map: &HashMap<VarId, Binding>) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| eq_under(x, y, map))
}

fn split_nil_cons(clauses: &[WhenClause]) -> Option<(&WhenClause, &WhenClause)> {
    let [a, b] = clauses else { return None };
    if a.guard.is_some() || b.guard.is_some() {
        return None;
    }
    if is_nil_pattern(&a.pattern) {
        Some((a, b))
    } else if is_nil_pattern(&b.pattern) {
        Some((b, a))
    } else {
        None
    }
}

pub(super) fn is_nil_pattern(p: &WhenPattern) -> bool {
    match p {
        WhenPattern::List {
            elements,
            tail: None,
        } => elements.is_empty(),
        WhenPattern::Constructor {
            shape: ConstructorShape::Known(KnownConstructor::Nil),
            fields,
            ..
        } => fields.is_empty(),
        _ => false,
    }
}

/// The head and tail binders of a one-element cons pattern, in either spelling.
pub(super) fn cons_binders(p: &WhenPattern) -> Option<(&Binder, &Binder)> {
    match p {
        WhenPattern::List {
            elements,
            tail: Some(t),
        } => match elements.as_slice() {
            [h] => Some((h, t)),
            _ => None,
        },
        WhenPattern::Constructor {
            shape: ConstructorShape::Known(KnownConstructor::Cons),
            fields,
            ..
        } => match fields.as_slice() {
            [h, t] => Some((h, t)),
            _ => None,
        },
        _ => None,
    }
}

/// The head and tail of a cons cell, in either spelling.
fn cons_parts(e: &PseudoExpr) -> Option<(&PseudoExpr, &PseudoExpr)> {
    match e {
        PseudoExpr::List {
            elements,
            tail: Some(tail),
        } => match elements.as_slice() {
            [elem] => Some((elem, tail.as_ref())),
            _ => None,
        },
        PseudoExpr::Constr {
            shape: ConstructorShape::Known(KnownConstructor::Cons),
            fields,
            ..
        } => match fields.as_slice() {
            [elem, tail] => Some((elem, tail)),
            _ => None,
        },
        _ => None,
    }
}

fn is_empty_list_literal(e: &PseudoExpr) -> bool {
    matches!(e, PseudoExpr::List { elements, tail: None } if elements.is_empty())
}

fn is_var(e: &PseudoExpr, id: VarId) -> bool {
    matches!(e, PseudoExpr::Var { id: Some(v), .. } if *v == id)
}

fn mentions_any_var(e: &PseudoExpr) -> bool {
    let mut stack = vec![e];
    while let Some(n) = stack.pop() {
        if matches!(n, PseudoExpr::Var { .. }) {
            return true;
        }
        n.child_refs_into(&mut stack);
    }
    false
}

fn mentions_any(e: &PseudoExpr, ids: &[VarId]) -> bool {
    let wanted: HashSet<VarId> = ids.iter().copied().collect();
    let mut stack = vec![e];
    while let Some(n) = stack.pop() {
        if matches!(n, PseudoExpr::Var { id: Some(v), .. } if wanted.contains(v)) {
            return true;
        }
        n.child_refs_into(&mut stack);
    }
    false
}

#[cfg(test)]
mod tests;
