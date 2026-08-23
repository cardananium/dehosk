//! Recover Constr-encoded list cons cells whose tail is a hoisted const/let
//! (or a chain of them) into a native spread `[head, ..tail]`.
//!
//! A data-encoded cons is `Constr<1>(head, tail)` terminating in
//! `Constr<0>` (nil). `simplify_constr` folds that chain into a `List`
//! only when it is fully inline and ends in nil; after CSE hoists the
//! tail into a `Let`, the cell prints as `Unknown_E_2_1(head, tail)`
//! while identical inline sites already print `[head, other]`. This
//! pass runs after that hoist and folds to
//! `List { elements: [head..], tail: Some(tailVar) }` when `tail`
//! provably resolves to a list.
//!
//! Fail-closed on over-fire: `Unknown_E_2` can merge unrelated
//! constructors — `Constr<0>(Data, Data)` may be a genuine `(enum, list)`
//! pair. Only tag-1 arity-2 constructors whose second field resolves to
//! a list are folded; the tag-0 pair is never touched.
//!
//! `resolves_to_list` chases the collected `Let`-value table by VarId
//! (cycle-guarded) and returns true only for a `List` node, a nil
//! `Constr<0>` (arity 0), a cons `Constr<1>` arity-2 whose own second
//! field resolves, or a `Var` whose unique binding does. An opaque
//! `Var`, a `Constr<0>` pair (arity 2), a builtin, or an `Apply` is not
//! a list, so the stub stays.

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::rewrite_bottom_up;

pub(super) fn recover_constr_cons_spread(expr: PseudoExpr) -> PseudoExpr {
    let table = collect_let_values(&expr);
    rewrite(expr, &table)
}

/// Map every `Let` binder `VarId` to a clone of its bound value. Uses
/// `fold::ExprVisitor` so nested lets and `WhenPattern::Literal` payloads are
/// all seen.
fn collect_let_values(expr: &PseudoExpr) -> HashMap<VarId, PseudoExpr> {
    struct Collector {
        table: HashMap<VarId, PseudoExpr>,
    }
    impl ExprVisitor for Collector {
        fn visit_let_value_post(&mut self, _name: &str, id: &Option<VarId>, value: &PseudoExpr) {
            if let Some(vid) = id {
                self.table.entry(*vid).or_insert_with(|| value.clone());
            }
        }
    }
    let mut c = Collector {
        table: HashMap::new(),
    };
    c.walk(expr);
    c.table
}

/// Bottom-up rewrite: each node is rebuilt from its already-rewritten
/// children, then handed to [`try_fold_cons_spread`].
fn rewrite(expr: PseudoExpr, table: &HashMap<VarId, PseudoExpr>) -> PseudoExpr {
    rewrite_bottom_up(expr, |e| try_fold_cons_spread(e, table))
}

/// A tag-1 arity-2 constructor is a cons-cell candidate — either the church/
/// data `Known(Cons)` or the stub `Unknown { tag: 1, arity: 2 }`.
fn is_cons_shape(shape: &ConstructorShape) -> bool {
    matches!(
        shape,
        ConstructorShape::Known(KnownConstructor::Cons)
            | ConstructorShape::Unknown {
                tag: 1,
                arity: 2,
                ..
            }
    )
}

/// A nil-cell terminator: ONLY the recovered `Known(Nil)`.
///
/// The generic `Unknown { tag: 0, arity: 0 }` stub is DELIBERATELY excluded:
/// its surface is `Unknown_E_0_0`, not `[]`, and it is shared with genuine
/// nullary enum values. Treating it as a list terminator would fold cons
/// cells whose "list-ness" isn't actually established, producing a spread
/// with a stub-displayed tail (`[x, ..Unknown_E_0_0]`) — a NEW inconsistency.
/// Fail-closed: a chain must terminate in a `Known(Nil)` or a `List` (direct
/// or through a `Var`), never a bare nullary stub.
fn is_nil_shape(shape: &ConstructorShape) -> bool {
    matches!(shape, ConstructorShape::Known(KnownConstructor::Nil))
}

/// Fail-closed proof that `expr` renders as a list. Chases `Var`s through
/// the collected `Let`-value table (cycle-guarded).
///
/// Deliberately scoped: this does NOT prove a list through a function CALL
/// (`Apply`). A recursive list-map builder (`[] -> Unknown_E_0_0;
/// [_, ..t] -> Constr<1>(f(head), i(t))`) is left alone — its nil arm is
/// the SHARED nullary stub, so folding its cons arm to `[head, ..i(t)]`
/// while the nil arm stays `Unknown_E_0_0` would just create a NEW
/// inconsistency. Recovering it needs a coordinated nil-arm relabel that
/// respects the shared stub, which this pass does not attempt.
fn resolves_to_list(
    expr: &PseudoExpr,
    table: &HashMap<VarId, PseudoExpr>,
    visiting: &mut HashSet<VarId>,
) -> bool {
    let mut current = expr;
    let mut inserted: Vec<VarId> = Vec::new();
    let result = loop {
        match current {
            PseudoExpr::List { .. } => break true,
            PseudoExpr::Constr {
                tag, fields, shape, ..
            } => {
                if is_nil_shape(shape) {
                    break true;
                }
                if is_cons_shape(shape) && *tag == 1 && fields.len() == 2 {
                    current = &fields[1];
                    continue;
                }
                break false;
            }
            PseudoExpr::Var { id: Some(vid), .. } => {
                if !visiting.insert(*vid) {
                    // cycle — cannot prove
                    break false;
                }
                inserted.push(*vid);
                match table.get(vid) {
                    Some(value) => current = value,
                    None => break false,
                }
            }
            _ => break false,
        }
    };
    for vid in inserted {
        visiting.remove(&vid);
    }
    result
}

/// If `expr` is a cons-cell `Constr<1>(head, tail)` whose tail provably
/// resolves to a list, fold the (possibly nested inline) cons chain into a
/// `List { elements, tail }` spread. Otherwise return `expr` unchanged.
fn try_fold_cons_spread(expr: PseudoExpr, table: &HashMap<VarId, PseudoExpr>) -> PseudoExpr {
    let PseudoExpr::Constr {
        tag: 1,
        ref fields,
        ref shape,
        ..
    } = expr
    else {
        return expr;
    };
    if !is_cons_shape(shape) || fields.len() != 2 {
        return expr;
    }
    // Gate: the tail (second field) must provably resolve to a list — what
    // distinguishes a genuine cons cell from a coincidental tag-1 arity-2
    // constructor whose second field is opaque.
    if !resolves_to_list(&fields[1], table, &mut HashSet::new()) {
        return expr;
    }

    // Peel the inline cons chain: collect heads while the running tail is
    // itself an inline cons cell. The first non-cons tail (a `List`, a nil,
    // or a list-resolving `Var`) becomes the spread tail (or `None` when it
    // is nil / an empty list).
    let PseudoExpr::Constr { fields, .. } = expr else {
        unreachable!("matched Constr above");
    };
    let mut fields = fields;
    let tail = fields.pop().expect("arity 2");
    let head = fields.pop().expect("arity 2");
    let mut elements = vec![head];
    let mut running_tail = tail;

    loop {
        match running_tail {
            PseudoExpr::Constr {
                tag: 1,
                fields,
                shape,
                ..
            } if is_cons_shape(&shape) && fields.len() == 2 => {
                let mut fields = fields;
                let inner_tail = fields.pop().expect("arity 2");
                let inner_head = fields.pop().expect("arity 2");
                elements.push(inner_head);
                running_tail = inner_tail;
            }
            PseudoExpr::Constr { ref shape, .. } if is_nil_shape(shape) => {
                return PseudoExpr::List {
                    elements: elements.into(),
                    tail: None,
                };
            }
            PseudoExpr::List {
                elements: mut inline_elems,
                tail: inline_tail,
            } => {
                // Merge an inline list literal tail directly:
                //   [a, ..[b, c]]       -> [a, b, c]
                //   [a, ..[b, ..rest]]  -> [a, b, ..rest]
                elements.append(&mut inline_elems);
                return PseudoExpr::List {
                    elements: elements.into(),
                    tail: inline_tail,
                };
            }
            other => {
                // A list-resolving `Var` (or any other proven-list node):
                // emit it as the spread tail.
                return PseudoExpr::List {
                    elements: elements.into(),
                    tail: Some(PBox::new(other)),
                };
            }
        }
    }
}

#[cfg(test)]
mod tests;
