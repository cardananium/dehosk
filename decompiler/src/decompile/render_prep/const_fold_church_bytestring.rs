//! Const-fold the church-bytestring-from-bytes construction
//! `s5(o5([b1, b2, ..., bN]))` to a raw `#"<hex>"` literal.
//!
//! A compiled script emits two helpers: `o5` maps each byte to a
//! 1-byte bytestring and builds a church-list of those; `s5` folds
//! that list with `#""` initial and `<>` step. Over a literal int
//! list the composition is a compile-time constant — typically a
//! script hash used in an equality check.
//!
//! Detect `Apply(Var(s5_id), [Apply(Var(o5_id), [List<Int>])])`,
//! verify both helpers match those structural shapes, and replace
//! with `PseudoExpr::ByteArray(<bytes>)`.
//!
//! Strict shape match on both helpers; any mismatch refuses the
//! fold. Every list element must be an integer literal in `0..=255`.
//! Each helper's recursive self-reference is verified by `VarId`,
//! not by name, so a name collision cannot produce a false
//! positive. The `o5` cons-arm `church_cons` call is matched by
//! name on the Var, so a rename elsewhere silently stops the fold —
//! under-folding is preferred to mis-folding.

use crate::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, PseudoExpr, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::rewrite_top_down_pruning;
use std::collections::HashMap;

pub(super) fn const_fold_church_bytestring(expr: PseudoExpr) -> PseudoExpr {
    let mut env: HashMap<VarId, PseudoExpr> = HashMap::new();
    collect_let_bindings(&expr, &mut env);
    let folded = rewrite(expr, &env);
    // Folding can leave the `o5`/`s5` helper lets unreferenced.
    // Drop a let only when its value matches one of the two helper
    // shapes AND its binder is unreferenced in `body`.
    drop_dead_church_helper_lets(folded)
}

fn drop_dead_church_helper_lets(expr: PseudoExpr) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;

    struct DropDeadHelperLets;

    impl ExprFolder for DropDeadHelperLets {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_let(
            &mut self,
            name: String,
            id: Option<VarId>,
            value: PseudoExpr,
            body: PseudoExpr,
        ) -> PseudoExpr {
            if let Some(vid) = id {
                let is_target_shape =
                    is_bytes_to_church_list(&value) || is_church_list_to_bytestring_fold(&value);
                if is_target_shape && !contains_var_id_ref(&body, vid) {
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

    DropDeadHelperLets.fold(expr)
}

fn contains_var_id_ref(expr: &PseudoExpr, target: VarId) -> bool {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Var { id: Some(v), .. } => {
                if *v == target {
                    return true;
                }
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { body, .. } => pending.push(body),
            PseudoExpr::RecFn { body, .. } => pending.push(body),
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
                pending.push(function);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for c in clauses.iter().rev() {
                    pending.push(&c.body);
                    if let Some(g) = c.guard.as_ref() {
                        pending.push(g);
                    }
                }
                pending.push(subject);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
                pending.push(condition);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    pending.push(f);
                }
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail.as_ref() {
                    pending.push(t);
                }
                for e in elements.iter().rev() {
                    pending.push(e);
                }
            }
            PseudoExpr::Tuple(elements) => {
                for e in elements.iter().rev() {
                    pending.push(e);
                }
            }
            PseudoExpr::Pair(a, b) => {
                pending.push(b);
                pending.push(a);
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            _ => {}
        }
    }
    false
}

/// Collect every `Let { id: Some(vid), value, .. }` into a flat env;
/// binders are globally unique by `VarId`, so no scoping is needed.
fn collect_let_bindings(expr: &PseudoExpr, env: &mut HashMap<VarId, PseudoExpr>) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Let {
                id: Some(vid),
                value,
                body,
                ..
            } => {
                env.insert(*vid, (**value).clone());
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { body, .. } => pending.push(body),
            PseudoExpr::RecFn { body, .. } => pending.push(body),
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
                pending.push(function);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for c in clauses.iter().rev() {
                    pending.push(&c.body);
                    if let Some(g) = &c.guard {
                        pending.push(g);
                    }
                }
                pending.push(subject);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
                pending.push(condition);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    pending.push(f);
                }
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    pending.push(t);
                }
                for e in elements.iter().rev() {
                    pending.push(e);
                }
            }
            PseudoExpr::Tuple(elements) => {
                for e in elements.iter().rev() {
                    pending.push(e);
                }
            }
            PseudoExpr::Pair(a, b) => {
                pending.push(b);
                pending.push(a);
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            _ => {}
        }
    }
}

/// Top-down with pruning, as before: firing at a node replaces the subtree,
/// so it is never walked. `recurse` is gone — the helper does that descent.
fn rewrite(expr: PseudoExpr, env: &HashMap<VarId, PseudoExpr>) -> PseudoExpr {
    rewrite_top_down_pruning(expr, |node| try_fold(node, env))
}

/// Try to fold the entire `s5(o5([bytes]))` pattern. Returns the
/// resulting `ByteArray` literal on success, `None` on any mismatch.
fn try_fold(expr: &PseudoExpr, env: &HashMap<VarId, PseudoExpr>) -> Option<PseudoExpr> {
    // Outer: Apply(s5, [inner_call])
    let PseudoExpr::Apply { function, args } = expr else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    let s5_id = var_id_of(function)?;
    let s5_def = env.get(&s5_id)?;
    if !is_church_list_to_bytestring_fold(s5_def) {
        return None;
    }

    // Inner: Apply(o5, [List<Int>])
    let PseudoExpr::Apply {
        function: inner_fn,
        args: inner_args,
    } = &args[0]
    else {
        return None;
    };
    if inner_args.len() != 1 {
        return None;
    }
    let o5_id = var_id_of(inner_fn)?;
    let o5_def = env.get(&o5_id)?;
    if !is_bytes_to_church_list(o5_def) {
        return None;
    }

    // Argument: literal list of u8 ints
    let PseudoExpr::List {
        elements,
        tail: None,
    } = &inner_args[0]
    else {
        return None;
    };
    let bytes = extract_byte_list(elements)?;
    Some(PseudoExpr::ByteArray(bytes))
}

fn var_id_of(expr: &PseudoExpr) -> Option<VarId> {
    match expr {
        PseudoExpr::Var { id: Some(v), .. } => Some(*v),
        _ => None,
    }
}

fn extract_byte_list(elements: &[PseudoExpr]) -> Option<Vec<u8>> {
    elements
        .iter()
        .map(|e| match e {
            PseudoExpr::Int(n) => {
                use num_traits::ToPrimitive;
                let v = n.to_u8()?;
                Some(v)
            }
            _ => None,
        })
        .collect()
}

/// Match `rec fn self(xs) { xs(#"", fn(x, y) { x <> self(y) }) }`.
fn is_church_list_to_bytestring_fold(expr: &PseudoExpr) -> bool {
    let PseudoExpr::RecFn { name, params, body } = expr else {
        return false;
    };
    if params.len() != 1 {
        return false;
    }
    let arg_id = params[0].id;
    let self_id = name.id;

    // body = Apply(Var(arg), [ByteArray(empty), Lambda(2 args, body)])
    let PseudoExpr::Apply { function, args } = body.as_ref() else {
        return false;
    };
    if !var_matches(function, arg_id) {
        return false;
    }
    if args.len() != 2 {
        return false;
    }
    // arg 0: empty ByteArray (nil case = #"")
    if !matches!(&args[0], PseudoExpr::ByteArray(b) if b.is_empty()) {
        return false;
    }
    // arg 1: Lambda(x, y, x <> self(y))
    let PseudoExpr::Lambda {
        params: lp,
        body: lbody,
    } = &args[1]
    else {
        return false;
    };
    if lp.len() != 2 {
        return false;
    }
    let x_id = lp[0].id;
    let y_id = lp[1].id;
    let PseudoExpr::BinOp {
        op: BinaryOp::Concat,
        left,
        right,
    } = lbody.as_ref()
    else {
        return false;
    };
    if !var_matches(left, x_id) {
        return false;
    }
    // right = Apply(Var(self), [Var(y)])
    let PseudoExpr::Apply {
        function: rfn,
        args: rargs,
    } = right.as_ref()
    else {
        return false;
    };
    if !var_matches(rfn, self_id) {
        return false;
    }
    if rargs.len() != 1 || !var_matches(&rargs[0], y_id) {
        return false;
    }
    true
}

/// Match
/// `rec fn self(xs) { when xs is { [] -> _; [h, ..t] -> church_cons(ByteArray.push(h, #""), self(t)) } }`.
fn is_bytes_to_church_list(expr: &PseudoExpr) -> bool {
    let PseudoExpr::RecFn { name, params, body } = expr else {
        return false;
    };
    if params.len() != 1 {
        return false;
    }
    let arg_id = params[0].id;
    let self_id = name.id;

    let PseudoExpr::When {
        subject, clauses, ..
    } = body.as_ref()
    else {
        return false;
    };
    if !var_matches(subject, arg_id) {
        return false;
    }
    if clauses.len() != 2 {
        return false;
    }
    let (nil_arm, cons_arm) = match (
        is_list_nil_pattern(&clauses[0].pattern),
        is_list_nil_pattern(&clauses[1].pattern),
    ) {
        (true, false) => (&clauses[0], &clauses[1]),
        (false, true) => (&clauses[1], &clauses[0]),
        _ => return false,
    };
    // Cons arm pattern: either `[h, ..t]` (List shape) or
    // `Cons(h, t)` (Constructor shape with KnownConstructor::Cons).
    let (h_id, t_id) = match &cons_arm.pattern {
        WhenPattern::List {
            elements,
            tail: Some(t),
        } if elements.len() == 1 => (elements[0].id, t.id),
        WhenPattern::Constructor {
            shape: ConstructorShape::Known(KnownConstructor::Cons),
            fields,
            ..
        } if fields.len() == 2 => (fields[0].id, fields[1].id),
        _ => return false,
    };

    let PseudoExpr::Apply { function, args } = &cons_arm.body else {
        return false;
    };
    // Matched by name: `church_cons` is a hoisted helper with no
    // stable `VarId`. The matcher peels the UPLC's `force` wrappers.
    if !var_name_matches(function, "church_cons") {
        return false;
    }
    if args.len() != 2 {
        return false;
    }
    // arg 0: ByteArray.push(h, #"")
    if !is_byte_push_of(&args[0], h_id) {
        return false;
    }
    // arg 1: self(t)
    let PseudoExpr::Apply {
        function: rfn,
        args: rargs,
    } = &args[1]
    else {
        return false;
    };
    if !var_matches(rfn, self_id) {
        return false;
    }
    if rargs.len() != 1 || !var_matches(&rargs[0], t_id) {
        return false;
    }
    // Nil arm: body can be anything — the call site's list is
    // non-empty, so the nil case never runs.
    let _ = nil_arm;
    true
}

/// Match the empty-list pattern in either form:
/// - `WhenPattern::List { elements: [], tail: None }` (idiomatic)
/// - `WhenPattern::Constructor { shape: Known(Nil), .. }` (church-encoded)
fn is_list_nil_pattern(p: &WhenPattern) -> bool {
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

fn is_byte_push_of(expr: &PseudoExpr, h_id: VarId) -> bool {
    let PseudoExpr::BuiltinCall { name, args } = expr else {
        return false;
    };
    if *name != BuiltinId::ByteArrayPush {
        return false;
    }
    if args.len() != 2 {
        return false;
    }
    if !var_matches(&args[0], h_id) {
        return false;
    }
    matches!(&args[1], PseudoExpr::ByteArray(b) if b.is_empty())
}

fn var_matches(expr: &PseudoExpr, expected: VarId) -> bool {
    let inner = strip_forces(expr);
    matches!(inner, PseudoExpr::Var { id: Some(v), .. } if *v == expected)
}

/// Strip any number of `Force(...)` wrappers. Pseudo-AST
/// identifiers often retain `Force` layers from the original UPLC,
/// which structural matching must see through.
fn strip_forces(expr: &PseudoExpr) -> &PseudoExpr {
    let mut cur = expr;
    while let PseudoExpr::Force(inner) = cur {
        cur = inner.as_ref();
    }
    cur
}

/// Match a Var by NAME, transparently peeling `Force(...)` wrappers.
fn var_name_matches(expr: &PseudoExpr, expected: &str) -> bool {
    let inner = strip_forces(expr);
    matches!(inner, PseudoExpr::Var { name, .. } if name == expected)
}
