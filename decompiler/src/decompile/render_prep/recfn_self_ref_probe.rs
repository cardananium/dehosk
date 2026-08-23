//! Diagnostic for `RecFn` bodies with value-context self-
//! references — uses of the rec-fn's own `name.id` outside
//! `Apply.function` position. They surface as the "match
//! recursive function as Ordering" rendering: type-erased UPLC
//! residue where a PlutusTx case-analysis on an ADT got
//! conflated with the Y-combinator's self-reference.
//!
//! `mid/patterns::mark_closure_recursive` sets the rec-fn's
//! `recursive` field to the outer let-binder's VarId, and that
//! VarId then surfaces as both the rec-fn name and a
//! value-context use inside the body. The AST tracks what UPLC
//! encoded; without source-level info there is nothing to fix.
//!
//! With env-var `DEBUG_RECFN_SELF_REF` set, enumerates the
//! offending rec-fns and their context; otherwise a no-op.

use crate::pseudo::ast::{PseudoExpr, WhenClause};
use crate::pseudo::var_id::VarId;

pub(super) fn recfn_self_ref_probe(expr: PseudoExpr) -> PseudoExpr {
    if crate::debug_env::recfn_self_ref() {
        walk(&expr);
    }
    expr
}

fn walk(expr: &PseudoExpr) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::RecFn {
            name,
            params: _,
            body,
        } = cur
        {
            let self_id = name.id;
            let mut value_refs: Vec<&'static str> = Vec::new();
            scan_value_refs(body, self_id, &mut value_refs);
            if !value_refs.is_empty() {
                eprintln!(
                    "[recfn_probe] rec fn {} (id={:?}) — {} value-context self refs:",
                    name.name,
                    name.id,
                    value_refs.len()
                );
                for ctx in value_refs.iter().take(5) {
                    eprintln!("    in: {}", ctx);
                }
            }
        }
        pending.extend(super::scope_recurse::children(cur).into_iter().rev());
    }
}

fn scan_value_refs(expr: &PseudoExpr, target: VarId, out: &mut Vec<&'static str>) {
    enum Task<'a> {
        Node(&'a PseudoExpr),
        /// Check `node` for being a bare `Var(target)`, push `tag` if so,
        /// then visit `node` normally (which independently pushes
        /// "bare-Var" for that same case).
        TaggedCheck {
            node: &'a PseudoExpr,
            tag: &'static str,
        },
    }

    let mut pending: Vec<Task> = vec![Task::Node(expr)];
    while let Some(task) = pending.pop() {
        let cur = match task {
            Task::TaggedCheck { node, tag } => {
                if matches!(node, PseudoExpr::Var { id: Some(v), .. } if *v == target) {
                    out.push(tag);
                }
                node
            }
            Task::Node(node) => node,
        };
        match cur {
            PseudoExpr::Apply { function, args } => {
                // Pushed in reverse of the desired pop order: args (reversed)
                // first, function last — so function (on top) pops before
                // arg0, which pops before arg1, etc.
                for a in args.iter().rev() {
                    pending.push(Task::TaggedCheck {
                        node: a,
                        tag: "Apply-arg",
                    });
                }
                // Var(target) in function position is legit recursion; in an arg it is
                // a value-context use.
                if !matches!(function.as_ref(), PseudoExpr::Var { id: Some(v), .. } if *v == target)
                {
                    pending.push(Task::Node(function));
                }
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for c in clauses.iter().rev() {
                    pending.push(Task::Node(&c.body));
                    if let Some(g) = &c.guard {
                        pending.push(Task::Node(g));
                    }
                }
                pending.push(Task::TaggedCheck {
                    node: subject,
                    tag: "When-subject",
                });
            }
            PseudoExpr::Var { id: Some(v), .. } if *v == target => {
                out.push("bare-Var");
            }
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
            other => {
                for c in super::scope_recurse::children(other).into_iter().rev() {
                    pending.push(Task::Node(c));
                }
            }
        }
    }
    let _ = WhenClause {
        pattern: crate::pseudo::ast::WhenPattern::Wildcard,
        guard: None,
        body: PseudoExpr::Unit,
    };
}
