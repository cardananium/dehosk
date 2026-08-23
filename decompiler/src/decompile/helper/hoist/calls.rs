use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::references::pattern_binds_var;

pub(super) fn append_helper_call_args(
    expr: &PseudoExpr,
    fn_name: &str,
    fn_id: VarId,
    expected_arity: usize,
    extra_args: &[PseudoExpr],
) -> PseudoExpr {
    if extra_args.is_empty() {
        return expr.clone();
    }

    struct AppendHelperCallArgs<'a> {
        fn_name: &'a str,
        fn_id: VarId,
        expected_arity: usize,
        extra_args: &'a [PseudoExpr],
        blocked_depth: usize,
    }

    impl ExprFolder for AppendHelperCallArgs<'_> {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
            if params.iter().any(|param| param == self.fn_name) {
                self.blocked_depth += 1;
            }
            params.to_vec()
        }

        fn exit_lambda(&mut self, params: &[Binder]) {
            if params.iter().any(|param| param == self.fn_name) {
                self.blocked_depth -= 1;
            }
        }

        fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
            if name == self.fn_name || params.iter().any(|param| param == self.fn_name) {
                self.blocked_depth += 1;
            }
            (name.clone(), params.to_vec())
        }

        fn exit_recfn(&mut self, name: &Binder, params: &[Binder]) {
            if name == self.fn_name || params.iter().any(|param| param == self.fn_name) {
                self.blocked_depth -= 1;
            }
        }

        fn enter_let(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) -> String {
            if name == self.fn_name {
                self.blocked_depth += 1;
            }
            name.to_string()
        }

        fn exit_let(&mut self, name: &str) {
            if name == self.fn_name {
                self.blocked_depth -= 1;
            }
        }

        fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
            if self.blocked_depth == 0
                && matches!(&function, PseudoExpr::Var { name, id, .. } if helper_ref_matches(name, *id, self.fn_name, self.fn_id))
                && args.len() == self.expected_arity
            {
                let mut extended_args = args;
                extended_args.extend(self.extra_args.iter().cloned());
                PseudoExpr::Apply {
                    function: PBox::new(function),
                    args: extended_args.into(),
                }
            } else {
                PseudoExpr::Apply {
                    function: PBox::new(function),
                    args: args.into(),
                }
            }
        }
    }

    AppendHelperCallArgs {
        fn_name,
        fn_id,
        expected_arity,
        extra_args,
        blocked_depth: 0,
    }
    .fold(expr.clone())
}

fn helper_ref_matches(name: &str, id: Option<VarId>, fn_name: &str, fn_id: VarId) -> bool {
    crate::decompile::var_match::refs_match(name, id.get(), fn_name, fn_id.get())
}

pub(super) fn helper_is_direct_call_only(
    expr: &PseudoExpr,
    fn_name: &str,
    fn_id: VarId,
    expected_arity: usize,
) -> bool {
    enum Task<'a> {
        Node(&'a PseudoExpr, usize),
        CheckClause(&'a WhenClause, usize),
    }

    let mut pending = vec![Task::Node(expr, 0)];
    while let Some(task) = pending.pop() {
        let (cur, blocked_depth) = match task {
            Task::Node(cur, depth) => (cur, depth),
            Task::CheckClause(clause, base_depth) => {
                let depth = base_depth + usize::from(pattern_binds_var(&clause.pattern, fn_name));
                pending.push(Task::Node(&clause.body, depth));
                if let Some(guard) = clause.guard.as_ref() {
                    pending.push(Task::Node(guard, depth));
                }
                continue;
            }
        };
        match cur {
            PseudoExpr::Var { name, id, .. } => {
                if blocked_depth == 0 && helper_ref_matches(name, *id, fn_name, fn_id) {
                    return false;
                }
            }
            PseudoExpr::Apply { function, args } => {
                if blocked_depth == 0
                    && matches!(function.as_ref(), PseudoExpr::Var { name, id, .. } if helper_ref_matches(name, *id, fn_name, fn_id))
                {
                    if args.len() != expected_arity {
                        return false;
                    }
                    for arg in args.iter().rev() {
                        pending.push(Task::Node(arg, blocked_depth));
                    }
                } else {
                    for arg in args.iter().rev() {
                        pending.push(Task::Node(arg, blocked_depth));
                    }
                    pending.push(Task::Node(function, blocked_depth));
                }
            }
            PseudoExpr::Lambda { params, body } => {
                let blocked_depth =
                    blocked_depth + usize::from(params.iter().any(|param| param == fn_name));
                pending.push(Task::Node(body, blocked_depth));
            }
            PseudoExpr::RecFn { name, params, body } => {
                let blocked_depth = blocked_depth
                    + usize::from(name == fn_name || params.iter().any(|param| param == fn_name));
                pending.push(Task::Node(body, blocked_depth));
            }
            PseudoExpr::Let {
                name, value, body, ..
            } => {
                pending.push(Task::Node(
                    body,
                    blocked_depth + usize::from(name == fn_name),
                ));
                pending.push(Task::Node(value, blocked_depth));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(Task::Node(else_branch, blocked_depth));
                pending.push(Task::Node(then_branch, blocked_depth));
                pending.push(Task::Node(condition, blocked_depth));
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                let base_depth = blocked_depth
                    + usize::from(subject_name.as_ref().is_some_and(|name| name == fn_name));
                for clause in clauses.iter().rev() {
                    pending.push(Task::CheckClause(clause, base_depth));
                }
                pending.push(Task::Node(subject, blocked_depth));
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(Task::Node(right, blocked_depth));
                pending.push(Task::Node(left, blocked_depth));
            }
            PseudoExpr::UnOp { operand, .. }
            | PseudoExpr::Delay(operand)
            | PseudoExpr::Force(operand) => pending.push(Task::Node(operand, blocked_depth)),
            PseudoExpr::Trace { message, value } => {
                pending.push(Task::Node(value, blocked_depth));
                pending.push(Task::Node(message, blocked_depth));
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(tail) = tail.as_ref() {
                    pending.push(Task::Node(tail, blocked_depth));
                }
                for element in elements.iter().rev() {
                    pending.push(Task::Node(element, blocked_depth));
                }
            }
            PseudoExpr::Tuple(items) => {
                for item in items.iter().rev() {
                    pending.push(Task::Node(item, blocked_depth));
                }
            }
            PseudoExpr::Pair(a, b) => {
                pending.push(Task::Node(b, blocked_depth));
                pending.push(Task::Node(a, blocked_depth));
            }
            PseudoExpr::Constr { fields, .. } => {
                for field in fields.iter().rev() {
                    pending.push(Task::Node(field, blocked_depth));
                }
            }
            PseudoExpr::FieldAccess { record, .. } => {
                pending.push(Task::Node(record, blocked_depth))
            }
            PseudoExpr::IndexAccess { collection, .. } => {
                pending.push(Task::Node(collection, blocked_depth))
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args.iter().rev() {
                    pending.push(Task::Node(arg, blocked_depth));
                }
            }
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
        }
    }
    true
}

pub(super) fn helper_body_binds_name(expr: &PseudoExpr, target: &str) -> bool {
    enum Task<'a> {
        Node(&'a PseudoExpr),
        CheckClause(&'a WhenClause),
    }

    let mut pending = vec![Task::Node(expr)];
    while let Some(task) = pending.pop() {
        let cur = match task {
            Task::Node(cur) => cur,
            Task::CheckClause(clause) => {
                if pattern_binds_var(&clause.pattern, target) {
                    return true;
                }
                pending.push(Task::Node(&clause.body));
                if let Some(guard) = clause.guard.as_ref() {
                    pending.push(Task::Node(guard));
                }
                continue;
            }
        };
        match cur {
            PseudoExpr::Lambda { params, body } => {
                if params.iter().any(|param| param == target) {
                    return true;
                }
                pending.push(Task::Node(body));
            }
            PseudoExpr::RecFn { name, params, body } => {
                if name == target || params.iter().any(|param| param == target) {
                    return true;
                }
                pending.push(Task::Node(body));
            }
            PseudoExpr::Let {
                name, value, body, ..
            } => {
                if name == target {
                    return true;
                }
                pending.push(Task::Node(body));
                pending.push(Task::Node(value));
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                if subject_name.as_ref().is_some_and(|name| name == target) {
                    return true;
                }
                for clause in clauses.iter().rev() {
                    pending.push(Task::CheckClause(clause));
                }
                pending.push(Task::Node(subject));
            }
            PseudoExpr::Apply { function, args } => {
                for arg in args.iter().rev() {
                    pending.push(Task::Node(arg));
                }
                pending.push(Task::Node(function));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(Task::Node(else_branch));
                pending.push(Task::Node(then_branch));
                pending.push(Task::Node(condition));
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(Task::Node(right));
                pending.push(Task::Node(left));
            }
            PseudoExpr::UnOp { operand, .. }
            | PseudoExpr::Delay(operand)
            | PseudoExpr::Force(operand) => pending.push(Task::Node(operand)),
            PseudoExpr::Trace { message, value } => {
                pending.push(Task::Node(value));
                pending.push(Task::Node(message));
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(tail) = tail.as_ref() {
                    pending.push(Task::Node(tail));
                }
                for element in elements.iter().rev() {
                    pending.push(Task::Node(element));
                }
            }
            PseudoExpr::Tuple(items) => {
                for item in items.iter().rev() {
                    pending.push(Task::Node(item));
                }
            }
            PseudoExpr::Pair(a, b) => {
                pending.push(Task::Node(b));
                pending.push(Task::Node(a));
            }
            PseudoExpr::Constr { fields, .. } => {
                for field in fields.iter().rev() {
                    pending.push(Task::Node(field));
                }
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(Task::Node(record)),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(Task::Node(collection)),
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args.iter().rev() {
                    pending.push(Task::Node(arg));
                }
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
        }
    }
    false
}
