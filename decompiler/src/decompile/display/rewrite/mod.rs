use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::super::helper::hoist::{
    pattern_binds_var, peel_leading_lets, var_is_referenced_id_aware, wrap_lifted_lets,
};
use super::super::late::display_structural::{
    try_inline_when_adapter_let, try_normalize_sorted_assoc_lookup_if,
    try_reorder_inverted_if_arg_lets, try_repair_self_referenced_let,
};
use super::super::late::list_alias::{
    extract_nullary_list_prepend_alias_value, rewrite_list_prepend_alias_uses,
};
use super::super::late::option_cps::try_rewrite_option_cps_apply;
use super::super::naming::{
    extract_comparison_binop, extract_data_int_binop, is_generic_name, is_temporary_helper_name,
};

/// Run cosmetic structural rewrites explicitly instead of
/// smuggling them through the pretty-printer.
pub(crate) fn normalize_display_rewrites(expr: PseudoExpr) -> PseudoExpr {
    normalize_display_rewrites_fixpoint(expr)
}

fn normalize_display_rewrites_fixpoint(expr: PseudoExpr) -> PseudoExpr {
    let mut expr = expr;
    for _ in 0..4 {
        let next = normalize_display_rewrites_round(expr.clone());
        if next.structural_eq(&expr) {
            break;
        }
        expr = next;
    }
    expr
}

fn normalize_display_rewrites_round(expr: PseudoExpr) -> PseudoExpr {
    rewrite_int_operator_helpers(deduplicate_identical_lets(rename_pair_entry_binders(
        LateDisplayRewriter.fold(expr),
    )))
}

fn rewrite_int_operator_helpers(expr: PseudoExpr) -> PseudoExpr {
    IntOperatorHelperRewriter::rewrite(expr)
}

fn deduplicate_identical_lets(expr: PseudoExpr) -> PseudoExpr {
    IdenticalLetDeduper::default().fold(expr)
}

fn rename_pair_entry_binders(expr: PseudoExpr) -> PseudoExpr {
    PairEntryBinderRenamer.fold(expr)
}

struct PairEntryBinderRenamer;

impl ExprFolder for PairEntryBinderRenamer {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn post_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name,
            clauses: clauses
                .into_iter()
                .map(rename_pair_entry_binder_clause)
                .collect(),
        }
    }
}

/// `clause`'s guard/body arrive already folded by the `ExprFolder` driver
/// (`fold_clause` recurses into both before `post_when` runs), so this only
/// does the pattern-driven renaming — no recursive descent of its own.
fn rename_pair_entry_binder_clause(clause: WhenClause) -> WhenClause {
    let mut guard = clause.guard;
    let mut body = clause.body;

    match clause.pattern {
        WhenPattern::List { mut elements, tail } if elements.len() == 1 => {
            let head = elements[0].clone();
            if let Some(legacy_head_alias) = generated_list_head_alias_name(head.as_str()) {
                guard = guard.map(|guard| {
                    rename_var_display_name(guard, &legacy_head_alias, head.id, head.as_str())
                });
                body = rename_var_display_name(body, &legacy_head_alias, head.id, head.as_str());
            }
            let uses_pair_fields =
                guard.as_ref().is_some_and(|guard| {
                    body_contains_pair_field_access_of_var(guard, head.as_str(), head.id)
                }) || body_contains_pair_field_access_of_var(&body, head.as_str(), head.id);

            if uses_pair_fields
                && is_generic_list_clause_binder_name(head.as_str())
                && head.as_str() != "entry"
            {
                elements[0] = head.renamed("entry".to_string());
                let mut guard = guard
                    .map(|guard| rename_var_display_name(guard, head.as_str(), head.id, "entry"));
                let mut body = rename_var_display_name(body, head.as_str(), head.id, "entry");
                let tail = match tail {
                    Some(tail_binder)
                        if is_generic_list_clause_binder_name(tail_binder.as_str())
                            && tail_binder.as_str() != "tail" =>
                    {
                        let tail_name = tail_binder.to_string();
                        guard = guard.map(|guard| {
                            rename_var_display_name(guard, &tail_name, tail_binder.id, "tail")
                        });
                        body = rename_var_display_name(body, &tail_name, tail_binder.id, "tail");
                        Some(tail_binder.renamed("tail".to_string()))
                    }
                    other => other,
                };
                return WhenClause {
                    pattern: WhenPattern::List { elements, tail },
                    guard,
                    body,
                };
            }

            if tail.as_ref().is_some_and(|tail_binder| {
                (head.as_str().ends_with("_h")
                    && tail_binder.as_str().ends_with("_t")
                    && is_generated_list_pattern_binder_name(head.as_str(), "_h")
                    && is_generated_list_pattern_binder_name(tail_binder.as_str(), "_t"))
                    || (is_generic_list_clause_binder_name(head.as_str())
                        && is_generic_list_clause_binder_name(tail_binder.as_str()))
            }) && head.as_str() != "head"
            {
                let tail_binder = tail.expect("guard above ensures tail exists");
                let head_name = head.to_string();
                let tail_name = tail_binder.to_string();
                let guard =
                    guard.map(|guard| rename_var_display_name(guard, &head_name, head.id, "head"));
                let guard = guard.map(|guard| {
                    rename_var_display_name(guard, &tail_name, tail_binder.id, "tail")
                });
                let body = rename_var_display_name(body, &head_name, head.id, "head");
                let body = rename_var_display_name(body, &tail_name, tail_binder.id, "tail");

                return WhenClause {
                    pattern: WhenPattern::List {
                        elements: vec![head.renamed("head".to_string())],
                        tail: Some(tail_binder.renamed("tail".to_string())),
                    },
                    guard,
                    body,
                };
            }

            WhenClause {
                pattern: WhenPattern::List { elements, tail },
                guard,
                body,
            }
        }
        pattern => WhenClause {
            pattern,
            guard,
            body,
        },
    }
}

fn generated_list_head_alias_name(name: &str) -> Option<String> {
    name.strip_suffix("_h").map(|stem| format!("{stem}_0"))
}

fn is_generic_list_clause_binder_name(name: &str) -> bool {
    if matches!(name, "entry" | "head" | "tail") {
        return false;
    }

    is_generic_name(name)
        || is_temporary_helper_name(name)
        || name.contains('_')
        || name.chars().any(|c| c.is_ascii_digit())
}

fn is_generated_list_pattern_binder_name(name: &str, suffix: &str) -> bool {
    let Some(stem) = name.strip_suffix(suffix) else {
        return false;
    };

    is_generic_name(stem) || is_temporary_helper_name(stem)
}

fn body_contains_pair_field_access_of_var(
    expr: &PseudoExpr,
    target_name: &str,
    target_id: VarId,
) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::FieldAccess {
                record, selector, ..
            } => {
                if (selector.is_pair_fst() || selector.is_pair_snd())
                    && matches!(record.as_ref(), PseudoExpr::Var { name, id, .. }
                    if if id.get().is_some() {
                        *id == Some(target_id)
                    } else {
                        name == target_name
                    })
                {
                    return true;
                }
                pending.push(record);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(value);
                pending.push(body);
            }
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(condition);
                pending.push(then_branch);
                pending.push(else_branch);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                pending.push(subject);
                for clause in clauses {
                    if let Some(guard) = clause.guard.as_ref() {
                        pending.push(guard);
                    }
                    pending.push(&clause.body);
                }
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            PseudoExpr::Pair(left, right) | PseudoExpr::BinOp { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            PseudoExpr::UnOp { operand, .. }
            | PseudoExpr::IndexAccess {
                collection: operand,
                ..
            }
            | PseudoExpr::Delay(operand)
            | PseudoExpr::Force(operand) => {
                pending.push(operand);
            }
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args),
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements);
                if let Some(tail) = tail.as_ref() {
                    pending.push(tail);
                }
            }
            PseudoExpr::Tuple(elements) => pending.extend(elements),
            PseudoExpr::Constr { fields, .. } => pending.extend(fields),
            PseudoExpr::Trace { message, value } => {
                pending.push(message);
                pending.push(value);
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

fn rename_var_display_name(
    expr: PseudoExpr,
    target_name: &str,
    target_id: VarId,
    new_name: &str,
) -> PseudoExpr {
    struct VarIdDisplayRenamer {
        target_name: String,
        target_id: VarId,
        new_name: String,
    }

    impl ExprFolder for VarIdDisplayRenamer {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
            // `retarget_refs_by_scope` runs upstream, so an
            // authoritative ref's id matches its lexical binder.
            // Compat-placeholder refs (`id.get()` is None) have no
            // stable identity, so only they match by name.
            let matches = if id.get().is_some() {
                id == Some(self.target_id)
            } else {
                name == self.target_name
            };
            PseudoExpr::Var {
                name: if matches { self.new_name.clone() } else { name },
                id,
            }
        }
    }

    VarIdDisplayRenamer {
        target_name: target_name.to_string(),
        target_id,
        new_name: new_name.to_string(),
    }
    .fold(expr)
}

struct LateDisplayRewriter;

#[derive(Debug, Clone)]
struct IntOperatorHelper {
    id: VarId,
    op: BinaryOp,
}

struct IntOperatorHelperRewriter {
    helper_scopes: Vec<HashMap<String, Option<IntOperatorHelper>>>,
    // `enter_let` decides whether the binding is a helper (from the folded
    // value); `post_let` needs that same decision to know whether the Let
    // can be dropped. The two hooks run in matched LIFO order per Let (same
    // as `helper_scopes`), so a stack carries it across the body descent.
    let_helper_ops: Vec<Option<BinaryOp>>,
}

#[derive(Debug, Clone)]
struct VisibleLetBinding {
    binder: Binder,
    value: PseudoExpr,
}

#[derive(Debug, Clone, Copy)]
struct LetDedupFrame {
    bindings_len: usize,
    aliases_len: usize,
    remove_current: bool,
}

#[derive(Default)]
struct IdenticalLetDeduper {
    visible_bindings: Vec<VisibleLetBinding>,
    aliases: Vec<(VarId, Binder)>,
    let_frames: Vec<LetDedupFrame>,
}

impl IdenticalLetDeduper {
    fn alias_target(&self, id: Option<VarId>) -> Option<&Binder> {
        let id = id?;
        self.aliases
            .iter()
            .rev()
            .find_map(|(from, target)| (*from == id).then_some(target))
    }

    fn find_visible_duplicate(&self, value: &PseudoExpr) -> Option<Binder> {
        self.visible_bindings
            .iter()
            .rev()
            .find(|binding| binding.value.structural_eq(value))
            .map(|binding| binding.binder.clone())
    }
}

impl ExprFolder for IdenticalLetDeduper {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
        if let Some(target) = self.alias_target(id) {
            return PseudoExpr::Var {
                name: target.name.clone(),
                id: Some(target.id),
            };
        }

        PseudoExpr::Var { name, id }
    }

    fn enter_let(&mut self, name: &str, id: &Option<VarId>, value: &PseudoExpr) -> String {
        let bindings_len = self.visible_bindings.len();
        let aliases_len = self.aliases.len();
        let mut remove_current = false;

        if is_deduplicable_let_value(value) {
            if let Some(existing) = self.find_visible_duplicate(value) {
                if let Some(id_val) = *id {
                    self.aliases.push((id_val, existing));
                    remove_current = true;
                }
            } else if let Some(id_val) = *id {
                self.visible_bindings.push(VisibleLetBinding {
                    binder: Binder::new(name, id_val),
                    value: value.clone(),
                });
            }
        }

        self.let_frames.push(LetDedupFrame {
            bindings_len,
            aliases_len,
            remove_current,
        });

        name.to_string()
    }

    fn exit_let(&mut self, _name: &str) {}

    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        let frame = self
            .let_frames
            .pop()
            .expect("let frame should exist for every folded let");
        self.visible_bindings.truncate(frame.bindings_len);
        self.aliases.truncate(frame.aliases_len);

        if frame.remove_current {
            body
        } else {
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }
    }
}

fn is_deduplicable_let_value(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Var { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements.iter());
                if let Some(tail) = tail.as_deref() {
                    pending.push(tail);
                }
            }
            PseudoExpr::Tuple(elements) => pending.extend(elements.iter()),
            PseudoExpr::Pair(first, second) => {
                pending.push(first);
                pending.push(second);
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            _ => return false,
        }
    }
    true
}

fn infer_int_operator_helper(value: &PseudoExpr) -> Option<BinaryOp> {
    let body = match value {
        PseudoExpr::Lambda { params, body } if params.len() == 2 => body.as_ref(),
        _ => return None,
    };

    if let Some(op) = extract_data_int_binop(body) {
        return match op {
            BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                Some(op)
            }
            _ => None,
        };
    }

    if let Some(op) = extract_comparison_binop(body) {
        return match op {
            BinaryOp::Lt | BinaryOp::Lte | BinaryOp::Gt | BinaryOp::Gte => Some(op),
            _ => None,
        };
    }

    let PseudoExpr::Let {
        value,
        body: let_body,
        ..
    } = body
    else {
        return None;
    };

    let op = extract_comparison_binop(value.as_ref())?;
    match let_body.as_ref() {
        PseudoExpr::UnOp {
            op: crate::pseudo::ast::UnaryOp::Not,
            ..
        } => match op {
            BinaryOp::Lt => Some(BinaryOp::Gte),
            BinaryOp::Lte => Some(BinaryOp::Gt),
            BinaryOp::Gt => Some(BinaryOp::Lte),
            BinaryOp::Gte => Some(BinaryOp::Lt),
            _ => None,
        },
        _ => None,
    }
}

impl IntOperatorHelperRewriter {
    fn rewrite(expr: PseudoExpr) -> PseudoExpr {
        Self {
            helper_scopes: vec![HashMap::new()],
            let_helper_ops: Vec::new(),
        }
        .fold(expr)
    }

    fn push_scope(&mut self) {
        self.helper_scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.helper_scopes.pop();
    }

    fn shadow_name(&mut self, name: &str) {
        self.helper_scopes
            .last_mut()
            .expect("helper scope")
            .insert(name.to_string(), None);
    }

    fn bind_helper(&mut self, name: String, id: Option<VarId>, op: BinaryOp) {
        // Compat Lets carry `id: None`; synthesize a placeholder so the
        // helper is still registered. Refs whose `id.get()` is `None` match
        // by name in `lookup_helper`, so the placeholder value never gates
        // inlining.
        let id = id.unwrap_or_else(VarId::fresh_compat_placeholder);
        self.helper_scopes
            .last_mut()
            .expect("helper scope")
            .insert(name, Some(IntOperatorHelper { id, op }));
    }

    fn lookup_helper(&self, name: &str, id: Option<VarId>) -> Option<BinaryOp> {
        for scope in self.helper_scopes.iter().rev() {
            if let Some(helper) = scope.get(name) {
                return helper.as_ref().and_then(|helper| {
                    // `OptionVarIdGet::get()` treats a `Some(compat)` ref
                    // id as "no specific binder"; otherwise compat-placeholder
                    // Apply callees never match their compat-placeholder Let
                    // helpers.
                    (id.get().is_none() || id.get() == Some(helper.id)).then_some(helper.op)
                });
            }
        }
        None
    }

    fn active_helper_names(&self) -> HashSet<String> {
        self.helper_scopes
            .iter()
            .flat_map(|scope| scope.keys().cloned())
            .collect()
    }
}

impl ExprFolder for IntOperatorHelperRewriter {
    fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
        self.push_scope();
        for param in params {
            self.shadow_name(param.name.as_str());
        }
        params.to_vec()
    }

    fn exit_lambda(&mut self, _params: &[Binder]) {
        self.pop_scope();
    }

    fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
        self.push_scope();
        self.shadow_name(name.name.as_str());
        for param in params {
            self.shadow_name(param.name.as_str());
        }
        (name.clone(), params.to_vec())
    }

    fn exit_recfn(&mut self, _name: &Binder, _params: &[Binder]) {
        self.pop_scope();
    }

    fn enter_let(&mut self, name: &str, id: &Option<VarId>, value: &PseudoExpr) -> String {
        let helper_op = infer_int_operator_helper(value);
        self.push_scope();
        self.shadow_name(name);
        if let Some(op) = helper_op {
            self.bind_helper(name.to_string(), *id, op);
        }
        self.let_helper_ops.push(helper_op);
        name.to_string()
    }

    fn exit_let(&mut self, _name: &str) {
        self.pop_scope();
    }

    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        let helper_op = self.let_helper_ops.pop().expect("let_helper_ops");
        if helper_op.is_some()
            && !var_is_referenced_id_aware(
                &body,
                id.unwrap_or_else(VarId::fresh_compat_placeholder),
                &name,
            )
        {
            body
        } else {
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }
    }

    fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
        match function {
            PseudoExpr::Var { name, id } => {
                if let [left, right] = args.as_slice()
                    && let Some(op) = self.lookup_helper(name.as_str(), id)
                {
                    return PseudoExpr::BinOp {
                        op,
                        left: PBox::new(left.clone()),
                        right: PBox::new(right.clone()),
                    };
                }
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::Var { name, id }),
                    args: args.into(),
                }
            }
            function => PseudoExpr::Apply {
                function: PBox::new(function),
                args: args.into(),
            },
        }
    }

    fn fold_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        let subject = self.fold(subject);
        self.push_scope();
        if let Some(subject_name) = &subject_name {
            self.shadow_name(subject_name.name.as_str());
        }
        let clauses = clauses
            .into_iter()
            .map(|clause| {
                self.push_scope();
                for helper_name in self.active_helper_names() {
                    if pattern_binds_var(&clause.pattern, &helper_name) {
                        self.shadow_name(&helper_name);
                    }
                }
                let guard = clause.guard.map(|guard| self.fold(guard));
                let body = self.fold(clause.body);
                self.pop_scope();
                WhenClause {
                    pattern: clause.pattern,
                    guard,
                    body,
                }
            })
            .collect();
        self.pop_scope();
        self.post_when(subject, subject_name, clauses)
    }
}

impl ExprFolder for LateDisplayRewriter {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
        let (mut lifted, function) = peel_leading_lets(function, |_, _| true);
        let mut args_out = Vec::with_capacity(args.len());
        for arg in args {
            let (arg_lifted, arg) = peel_leading_lets(arg, |_, _| true);
            lifted.extend(arg_lifted);
            args_out.push(arg);
        }

        if let Some(rewritten) =
            try_rewrite_option_cps_apply(function.clone(), args_out.clone(), false)
        {
            return wrap_lifted_lets(lifted, rewritten);
        }

        wrap_lifted_lets(
            lifted,
            PseudoExpr::Apply {
                function: PBox::new(function),
                args: args_out.into(),
            },
        )
    }

    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        if let Some(rewritten) =
            try_inline_when_adapter_let(name.clone(), value.clone(), body.clone())
        {
            return rewritten;
        }

        if let Some(rewritten) = try_reorder_inverted_if_arg_lets(
            name.clone(),
            id.unwrap_or_else(VarId::fresh_compat_placeholder),
            value.clone(),
            body.clone(),
        ) {
            return rewritten;
        }

        if let Some(rewritten) = try_repair_self_referenced_let(
            name.clone(),
            id.unwrap_or_else(VarId::fresh_compat_placeholder),
            value.clone(),
            body.clone(),
        ) {
            return rewritten;
        }

        if let Some(rewritten) =
            try_rewrite_list_prepend_alias_let(name.clone(), id, value.clone(), body.clone())
        {
            return rewritten;
        }

        PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }

    fn post_if(
        &mut self,
        condition: PseudoExpr,
        then_branch: PseudoExpr,
        else_branch: PseudoExpr,
    ) -> PseudoExpr {
        let (lifted, condition) = peel_leading_lets(condition, |_, _| true);
        let rewritten = try_normalize_sorted_assoc_lookup_if(
            condition.clone(),
            then_branch.clone(),
            else_branch.clone(),
        )
        .unwrap_or(PseudoExpr::If {
            condition: PBox::new(condition),
            then_branch: PBox::new(then_branch),
            else_branch: PBox::new(else_branch),
        });

        wrap_lifted_lets(lifted, rewritten)
    }

    fn post_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        let (lifted, subject) = peel_leading_lets(subject, |_, _| true);
        wrap_lifted_lets(
            lifted,
            PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses,
            },
        )
    }

    fn post_binop(&mut self, op: BinaryOp, left: PseudoExpr, right: PseudoExpr) -> PseudoExpr {
        let (mut lifted, left) = peel_leading_lets(left, |_, _| true);
        let (right_lifted, right) = peel_leading_lets(right, |_, _| true);
        lifted.extend(right_lifted);

        wrap_lifted_lets(
            lifted,
            PseudoExpr::BinOp {
                op,
                left: PBox::new(left),
                right: PBox::new(right),
            },
        )
    }
}

fn try_rewrite_list_prepend_alias_let(
    let_name: String,
    let_id: Option<VarId>,
    let_value: PseudoExpr,
    let_body: PseudoExpr,
) -> Option<PseudoExpr> {
    extract_nullary_list_prepend_alias_value(&let_value)?;

    let id_concrete = let_id?;
    let rewritten_body = rewrite_list_prepend_alias_uses(let_body, &let_name, id_concrete);

    if !var_is_referenced_id_aware(&rewritten_body, id_concrete, &let_name) {
        return Some(rewritten_body);
    }

    Some(PseudoExpr::Let {
        name: let_name,
        id: let_id,
        value: PBox::new(let_value),
        body: PBox::new(rewritten_body),
    })
}

#[cfg(test)]
mod tests;
