use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::{OptionVarIdGet, VarId};
use crate::pseudo::walker::WalkVisitor;
#[cfg(test)]
use crate::pseudo::walker::{FoldAction, Walker};
use std::collections::HashSet;

pub(super) fn ref_matches_inline_target(
    name: &str,
    id: Option<VarId>,
    target_name: &str,
    target_id: Option<VarId>,
) -> bool {
    crate::decompile::var_match::refs_match(name, id.get(), target_name, target_id)
}

fn pattern_binds_name(pattern: &WhenPattern, name: &str) -> bool {
    match pattern {
        WhenPattern::Constructor { fields, .. } => fields.iter().any(|f| f == name),
        WhenPattern::List { elements, tail } => {
            elements.iter().any(|h| h == name) || tail.as_ref().is_some_and(|t| t == name)
        }
        WhenPattern::Tuple(fields) => fields.iter().any(|f| f == name),
        WhenPattern::Pair(a, b) => a == name || b == name,
        WhenPattern::Var(v) => v == name,
        WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
    }
}

fn pattern_has_binder(pattern: &WhenPattern) -> bool {
    match pattern {
        WhenPattern::Constructor { fields, .. } => !fields.is_empty(),
        WhenPattern::List { elements, tail } => !elements.is_empty() || tail.is_some(),
        WhenPattern::Tuple(fields) => !fields.is_empty(),
        WhenPattern::Pair(_, _) | WhenPattern::Var(_) => true,
        WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
    }
}

pub(super) fn expr_has_binder(expr: &PseudoExpr) -> bool {
    struct HasBinder {
        found: bool,
    }

    impl WalkVisitor for HasBinder {
        fn visit_let_pre(&mut self, _name: &str) {
            self.found = true;
        }

        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            if !params.is_empty() {
                self.found = true;
            }
        }

        fn visit_recfn_pre(&mut self, _name: &Binder, _params: &[Binder]) {
            self.found = true;
        }

        fn visit_when(
            &mut self,
            _subject: &PseudoExpr,
            subject_name: Option<&Binder>,
            _clauses: &[WhenClause],
        ) {
            if subject_name.is_some() {
                self.found = true;
            }
        }

        fn visit_when_clause_pre(&mut self, _subject_name: Option<&Binder>, clause: &WhenClause) {
            if pattern_has_binder(&clause.pattern) {
                self.found = true;
            }
        }
    }

    let mut visitor = HasBinder { found: false };
    visitor.walk(expr);
    visitor.found
}

/// Simple variable rename in an expression tree. Replaces all occurrences of
/// `old_name` with `new_name`, stopping at shadowing or capture-risk bindings.
#[cfg(test)]
pub(super) fn rename_var_simple(expr: PseudoExpr, old_name: &str, new_name: &str) -> PseudoExpr {
    use crate::pseudo::ast::{PBox, WhenClause as WC};

    struct RenameVarSimple<'a> {
        old_name: &'a str,
        new_name: &'a str,
        blocked_depth: usize,
    }

    impl Walker for RenameVarSimple<'_> {
        fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
            if self.blocked_depth > 0 {
                return FoldAction::Replace(expr.clone());
            }
            if let PseudoExpr::When {
                subject,
                subject_name: Some(subject_name),
                clauses,
            } = expr
            {
                if binder_blocks_rename(subject_name, self.old_name, self.new_name) {
                    let subject = self.fold((**subject).clone());
                    self.blocked_depth += 1;
                    let clauses = clauses
                        .iter()
                        .cloned()
                        .map(|clause| self.fold_clause(clause))
                        .collect();
                    self.blocked_depth -= 1;
                    return FoldAction::Replace(PseudoExpr::When {
                        subject: PBox::new(subject),
                        subject_name: Some(subject_name.clone()),
                        clauses,
                    });
                }
            }
            if let PseudoExpr::Var { name, .. } = expr {
                if name == self.old_name {
                    let PseudoExpr::Var { id, .. } = expr else {
                        unreachable!("matched above")
                    };
                    return FoldAction::Replace(PseudoExpr::Var {
                        name: self.new_name.to_string(),
                        id: *id,
                    });
                }
            }
            FoldAction::Walk
        }

        fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
            // pre_expr handles Var replacement; this is only reached for non-matching Vars.
            PseudoExpr::Var { name, id }
        }

        fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
            if params
                .iter()
                .any(|p| binder_blocks_rename(p, self.old_name, self.new_name))
            {
                self.blocked_depth += 1;
            }
            params.to_vec()
        }

        fn exit_lambda(&mut self, params: &[Binder]) {
            if params
                .iter()
                .any(|p| binder_blocks_rename(p, self.old_name, self.new_name))
            {
                self.blocked_depth -= 1;
            }
        }

        fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
            if binder_blocks_rename(name, self.old_name, self.new_name)
                || params
                    .iter()
                    .any(|p| binder_blocks_rename(p, self.old_name, self.new_name))
            {
                self.blocked_depth += 1;
            }
            (name.clone(), params.to_vec())
        }

        fn exit_recfn(&mut self, name: &Binder, params: &[Binder]) {
            if binder_blocks_rename(name, self.old_name, self.new_name)
                || params
                    .iter()
                    .any(|p| binder_blocks_rename(p, self.old_name, self.new_name))
            {
                self.blocked_depth -= 1;
            }
        }

        fn enter_let(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) -> String {
            if name_blocks_rename(name, self.old_name, self.new_name) {
                self.blocked_depth += 1;
            }
            name.to_string()
        }

        fn exit_let(&mut self, name: &str) {
            if name_blocks_rename(name, self.old_name, self.new_name) {
                self.blocked_depth -= 1;
            }
        }

        fn fold_clause(&mut self, clause: WC) -> WC {
            if pattern_binds_name(&clause.pattern, self.old_name)
                || pattern_binds_name(&clause.pattern, self.new_name)
            {
                return clause;
            }
            let body = self.fold(clause.body);
            let guard = clause.guard.map(|g| self.fold(g));
            let pattern = self.fold_pattern(clause.pattern);
            WC {
                pattern,
                guard,
                body,
            }
        }
    }

    RenameVarSimple {
        old_name,
        new_name,
        blocked_depth: 0,
    }
    .fold(expr)
}

#[cfg(test)]
fn binder_blocks_rename(binder: &Binder, old_name: &str, new_name: &str) -> bool {
    name_blocks_rename(binder.as_str(), old_name, new_name)
}

#[cfg(test)]
fn name_blocks_rename(name: &str, old_name: &str, new_name: &str) -> bool {
    name == old_name || name == new_name
}

/// Check if a binding name looks like a generic field extraction (e.g., `fields_0_2`, `head_partial_327_0`).
pub(super) fn is_generic_field_binding(name: &str) -> bool {
    if let Some(rest) = name
        .strip_prefix("fields_")
        .or_else(|| name.strip_prefix("field_"))
    {
        rest.chars().all(|c| c.is_ascii_digit() || c == '_')
    } else if let Some(rest) = name.strip_prefix("head_partial_") {
        rest.chars().all(|c| c.is_ascii_digit() || c == '_')
    } else {
        false
    }
}

/// Check if a FieldAccess field name is semantic (not structural like `.fields`, `.tag`).
pub(super) fn is_semantic_field_name(name: &str) -> bool {
    !matches!(name, "fields" | "tag" | "fst" | "snd")
}

/// Check if the expression contains any Var reference or Let/Lambda binding with the given name.
pub(super) fn has_any_var_named(expr: &PseudoExpr, target: &str) -> bool {
    struct HasAnyVarNamed<'a> {
        target: &'a str,
        found: bool,
    }

    impl WalkVisitor for HasAnyVarNamed<'_> {
        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            if name == self.target {
                self.found = true;
            }
        }

        fn visit_let_pre(&mut self, name: &str) {
            if name == self.target {
                self.found = true;
            }
        }

        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            if params.iter().any(|param| param == self.target) {
                self.found = true;
            }
        }

        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            if name == self.target || params.iter().any(|param| param == self.target) {
                self.found = true;
            }
        }

        fn visit_when(
            &mut self,
            _subject: &PseudoExpr,
            subject_name: Option<&Binder>,
            _clauses: &[WhenClause],
        ) {
            if subject_name.is_some_and(|name| name == self.target) {
                self.found = true;
            }
        }

        fn visit_when_clause_pre(&mut self, _subject_name: Option<&Binder>, clause: &WhenClause) {
            if pattern_binds_name(&clause.pattern, self.target) {
                self.found = true;
            }
        }
    }

    let mut visitor = HasAnyVarNamed {
        target,
        found: false,
    };
    visitor.walk(expr);
    visitor.found
}

pub(super) fn collect_let_names(expr: &PseudoExpr) -> HashSet<String> {
    struct CollectLetNames {
        names: HashSet<String>,
    }

    impl WalkVisitor for CollectLetNames {
        fn visit_let_pre(&mut self, name: &str) {
            self.names.insert(name.to_string());
        }
    }

    let mut visitor = CollectLetNames {
        names: HashSet::new(),
    };
    visitor.walk(expr);
    visitor.names
}

/// Collect all call sites for `fn_name` in a simplified expression tree.
/// Simplified AST uses multi-arg Apply, so no need to peel chains.
pub(super) fn collect_call_sites_simplified(
    expr: &PseudoExpr,
    fn_name: &str,
    fn_id: Option<VarId>,
    results: &mut Vec<Vec<PseudoExpr>>,
) {
    struct CollectCallSites<'a, 'b> {
        fn_name: &'a str,
        fn_id: Option<VarId>,
        results: &'b mut Vec<Vec<PseudoExpr>>,
    }

    impl WalkVisitor for CollectCallSites<'_, '_> {
        fn visit_apply(&mut self, _expr: &PseudoExpr, function: &PseudoExpr, args: &[PseudoExpr]) {
            if let PseudoExpr::Var { name, id, .. } = function
                && ref_matches_inline_target(name, *id, self.fn_name, self.fn_id)
            {
                self.results.push(args.to_vec());
            }
        }
    }

    CollectCallSites {
        fn_name,
        fn_id,
        results,
    }
    .walk(expr);
}
