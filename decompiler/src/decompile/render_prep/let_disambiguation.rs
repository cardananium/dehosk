use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::{ExprFolder, ExprVisitor};
use crate::pseudo::var_id::VarId;

use super::{rename_compat_var_in_expr, rename_var_use_by_id_in_expr};

#[cfg(test)]
pub(crate) fn debug_disambiguate_shadowed_lets(expr: &PseudoExpr) -> PseudoExpr {
    disambiguate_shadowed_lets(expr)
}

#[cfg(test)]
pub(crate) fn debug_expr_contains_var_name(expr: &PseudoExpr, target: &str) -> bool {
    expr_contains_var_name(expr, target)
}

pub(super) fn disambiguate_shadowed_lets(expr: &PseudoExpr) -> PseudoExpr {
    let mut name_counts: HashMap<String, usize> = HashMap::new();
    let mut in_scope: HashSet<String> = HashSet::new();
    let fn_names = collect_function_names(expr);
    disambiguate_rec(expr.clone(), &mut name_counts, &mut in_scope, &fn_names)
}

struct PatternScopeFolder {
    /// Binder names currently in scope (lambda/recfn/let/pattern/
    /// subject), innermost last. A name may appear more than once when
    /// genuinely shadowed; `contains` only needs membership.
    scope: Vec<String>,
    /// Per-base-name suffix counter, using the let disambiguator's
    /// `_<N>` scheme for visual consistency.
    counts: HashMap<String, usize>,
}

impl PatternScopeFolder {
    fn in_scope(&self, name: &str) -> bool {
        self.scope.iter().any(|n| n == name)
    }

    /// Allocate a fresh `name_<N>` not currently in scope.
    fn fresh(&mut self, base: &str) -> String {
        let mut count = *self.counts.get(base).unwrap_or(&1);
        loop {
            count += 1;
            let candidate = make_unique_name(base, count);
            if !self.in_scope(&candidate) {
                self.counts.insert(base.to_string(), count);
                return candidate;
            }
        }
    }
}

impl ExprFolder for PatternScopeFolder {
    fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
        self.scope.extend(params.iter().map(|p| p.to_string()));
        params.to_vec()
    }

    fn exit_lambda(&mut self, params: &[Binder]) {
        let kept = self.scope.len() - params.len();
        self.scope.truncate(kept);
    }

    fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
        self.scope.push(name.to_string());
        self.scope.extend(params.iter().map(|p| p.to_string()));
        (name.clone(), params.to_vec())
    }

    fn exit_recfn(&mut self, _name: &Binder, params: &[Binder]) {
        let kept = self.scope.len() - params.len() - 1;
        self.scope.truncate(kept);
    }

    // The value is evaluated in the enclosing scope; the binder is visible
    // only in the body — `enter_let` runs after the value is folded and
    // before the body is, so pushing here (rather than in `pre_expr`) lands
    // exactly there.
    fn enter_let(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) -> String {
        self.scope.push(name.to_string());
        name.to_string()
    }

    fn exit_let(&mut self, _name: &str) {
        self.scope.pop();
    }

    fn fold_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        let subject = self.fold(subject);
        let subject_base = self.scope.len();
        if let Some(binder) = &subject_name {
            self.scope.push(binder.to_string());
        }
        let clauses = clauses
            .into_iter()
            .map(|clause| {
                let clause_base = self.scope.len();
                let mut renames: HashMap<VarId, String> = HashMap::new();
                for binder in pattern_binder_list(&clause.pattern) {
                    let name = binder.to_string();
                    if name == "_" {
                        continue; // wildcards never collide
                    }
                    if self.in_scope(&name) {
                        let fresh = self.fresh(&name);
                        renames.insert(binder.var_id(), fresh.clone());
                        self.scope.push(fresh);
                    } else {
                        self.scope.push(name);
                    }
                }
                let pattern =
                    super::rename_hygiene::rename_pattern_binders(clause.pattern, &renames);
                let guard = clause.guard.map(|g| self.fold(rewire_uses(g, &renames)));
                let body = self.fold(rewire_uses(clause.body, &renames));
                self.scope.truncate(clause_base);
                WhenClause {
                    pattern,
                    guard,
                    body,
                }
            })
            .collect();
        self.scope.truncate(subject_base);
        self.post_when(subject, subject_name, clauses)
    }
}

/// Suffix `when`/`expect` pattern binders that shadow an enclosing
/// binder of the same name, rewiring their uses by `VarId`.
///
/// `disambiguate_shadowed_lets` renames only `let`/`Lambda`/`RecFn`
/// binders, and `display/rewrite` relabels per-clause Pair/list
/// binders to the literal `head`/`tail` — so two nested cons clauses
/// both bind `tail`, and a parallel two-list traversal renders as
/// `rec_fn(tail, tail)` — both read as the inner binder though the
/// AST holds distinct `VarId`s.
pub(crate) fn disambiguate_shadowed_pattern_binders(expr: PseudoExpr) -> PseudoExpr {
    let mut folder = PatternScopeFolder {
        scope: Vec::new(),
        counts: HashMap::new(),
    };
    folder.fold(expr)
}

fn pattern_binder_list(pattern: &WhenPattern) -> Vec<Binder> {
    match pattern {
        WhenPattern::Constructor { fields, .. } => fields.clone(),
        WhenPattern::List { elements, tail } => {
            let mut v = elements.clone();
            v.extend(tail.clone());
            v
        }
        WhenPattern::Tuple(items) => items.clone(),
        WhenPattern::Pair(a, b) => vec![a.clone(), b.clone()],
        WhenPattern::Var(b) => vec![b.clone()],
        WhenPattern::Wildcard | WhenPattern::Literal(_) => Vec::new(),
    }
}

fn rewire_uses(expr: PseudoExpr, renames: &HashMap<VarId, String>) -> PseudoExpr {
    let mut current = expr;
    for (id, new_name) in renames {
        current = rename_var_use_by_id_in_expr(&current, *id, new_name);
    }
    current
}

pub(super) fn pattern_binds_name(pattern: &WhenPattern, target: &str) -> bool {
    match pattern {
        WhenPattern::Var(name) => name == target,
        WhenPattern::List { elements, tail } => {
            elements.iter().any(|name| name == target)
                || tail.as_ref().is_some_and(|name| name == target)
        }
        WhenPattern::Constructor { fields, .. } => fields.iter().any(|name| name == target),
        WhenPattern::Pair(a, b) => a == target || b == target,
        WhenPattern::Tuple(items) => items.iter().any(|name| name == target),
        WhenPattern::Literal(_) | WhenPattern::Wildcard => false,
    }
}

fn expr_contains_var_name(expr: &PseudoExpr, target: &str) -> bool {
    struct ContainsVarNameVisitor<'a> {
        target: &'a str,
        blocked_depth: usize,
        found: bool,
    }

    impl ExprVisitor for ContainsVarNameVisitor<'_> {
        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            if self.blocked_depth == 0 && name == self.target {
                self.found = true;
            }
        }

        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            if params.iter().any(|param| param == self.target) {
                self.blocked_depth += 1;
            }
        }

        fn visit_lambda_post(&mut self, params: &[Binder]) {
            if params.iter().any(|param| param == self.target) {
                self.blocked_depth -= 1;
            }
        }

        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            if name == self.target || params.iter().any(|param| param == self.target) {
                self.blocked_depth += 1;
            }
        }

        fn visit_recfn_post(&mut self, name: &Binder, params: &[Binder]) {
            if name == self.target || params.iter().any(|param| param == self.target) {
                self.blocked_depth -= 1;
            }
        }

        fn visit_let_value_post(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) {
            if name == self.target {
                self.blocked_depth += 1;
            }
        }

        fn visit_let_post(&mut self, name: &str) {
            if name == self.target {
                self.blocked_depth -= 1;
            }
        }

        fn visit_when_clause_pre(&mut self, subject_name: Option<&Binder>, clause: &WhenClause) {
            let subject_binds_target = subject_name.is_some_and(|name| name == self.target);
            let pattern_binds_target = pattern_binds_name(&clause.pattern, self.target);
            if subject_binds_target || pattern_binds_target {
                self.blocked_depth += 1;
            }
        }

        fn visit_when_clause_post(&mut self, subject_name: Option<&Binder>, clause: &WhenClause) {
            let subject_binds_target = subject_name.is_some_and(|name| name == self.target);
            let pattern_binds_target = pattern_binds_name(&clause.pattern, self.target);
            if subject_binds_target || pattern_binds_target {
                self.blocked_depth -= 1;
            }
        }
    }

    let mut visitor = ContainsVarNameVisitor {
        target,
        blocked_depth: 0,
        found: false,
    };
    visitor.walk(expr);
    visitor.found
}

fn expr_contains_var_id(expr: &PseudoExpr, target: VarId) -> bool {
    struct ContainsVarIdVisitor {
        target: VarId,
        found: bool,
    }

    impl ExprVisitor for ContainsVarIdVisitor {
        fn visit_var(&mut self, _name: &str, id: &Option<VarId>) {
            if *id == Some(self.target) {
                self.found = true;
            }
        }
    }

    let mut visitor = ContainsVarIdVisitor {
        target,
        found: false,
    };
    visitor.walk(expr);
    visitor.found
}

/// Names bound to a FUNCTION anywhere in `expr` — every `rec fn` name plus
/// every `let` whose value is a `Lambda`/`RecFn`. A parameter or pattern
/// binder sharing one of these names shadows a callable, so its uses read as
/// calls to the function. Collected program-wide because top-level
/// functions are visible regardless of definition order.
fn collect_function_names(expr: &PseudoExpr) -> HashSet<String> {
    struct FnNameCollector {
        names: HashSet<String>,
    }
    impl ExprVisitor for FnNameCollector {
        fn visit_recfn_pre(&mut self, name: &Binder, _params: &[Binder]) {
            self.names.insert(name.to_string());
        }
        fn visit_let_value_post(&mut self, name: &str, _id: &Option<VarId>, value: &PseudoExpr) {
            if matches!(value, PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. }) {
                self.names.insert(name.to_string());
            }
        }
    }
    let mut collector = FnNameCollector {
        names: HashSet::new(),
    };
    collector.walk(expr);
    collector.names
}

fn make_unique_name(base: &str, suffix: usize) -> String {
    if suffix <= 1 {
        base.to_string()
    } else {
        format!("{}_{}", base, suffix)
    }
}

fn is_intentional_inverted_rec_let(
    display_name: &str,
    value: &PseudoExpr,
    body: &PseudoExpr,
) -> bool {
    matches!(value, PseudoExpr::Apply { function, .. }
        if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == display_name))
        && matches!(body, PseudoExpr::RecFn { name, .. } if name == display_name)
}

/// Give every shadowed `let` / lambda param / rec-fn param a distinct
/// display name, so the rendered program never binds one name twice in
/// nested scopes.
///
/// `in_scope` is the set of names live at this point and `name_counts`
/// the suffix counter per base name; both are threaded mutably and each
/// binder REMOVES what it added on the way out, which is what makes the
/// scope a scope.
///
/// `name_counts` / `in_scope` are carried by the loop rather than as call arguments.
/// Choosing a `let`'s display name and rewriting its body once the VALUE is known,
/// then pushing the binder — and popping the binder back off `in_scope` after the
/// last child — are their own step variants.
fn disambiguate_rec(
    expr: PseudoExpr,
    name_counts: &mut HashMap<String, usize>,
    in_scope: &mut HashSet<String>,
    fn_names: &HashSet<String>,
) -> PseudoExpr {
    let mut steps: Vec<DisStep> = vec![DisStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            DisStep::Visit(expr) => match expr {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    // The value is disambiguated in the ENCLOSING scope; the
                    // binder only goes in afterwards, in `LetMid`.
                    steps.push(DisStep::LetMid { name, id, body });
                    steps.push(DisStep::Visit(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    let mut added = Vec::new();
                    let mut new_params = params.clone();
                    let mut renamed_body = body.into_inner();
                    for (i, p) in params.iter().enumerate() {
                        // A bare `_` param is a wildcard: it cannot be referenced,
                        // so it never collides — suffixing it would mint
                        // unreadable `__2`/`__3` names.
                        if p.as_str() == "_" {
                            added.push(p.to_string());
                            continue;
                        }
                        if in_scope.contains(p.as_str()) {
                            let count = name_counts.entry(p.to_string()).or_insert(1);
                            *count += 1;
                            let mut new_name = make_unique_name(p, *count);
                            while in_scope.contains(&new_name) {
                                *count += 1;
                                new_name = make_unique_name(p, *count);
                            }
                            renamed_body =
                                rename_var_use_by_id_in_expr(&renamed_body, p.id, &new_name);
                            for candidate in new_params.iter_mut().skip(i + 1) {
                                if *candidate == *p {
                                    *candidate = candidate.renamed(new_name.clone());
                                }
                            }
                            new_params[i] = new_params[i].renamed(new_name.clone());
                            in_scope.insert(new_name.clone());
                            added.push(new_name);
                        } else {
                            in_scope.insert(p.to_string());
                            added.push(p.to_string());
                        }
                    }
                    steps.push(DisStep::Post(DisPost::Lambda {
                        params: new_params,
                        added,
                    }));
                    steps.push(DisStep::Visit(renamed_body));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    let mut added = Vec::new();
                    if !in_scope.contains(name.as_str()) {
                        in_scope.insert(name.to_string());
                        added.push(name.to_string());
                    }
                    let mut new_params = params.clone();
                    let mut renamed_body = body.into_inner();
                    let mut seen_param_names = HashSet::from([name.to_string()]);
                    for (i, p) in params.iter().enumerate() {
                        // Rename a param that collides with a sibling param or a
                        // FUNCTION name anywhere in the program: the latter would
                        // read as a call to the function it shadows. Uses are
                        // rewired by VarId, so the outer function (a different
                        // VarId) is untouched. Gating on FUNCTION names, not all
                        // in-scope binders, leaves a param legitimately shadowing
                        // an outer VALUE (`fn find(list)`) alone.
                        if p.as_str() == "_" {
                            added.push(p.to_string());
                            continue;
                        }
                        if seen_param_names.contains(p.as_str()) || fn_names.contains(p.as_str()) {
                            let count = name_counts.entry(p.to_string()).or_insert(1);
                            *count += 1;
                            let mut new_p = make_unique_name(p.as_str(), *count);
                            while in_scope.contains(&new_p)
                                || seen_param_names.contains(&new_p)
                                || fn_names.contains(&new_p)
                            {
                                *count += 1;
                                new_p = make_unique_name(p.as_str(), *count);
                            }
                            renamed_body =
                                rename_var_use_by_id_in_expr(&renamed_body, p.id, &new_p);
                            for candidate in new_params.iter_mut().skip(i + 1) {
                                if *candidate == *p {
                                    *candidate = p.renamed(new_p.clone());
                                }
                            }
                            new_params[i] = p.renamed(new_p.clone());
                            seen_param_names.insert(new_p.clone());
                            if in_scope.insert(new_p.clone()) {
                                added.push(new_p);
                            }
                        } else {
                            seen_param_names.insert(p.to_string());
                            if in_scope.insert(p.to_string()) {
                                added.push(p.to_string());
                            }
                        }
                    }
                    steps.push(DisStep::Post(DisPost::RecFn {
                        name,
                        params: new_params,
                        added,
                    }));
                    steps.push(DisStep::Visit(renamed_body));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    // No scope change of its own: subject, then each clause's
                    // guard and body, all in the enclosing scope.
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    let mut clause_children = Vec::new();
                    for c in clauses {
                        clause_meta.push((c.pattern, c.guard.is_some()));
                        if let Some(g) = c.guard {
                            clause_children.push(g);
                        }
                        clause_children.push(c.body);
                    }
                    steps.push(DisStep::Post(DisPost::When {
                        subject_name,
                        clause_meta,
                    }));
                    // Reversed so they pop in source order.
                    for c in clause_children.into_iter().rev() {
                        steps.push(DisStep::Visit(c));
                    }
                    steps.push(DisStep::Visit(subject.into_inner()));
                }
                // No binder of its own: every child stays in this scope.
                other => match super::scope_recurse::plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(DisStep::Post(DisPost::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(DisStep::Visit(c));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            // Ran after the let VALUE and before the let BODY: everything
            // between `let new_value = disambiguate_rec(&value, ..)` and
            // `let new_body = disambiguate_rec(&body_to_process, ..)`.
            DisStep::LetMid { name, id, body } => {
                let new_value = done.last().expect("let value");
                let mut display_name = if in_scope.contains(&name) {
                    let count = name_counts.entry(name.clone()).or_insert(1);
                    *count += 1;
                    make_unique_name(&name, *count)
                } else {
                    name_counts.entry(name.clone()).or_insert(1);
                    name.clone()
                };
                // A binding whose VALUE already mentions the chosen display
                // name would read as self-reference; step the suffix until it
                // does not — except for the deliberate inverted-rec shape.
                while expr_contains_var_name(new_value, &display_name)
                    && !is_intentional_inverted_rec_let(&display_name, new_value, body.as_ref())
                {
                    let count = name_counts.entry(name.clone()).or_insert(1);
                    *count += 1;
                    display_name = make_unique_name(&name, *count);
                }
                let was_in_scope = in_scope.contains(&name);
                in_scope.insert(name.clone());
                let body_to_process = if display_name != name {
                    if let Some(real_id) = id.filter(|vid| expr_contains_var_id(&body, *vid)) {
                        rename_var_use_by_id_in_expr(&body, real_id, &display_name)
                    } else {
                        rename_compat_var_in_expr(&body, &name, &display_name)
                    }
                } else {
                    body.into_inner()
                };
                steps.push(DisStep::Post(DisPost::Let {
                    name,
                    display_name,
                    id,
                    was_in_scope,
                }));
                steps.push(DisStep::Visit(body_to_process));
            }
            DisStep::Post(post) => {
                let rebuilt = match post {
                    DisPost::Let {
                        name,
                        display_name,
                        id,
                        was_in_scope,
                    } => {
                        let new_body = done.pop().expect("let body");
                        let new_value = done.pop().expect("let value");
                        if !was_in_scope {
                            in_scope.remove(&name);
                        }
                        PseudoExpr::Let {
                            name: display_name,
                            id,
                            value: PBox::new(new_value),
                            body: PBox::new(new_body),
                        }
                    }
                    DisPost::Lambda { params, added } => {
                        let new_body = done.pop().expect("lambda body");
                        for p in &added {
                            in_scope.remove(p);
                        }
                        PseudoExpr::Lambda {
                            params,
                            body: PBox::new(new_body),
                        }
                    }
                    DisPost::RecFn {
                        name,
                        params,
                        added,
                    } => {
                        let new_body = done.pop().expect("recfn body");
                        for p in &added {
                            in_scope.remove(p);
                        }
                        PseudoExpr::RecFn {
                            name,
                            params,
                            body: PBox::new(new_body),
                        }
                    }
                    DisPost::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let total = 1 + clause_meta
                            .iter()
                            .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                            .sum::<usize>();
                        let mut parts = super::scope_recurse::take(&mut done, total).into_iter();
                        let subject = parts.next().expect("when subject");
                        let clauses = clause_meta
                            .into_iter()
                            .map(|(pattern, has_guard)| WhenClause {
                                pattern,
                                guard: has_guard.then(|| parts.next().expect("when guard")),
                                body: parts.next().expect("when clause body"),
                            })
                            .collect();
                        PseudoExpr::When {
                            subject: PBox::new(subject),
                            subject_name,
                            clauses,
                        }
                    }
                    DisPost::Plain(kind) => super::scope_recurse::rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "disambiguate_rec must leave one result");
    done.pop().expect("disambiguate_rec result")
}

/// A job on [`disambiguate_rec`]'s stack. `LetMid` sits between the two
/// children of a `let`; the `Post` variants unbind, then rebuild.
enum DisStep {
    Visit(PseudoExpr),
    LetMid {
        name: String,
        id: Option<VarId>,
        body: PBox,
    },
    Post(DisPost),
}

enum DisPost {
    Let {
        /// The ORIGINAL binder name — what `in_scope` holds and must drop.
        name: String,
        display_name: String,
        id: Option<VarId>,
        was_in_scope: bool,
    },
    Lambda {
        params: Vec<Binder>,
        added: Vec<String>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
        added: Vec<String>,
    },
    When {
        subject_name: Option<Binder>,
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(super::scope_recurse::PlainPost),
}
