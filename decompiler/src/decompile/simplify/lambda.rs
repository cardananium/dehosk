//! Lambda and recursive function simplification methods for Simplifier.

use super::Simplifier;
use crate::decompile::list_traversal::list_tail_argument;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, Default)]
struct BindingRefIdState {
    found: Option<VarId>,
    ambiguous: bool,
}

impl Simplifier {
    fn push_pattern_bound_names(pattern: &WhenPattern, shadowed: &mut Vec<String>) {
        match pattern {
            WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                shadowed.extend(
                    fields
                        .iter()
                        .filter(|field| field.as_str() != "_")
                        .map(ToString::to_string),
                );
            }
            WhenPattern::List { elements, tail } => {
                shadowed.extend(
                    elements
                        .iter()
                        .filter(|element| element.as_str() != "_")
                        .map(ToString::to_string),
                );
                if let Some(tail) = tail
                    && tail != "_"
                {
                    shadowed.push(tail.to_string());
                }
            }
            WhenPattern::Pair(first, second) => {
                if first != "_" {
                    shadowed.push(first.to_string());
                }
                if second != "_" {
                    shadowed.push(second.to_string());
                }
            }
            WhenPattern::Var(name) => {
                if name != "_" {
                    shadowed.push(name.to_string());
                }
            }
            WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
        }
    }

    fn push_pattern_bound_name_refs<'a>(pattern: &'a WhenPattern, shadowed: &mut Vec<&'a str>) {
        match pattern {
            WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                shadowed.extend(
                    fields
                        .iter()
                        .map(Binder::as_str)
                        .filter(|field| *field != "_"),
                );
            }
            WhenPattern::List { elements, tail } => {
                shadowed.extend(
                    elements
                        .iter()
                        .map(Binder::as_str)
                        .filter(|element| *element != "_"),
                );
                if let Some(tail) = tail
                    && tail != "_"
                {
                    shadowed.push(tail.as_str());
                }
            }
            WhenPattern::Pair(first, second) => {
                if first != "_" {
                    shadowed.push(first.as_str());
                }
                if second != "_" {
                    shadowed.push(second.as_str());
                }
            }
            WhenPattern::Var(name) => {
                if name != "_" {
                    shadowed.push(name.as_str());
                }
            }
            WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
        }
    }

    fn infer_binding_ref_id<'a>(
        expr: &'a PseudoExpr,
        target: &str,
        shadowed: &mut Vec<&'a str>,
        found: &mut Option<VarId>,
        ambiguous: &mut bool,
    ) {
        /// One pending step of the worklist.
        enum Step<'a> {
            Visit(&'a PseudoExpr),
            EnterLetBody {
                name: &'a str,
                body: &'a PseudoExpr,
            },
            Truncate(usize),
            EnterWhenClause {
                subject_name: Option<&'a str>,
                clause: &'a WhenClause,
            },
        }

        let mut steps = vec![Step::Visit(expr)];
        while let Some(step) = steps.pop() {
            match step {
                // Ambiguity short-circuit: skip the rest of this subtree.
                Step::Visit(expr) => {
                    if *ambiguous {
                        continue;
                    }
                    match expr {
                        PseudoExpr::Var { name, id, .. } => {
                            if name == target
                                && !shadowed.iter().rev().any(|bound| *bound == target)
                                && let Some(candidate) = id.get()
                            {
                                match found {
                                    Some(existing) if *existing != candidate => {
                                        *ambiguous = true;
                                    }
                                    Some(_) => {}
                                    None => *found = Some(candidate),
                                }
                            }
                        }
                        PseudoExpr::Let {
                            name, value, body, ..
                        } => {
                            steps.push(Step::EnterLetBody {
                                name: name.as_str(),
                                body,
                            });
                            steps.push(Step::Visit(value));
                        }
                        PseudoExpr::Lambda { params, body } => {
                            let base = shadowed.len();
                            shadowed.extend(params.iter().map(Binder::as_str));
                            steps.push(Step::Truncate(base));
                            steps.push(Step::Visit(body));
                        }
                        PseudoExpr::RecFn { name, params, body } => {
                            let base = shadowed.len();
                            shadowed.push(name.as_str());
                            shadowed.extend(params.iter().map(Binder::as_str));
                            steps.push(Step::Truncate(base));
                            steps.push(Step::Visit(body));
                        }
                        PseudoExpr::Apply { function, args } => {
                            for arg in args.iter().rev() {
                                steps.push(Step::Visit(arg));
                            }
                            steps.push(Step::Visit(function));
                        }
                        PseudoExpr::If {
                            condition,
                            then_branch,
                            else_branch,
                        } => {
                            steps.push(Step::Visit(else_branch));
                            steps.push(Step::Visit(then_branch));
                            steps.push(Step::Visit(condition));
                        }
                        PseudoExpr::When {
                            subject,
                            subject_name,
                            clauses,
                        } => {
                            for clause in clauses.iter().rev() {
                                steps.push(Step::EnterWhenClause {
                                    subject_name: subject_name.as_ref().map(Binder::as_str),
                                    clause,
                                });
                            }
                            steps.push(Step::Visit(subject));
                        }
                        PseudoExpr::List { elements, tail } => {
                            if let Some(tail) = tail {
                                steps.push(Step::Visit(tail));
                            }
                            for element in elements.iter().rev() {
                                steps.push(Step::Visit(element));
                            }
                        }
                        PseudoExpr::Tuple(elements) => {
                            for element in elements.iter().rev() {
                                steps.push(Step::Visit(element));
                            }
                        }
                        PseudoExpr::Pair(first, second) => {
                            steps.push(Step::Visit(second));
                            steps.push(Step::Visit(first));
                        }
                        PseudoExpr::Constr { fields, .. }
                        | PseudoExpr::BuiltinCall { args: fields, .. } => {
                            for field in fields.iter().rev() {
                                steps.push(Step::Visit(field));
                            }
                        }
                        PseudoExpr::FieldAccess { record, .. } => {
                            steps.push(Step::Visit(record));
                        }
                        PseudoExpr::IndexAccess { collection, .. } => {
                            steps.push(Step::Visit(collection));
                        }
                        PseudoExpr::BinOp { left, right, .. } => {
                            steps.push(Step::Visit(right));
                            steps.push(Step::Visit(left));
                        }
                        PseudoExpr::UnOp { operand, .. } => {
                            steps.push(Step::Visit(operand));
                        }
                        PseudoExpr::Trace { message, value } => {
                            steps.push(Step::Visit(value));
                            steps.push(Step::Visit(message));
                        }
                        PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                            steps.push(Step::Visit(inner));
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
                Step::EnterLetBody { name, body } => {
                    let base = shadowed.len();
                    shadowed.push(name);
                    steps.push(Step::Truncate(base));
                    steps.push(Step::Visit(body));
                }
                Step::Truncate(base) => {
                    shadowed.truncate(base);
                }
                Step::EnterWhenClause {
                    subject_name,
                    clause,
                } => {
                    let base = shadowed.len();
                    if let Some(subject_name) = subject_name {
                        shadowed.push(subject_name);
                    }
                    Self::push_pattern_bound_name_refs(&clause.pattern, shadowed);
                    steps.push(Step::Truncate(base));
                    steps.push(Step::Visit(&clause.body));
                    if let Some(guard) = &clause.guard {
                        steps.push(Step::Visit(guard));
                    }
                }
            }
        }
    }

    pub(crate) fn existing_binding_ref_id(body: &PseudoExpr, name: &str) -> Option<VarId> {
        if name == "_" {
            return None;
        }
        let mut found = None;
        let mut ambiguous = false;
        Self::infer_binding_ref_id(body, name, &mut Vec::new(), &mut found, &mut ambiguous);
        if ambiguous { None } else { found }
    }

    fn infer_binding_ref_ids<'a>(
        expr: &'a PseudoExpr,
        targets: &HashMap<&str, Vec<usize>>,
        shadowed: &mut Vec<&'a str>,
        states: &mut [BindingRefIdState],
    ) {
        /// One pending step of the worklist — see `infer_binding_ref_id`
        /// for why the binding scopes are their own steps rather than
        /// code between two recursive calls.
        enum Step<'a> {
            Visit(&'a PseudoExpr),
            EnterLetBody {
                name: &'a str,
                body: &'a PseudoExpr,
            },
            Truncate(usize),
            EnterWhenClause {
                subject_name: Option<&'a str>,
                clause: &'a WhenClause,
            },
        }

        let mut steps = vec![Step::Visit(expr)];
        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(expr) => match expr {
                    PseudoExpr::Var { name, id, .. } => {
                        let Some(indices) = targets.get(name.as_str()) else {
                            continue;
                        };
                        if shadowed.iter().rev().any(|bound| *bound == name.as_str()) {
                            continue;
                        }
                        let Some(candidate) = id.get() else {
                            continue;
                        };
                        for &index in indices {
                            let state = &mut states[index];
                            match state.found {
                                Some(existing) if existing != candidate => state.ambiguous = true,
                                Some(_) => {}
                                None => state.found = Some(candidate),
                            }
                        }
                    }
                    PseudoExpr::Let {
                        name, value, body, ..
                    } => {
                        steps.push(Step::EnterLetBody {
                            name: name.as_str(),
                            body,
                        });
                        steps.push(Step::Visit(value));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        let base = shadowed.len();
                        shadowed.extend(params.iter().map(Binder::as_str));
                        steps.push(Step::Truncate(base));
                        steps.push(Step::Visit(body));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let base = shadowed.len();
                        shadowed.push(name.as_str());
                        shadowed.extend(params.iter().map(Binder::as_str));
                        steps.push(Step::Truncate(base));
                        steps.push(Step::Visit(body));
                    }
                    PseudoExpr::Apply { function, args } => {
                        for arg in args.iter().rev() {
                            steps.push(Step::Visit(arg));
                        }
                        steps.push(Step::Visit(function));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        steps.push(Step::Visit(else_branch));
                        steps.push(Step::Visit(then_branch));
                        steps.push(Step::Visit(condition));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        for clause in clauses.iter().rev() {
                            steps.push(Step::EnterWhenClause {
                                subject_name: subject_name.as_ref().map(Binder::as_str),
                                clause,
                            });
                        }
                        steps.push(Step::Visit(subject));
                    }
                    PseudoExpr::List { elements, tail } => {
                        if let Some(tail) = tail {
                            steps.push(Step::Visit(tail));
                        }
                        for element in elements.iter().rev() {
                            steps.push(Step::Visit(element));
                        }
                    }
                    PseudoExpr::Tuple(elements) => {
                        for element in elements.iter().rev() {
                            steps.push(Step::Visit(element));
                        }
                    }
                    PseudoExpr::Pair(first, second) => {
                        steps.push(Step::Visit(second));
                        steps.push(Step::Visit(first));
                    }
                    PseudoExpr::Constr { fields, .. }
                    | PseudoExpr::BuiltinCall { args: fields, .. } => {
                        for field in fields.iter().rev() {
                            steps.push(Step::Visit(field));
                        }
                    }
                    PseudoExpr::FieldAccess { record, .. } => {
                        steps.push(Step::Visit(record));
                    }
                    PseudoExpr::IndexAccess { collection, .. } => {
                        steps.push(Step::Visit(collection));
                    }
                    PseudoExpr::BinOp { left, right, .. } => {
                        steps.push(Step::Visit(right));
                        steps.push(Step::Visit(left));
                    }
                    PseudoExpr::UnOp { operand, .. } => {
                        steps.push(Step::Visit(operand));
                    }
                    PseudoExpr::Trace { message, value } => {
                        steps.push(Step::Visit(value));
                        steps.push(Step::Visit(message));
                    }
                    PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                        steps.push(Step::Visit(inner));
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
                },
                Step::EnterLetBody { name, body } => {
                    let base = shadowed.len();
                    shadowed.push(name);
                    steps.push(Step::Truncate(base));
                    steps.push(Step::Visit(body));
                }
                Step::Truncate(base) => {
                    shadowed.truncate(base);
                }
                Step::EnterWhenClause {
                    subject_name,
                    clause,
                } => {
                    let base = shadowed.len();
                    if let Some(subject_name) = subject_name {
                        shadowed.push(subject_name);
                    }
                    Self::push_pattern_bound_name_refs(&clause.pattern, shadowed);
                    steps.push(Step::Truncate(base));
                    steps.push(Step::Visit(&clause.body));
                    if let Some(guard) = &clause.guard {
                        steps.push(Step::Visit(guard));
                    }
                }
            }
        }
    }

    pub(crate) fn existing_binding_ref_ids(
        body: &PseudoExpr,
        params: &[Binder],
    ) -> Vec<Option<VarId>> {
        if params.is_empty() {
            return Vec::new();
        }
        if params.len() == 1 {
            let param = &params[0];
            return vec![if param == "_" {
                None
            } else {
                Self::existing_binding_ref_id(body, param.as_str())
            }];
        }

        let mut targets = HashMap::<&str, Vec<usize>>::new();
        for (index, param) in params.iter().enumerate() {
            if param != "_" {
                targets.entry(param.as_str()).or_default().push(index);
            }
        }
        if targets.is_empty() {
            return vec![None; params.len()];
        }

        let mut states = vec![BindingRefIdState::default(); params.len()];
        Self::infer_binding_ref_ids(body, &targets, &mut Vec::new(), &mut states);
        states
            .into_iter()
            .map(|state| if state.ambiguous { None } else { state.found })
            .collect()
    }

    fn stable_binding_id(&self, body: &PseudoExpr, binder: &Binder) -> Option<VarId> {
        if binder == "_" {
            return None;
        }
        Self::existing_binding_ref_id(body, binder.as_str()).or(Some(binder.id))
    }

    fn param_refers_to_binding(
        expr: &PseudoExpr,
        param_name: &str,
        param_id: Option<VarId>,
        name_to_id: &HashMap<String, VarId>,
    ) -> bool {
        match expr {
            PseudoExpr::Var { name, id, .. } => crate::decompile::var_match::refs_match(
                name,
                id.get().or_else(|| name_to_id.get(name).copied()),
                param_name,
                param_id,
            ),
            _ => false,
        }
    }

    pub(crate) fn annotate_binding_refs(
        expr: PseudoExpr,
        bindings: &HashMap<&str, VarId>,
        shadowed: &mut Vec<String>,
    ) -> PseudoExpr {
        use crate::pseudo::fold::ExprFolder;

        struct BindingRefAnnotator<'a> {
            bindings: &'a HashMap<&'a str, VarId>,
            shadowed: &'a mut Vec<String>,
        }

        impl ExprFolder for BindingRefAnnotator<'_> {
            fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
                let is_shadowed = self.shadowed.iter().rev().any(|bound| bound == &name);
                let id = if !is_shadowed {
                    self.bindings
                        .get(name.as_str())
                        .copied()
                        .map(Some)
                        .unwrap_or(id)
                } else {
                    id
                };
                PseudoExpr::Var { name, id }
            }

            fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
                self.shadowed.extend(params.iter().map(ToString::to_string));
                params.to_vec()
            }

            fn exit_lambda(&mut self, params: &[Binder]) {
                let base = self.shadowed.len() - params.len();
                self.shadowed.truncate(base);
            }

            fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
                self.shadowed.push(name.to_string());
                self.shadowed.extend(params.iter().map(ToString::to_string));
                (name.clone(), params.to_vec())
            }

            fn exit_recfn(&mut self, _name: &Binder, params: &[Binder]) {
                let base = self.shadowed.len() - params.len() - 1;
                self.shadowed.truncate(base);
            }

            fn enter_let(
                &mut self,
                name: &str,
                _id: &Option<VarId>,
                _value: &PseudoExpr,
            ) -> String {
                self.shadowed.push(name.to_string());
                name.to_string()
            }

            fn exit_let(&mut self, _name: &str) {
                self.shadowed.pop();
            }

            fn fold_when(
                &mut self,
                subject: PseudoExpr,
                subject_name: Option<Binder>,
                clauses: Vec<WhenClause>,
            ) -> PseudoExpr {
                let subject = self.fold(subject);
                let clauses = clauses
                    .into_iter()
                    .map(|clause| {
                        let base = self.shadowed.len();
                        if let Some(subject_name) = &subject_name {
                            self.shadowed.push(subject_name.to_string());
                        }
                        Simplifier::push_pattern_bound_names(&clause.pattern, self.shadowed);
                        let guard = clause.guard.map(|guard| self.fold(guard));
                        let body = self.fold(clause.body);
                        self.shadowed.truncate(base);
                        WhenClause {
                            pattern: clause.pattern,
                            guard,
                            body,
                        }
                    })
                    .collect();
                self.post_when(subject, subject_name, clauses)
            }
        }

        BindingRefAnnotator { bindings, shadowed }.fold(expr)
    }

    fn can_flatten_nested_params(outer_params: &[Binder], inner_params: &[Binder]) -> bool {
        if outer_params.len() + inner_params.len() > 50 {
            return false;
        }

        let mut seen = HashSet::new();
        for param in outer_params.iter().chain(inner_params.iter()) {
            if param == "_" {
                continue;
            }
            if !seen.insert(param.as_str()) {
                return false;
            }
        }

        true
    }

    /// Verify every direct self-recursive call in the post-flatten
    /// body has at least `min_args` immediate arguments. `rec_name`
    /// and `rec_id` together identify the self-binder — by `VarId`
    /// when present, else by display name, since pre-uniquify code
    /// can still emit nameless refs.
    ///
    /// A bare `Var(rec)` passed as a value, never applied, is
    /// allowed: flattening does not change partial-application
    /// semantics at the type-erased UPLC level.
    fn recursive_calls_have_arity(
        body: &PseudoExpr,
        rec_id: VarId,
        rec_name: &str,
        min_args: usize,
    ) -> bool {
        use crate::pseudo::fold::ExprVisitor;

        struct ArityChecker<'a> {
            rec_id: VarId,
            rec_name: &'a str,
            min_args: usize,
            ok: bool,
            blocked_depth: usize,
        }

        impl ArityChecker<'_> {
            fn matches_self(&self, callee: &PseudoExpr) -> bool {
                let mut cur = callee;
                while let PseudoExpr::Force(inner) = cur {
                    cur = inner.as_ref();
                }
                match cur {
                    PseudoExpr::Var { id: Some(v), .. } => *v == self.rec_id,
                    PseudoExpr::Var { id: None, name } => name.as_str() == self.rec_name,
                    _ => false,
                }
            }
        }

        impl ExprVisitor for ArityChecker<'_> {
            fn visit_apply(
                &mut self,
                _expr: &PseudoExpr,
                function: &PseudoExpr,
                args: &[PseudoExpr],
            ) {
                if self.blocked_depth == 0
                    && self.matches_self(function)
                    && args.len() < self.min_args
                {
                    self.ok = false;
                }
            }

            // Skip nested scopes that shadow the self-name: in a
            // `Let`, `Lambda`, or `RecFn` that rebinds it, any
            // `Apply(Var(rec), ...)` is a DIFFERENT rec helper,
            // not self-recursion.
            fn visit_let_pre(&mut self, name: &str) {
                if name == self.rec_name {
                    self.blocked_depth += 1;
                }
            }

            fn visit_let_post(&mut self, name: &str) {
                if name == self.rec_name {
                    self.blocked_depth -= 1;
                }
            }

            fn visit_lambda_pre(&mut self, params: &[Binder]) {
                if params.iter().any(|p| p.as_str() == self.rec_name) {
                    self.blocked_depth += 1;
                }
            }

            fn visit_lambda_post(&mut self, params: &[Binder]) {
                if params.iter().any(|p| p.as_str() == self.rec_name) {
                    self.blocked_depth -= 1;
                }
            }

            fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
                if name.as_str() == self.rec_name
                    || params.iter().any(|p| p.as_str() == self.rec_name)
                {
                    self.blocked_depth += 1;
                }
            }

            fn visit_recfn_post(&mut self, name: &Binder, params: &[Binder]) {
                if name.as_str() == self.rec_name
                    || params.iter().any(|p| p.as_str() == self.rec_name)
                {
                    self.blocked_depth -= 1;
                }
            }
        }

        let mut checker = ArityChecker {
            rec_id,
            rec_name,
            min_args,
            ok: true,
            blocked_depth: 0,
        };
        checker.walk(body);
        checker.ok
    }

    fn flatten_curried_lambda_chain(
        params: Vec<Binder>,
        body: PseudoExpr,
    ) -> (Vec<Binder>, PseudoExpr) {
        let mut merged_params = params;
        let mut current_body = body;

        loop {
            match current_body {
                PseudoExpr::Lambda { params, body }
                    if Self::can_flatten_nested_params(&merged_params, &params) =>
                {
                    merged_params.extend(params);
                    current_body = body.into_inner();
                }
                other => return (merged_params, other),
            }
        }
    }

    fn is_list_is_empty_of(expr: &PseudoExpr, var_name: &str) -> bool {
        match expr {
            PseudoExpr::BuiltinCall { name, args }
                if *name == crate::BuiltinId::ListIsEmpty && args.len() == 1 =>
            {
                matches!(&args[0], PseudoExpr::Var { name: vn, .. } if vn == var_name)
            }
            PseudoExpr::Apply { function, args } if args.len() == 1 => match function.as_ref() {
                PseudoExpr::Var { name, .. }
                    if *name == "List.is_empty" || *name == "null_list" =>
                {
                    matches!(&args[0], PseudoExpr::Var { name: vn, .. } if vn == var_name)
                }
                PseudoExpr::BuiltinCall {
                    name,
                    args: builtin_args,
                } if *name == crate::BuiltinId::ListIsEmpty && builtin_args.is_empty() => {
                    matches!(&args[0], PseudoExpr::Var { name: vn, .. } if vn == var_name)
                }
                _ => false,
            },
            _ => false,
        }
    }

    fn is_list_tail_call_of(expr: &PseudoExpr, var_name: &str, var_id: Option<VarId>) -> bool {
        match list_tail_argument(expr) {
            Some(PseudoExpr::Var { name, id, .. }) => {
                crate::decompile::var_match::refs_match(name, id.get(), var_name, var_id)
            }
            _ => false,
        }
    }

    fn rewrite_expect_nonempty_list_search_recfn(
        &mut self,
        rec_name: &str,
        rec_id: VarId,
        params: &[Binder],
        body: PseudoExpr,
    ) -> PseudoExpr {
        let Some(list_param) = params.first() else {
            return body;
        };

        let PseudoExpr::Apply { function, args } = &body else {
            return body;
        };
        if !matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "expect!")
            || args.len() != 2
        {
            return body;
        }

        let PseudoExpr::UnOp {
            op: UnaryOp::Not,
            operand,
        } = &args[0]
        else {
            return body;
        };
        if !Self::is_list_is_empty_of(operand, list_param.as_str()) {
            return body;
        }

        let PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } = &args[1]
        else {
            return body;
        };

        let recursive_tail_call = matches!(else_branch.as_ref(),
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == rec_name)
                    && args.len() == params.len()
                    && Self::is_list_tail_call_of(&args[0], list_param.as_str(), list_param.id.get())
                    && args.iter().skip(1).zip(params.iter().skip(1)).all(|(arg, param)| {
                        matches!(
                            arg,
                            PseudoExpr::Var { name, id, .. }
                                if name == param.as_str()
                                    && crate::decompile::var_match::ids_compatible(
                                        param.id.get(),
                                        id.get(),
                                    )
                        )
                    })
        );
        if !recursive_tail_call {
            return body;
        }

        let list_param_id = list_param.id.get();
        let uses_head = Self::contains_head_access_by_id(condition, list_param, list_param_id)
            || Self::contains_head_access_by_id(then_branch, list_param, list_param_id);
        if !uses_head {
            return body;
        }

        let head_binder = self.fresh_synthetic_binder(&format!("{}_h", list_param));
        let tail_binder = self.fresh_synthetic_binder(&format!("{}_t", list_param));

        let replace_list_parts = |expr: PseudoExpr| {
            let expr = Self::replace_head_access_by_id(
                expr,
                list_param.as_str(),
                list_param_id,
                head_binder.as_str(),
                head_binder.id,
            );
            Self::replace_tail_access_by_id(
                expr,
                list_param.as_str(),
                list_param_id,
                tail_binder.as_str(),
                tail_binder.id,
            )
        };

        let PseudoExpr::Apply { args, .. } = body else {
            unreachable!("validated nonempty-list search body should be an expect! apply");
        };
        let mut args = args.into_iter();
        let _expect_guard = args
            .next()
            .expect("validated nonempty-list search should keep an expect! guard");
        let PseudoExpr::If {
            condition,
            then_branch,
            ..
        } = args
            .next()
            .expect("validated nonempty-list search should keep an if body")
        else {
            unreachable!("validated nonempty-list search expect! payload should be an if");
        };

        let rewritten_condition = replace_list_parts(condition.into_inner());
        let rewritten_then = replace_list_parts(then_branch.into_inner());
        let rewritten_else = PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Var {
                name: rec_name.to_string(),
                id: Some(rec_id),
            }),
            args: std::iter::once(PseudoExpr::var_with_id(
                tail_binder.as_str(),
                tail_binder.id,
            ))
            .chain(
                params
                    .iter()
                    .skip(1)
                    .map(|param| PseudoExpr::var_with_id(param.as_str(), param.id)),
            )
            .collect(),
        };

        PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id(list_param.as_str(), list_param.id)),
            subject_name: Some(list_param.clone()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    PseudoExpr::error(),
                ),
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![head_binder],
                        tail: Some(tail_binder),
                    },
                    PseudoExpr::If {
                        condition: PBox::new(rewritten_condition),
                        then_branch: PBox::new(rewritten_then),
                        else_branch: PBox::new(rewritten_else),
                    },
                ),
            ],
        }
    }

    pub(super) fn simplify_lambda(&mut self, params: Vec<Binder>, body: PseudoExpr) -> PseudoExpr {
        let param_ids: Vec<Option<VarId>> = Self::existing_binding_ref_ids(&body, &params)
            .into_iter()
            .zip(params.iter())
            .map(|(existing, param)| existing.or((param != "_").then_some(param.id)))
            .collect();
        let lexical_shadows: Vec<_> = params
            .iter()
            .zip(param_ids.iter())
            .map(|(param, id)| {
                (
                    param.as_str(),
                    self.shadow_lexical_name(param.as_str(), *id),
                )
            })
            .collect();

        let mut simplified_body = self.simplify(body);
        let param_bindings: HashMap<&str, VarId> = params
            .iter()
            .zip(param_ids.iter().copied())
            .filter_map(|(param, id)| id.map(|vid| (param.as_str(), vid)))
            .collect();
        if !param_bindings.is_empty() {
            simplified_body =
                Self::annotate_binding_refs(simplified_body, &param_bindings, &mut Vec::new());
        }

        for (param, shadow) in lexical_shadows {
            self.restore_lexical_name(param, shadow);
        }

        // Y/fix definition that has already lost its outer `rec` wrapper:
        //   fn(acc) { rec fn self_fn(acc_2) { acc(self_fn, acc_2) } }
        //
        // It is deliberately left as written. Replacing the Lambda with a
        // bare `Var("fix")` orphans it whenever the surrounding context is
        // not a function call (e.g. a `when`-subject position), which the
        // downstream `flag_orphan_fix` pass then marks
        // `__fix_combinator_residue__`. The verbose Y-comb structure is the
        // faithful reading; `fix_combinator::simplify_z_combinator`
        // (Patterns 1/3/4) recognizes the shape where it is constrained.

        // Simplify fn(x) { force(x) } -> fn(x) { x }
        if let PseudoExpr::Force(inner) = &simplified_body
            && params.iter().zip(param_ids.iter()).any(|(param, id)| {
                Self::param_refers_to_binding(
                    inner.as_ref(),
                    param.as_str(),
                    *id,
                    &self.naming.name_to_id,
                )
            })
        {
            simplified_body = (**inner).clone();
        }

        // fn(x) { x } is deliberately not folded into an `identity` symbol —
        // the explicit lambda already shows it returns its argument unchanged.

        // Scott-encoded selectors are deliberately left as lambdas: fn(a, b) { b } could be
        // a Scott-encoded None, the selector for the 2nd variant of any 2+-variant enum, or
        // plain snd; fn(a, b) { a(v) } could be any constructor application. Without the
        // type there is nothing to choose between them, so the lambda stays.

        // Eta reduction: fn(x) { f(x) } → f when x is not free in f.
        if params.len() == 1
            && let PseudoExpr::Apply {
                function: ref f,
                args: ref call_args,
            } = simplified_body
            && call_args.len() == 1
            && Self::param_refers_to_binding(
                &call_args[0],
                params[0].as_str(),
                param_ids[0],
                &self.naming.name_to_id,
            )
            && !Self::is_var_used_by_id(f, params[0].as_str(), param_ids[0])
        {
            return (**f).clone();
        }

        let param_use_counts =
            Self::count_binding_uses_by_id(&simplified_body, &params, &param_ids);

        // Unused params become `_`, except the validator-entrypoint
        // names `rename_validator_params` sets (`script_context`,
        // `datum`, `redeemer`): the rendered signature keeps the role
        // marker even when the body never references them.
        let mut new_params: Vec<Binder> = params
            .iter()
            .zip(param_use_counts.iter())
            .map(|(p, use_count)| {
                if p == "_"
                    || *use_count > 0
                    || super::is_protected_validator_param_name(p.as_str())
                {
                    p.clone()
                } else {
                    p.renamed("_")
                }
            })
            .collect();

        // Flatten curried lambda chains into a single multi-arg lambda when
        // the merged signature would not introduce shadowing.
        (new_params, simplified_body) =
            Self::flatten_curried_lambda_chain(new_params, simplified_body);

        // Selector lambda CSE: if this lambda is a pure selector (fn(params) { param_i })
        // and an in-scope variable has the same selector signature, use that variable
        // instead — e.g. fn(_, err) { err } → y_409 when y_409 = fn(_, y) { y }.
        if let Some(sig) = Self::selector_signature(&new_params, &simplified_body)
            && let Some(selector) = self.selectors.selector_vars.get(&sig).cloned()
            && let Some(selector_var) = self.selector_binding_var(&selector)
        {
            return selector_var;
        }

        // Force-alias extraction: a parameter force()-d 3+ times in the body gets a
        // local `let param_forced = force(param)`, turning
        // `fn(d) { ... force(d).fst ... force(d).fst ... }` into
        // `fn(d) { let d_forced = force(d); ... d_forced.fst ... }` — N forces to 1.
        if !self.safe_mode {
            let force_use_counts = Self::count_force_of_bindings(&simplified_body, &new_params);
            for (param, force_uses) in new_params.iter().zip(force_use_counts) {
                if param == "_" {
                    continue;
                }
                if force_uses >= 3 {
                    let alias = format!("{}_forced", param.as_str());
                    let binder = self.fresh_synthetic_binder(&alias);
                    let new_body = Self::replace_force_of_var_with_id(
                        simplified_body,
                        param.as_str(),
                        param.id.get(),
                        &alias,
                        binder.id,
                    );
                    simplified_body = self.make_let_for_binder(
                        binder,
                        PseudoExpr::Force(PBox::new(self.make_var_for_binder(param))),
                        new_body,
                    );
                }
            }
        }

        PseudoExpr::Lambda {
            params: new_params,
            body: PBox::new(simplified_body),
        }
    }

    /// Simplify a recursive function expression, recursing into the body
    /// with tracking maps shadowed for the self-name and the parameters.
    pub(super) fn simplify_recfn(
        &mut self,
        name: Binder,
        params: Vec<Binder>,
        body: PseudoExpr,
    ) -> PseudoExpr {
        let rec_id = self.stable_binding_id(&body, &name);
        let initial_param_ids: Vec<Option<VarId>> =
            params.iter().map(|param| Some(param.id)).collect();
        let lexical_shadows: Vec<_> = std::iter::once((name.to_string(), rec_id))
            .chain(
                params
                    .iter()
                    .map(ToString::to_string)
                    .zip(initial_param_ids.iter().copied()),
            )
            .map(|(n, id)| {
                let shadow = self.shadow_lexical_name(&n, id);
                (n, shadow)
            })
            .collect();
        self.recursion
            .rec_vars
            .insert_binding(name.to_string(), rec_id);

        let rewrite_rec_id = rec_id.unwrap_or(name.id);
        let simplified = self.simplify(body);
        let mut simplified_body = self.rewrite_expect_nonempty_list_search_recfn(
            name.as_str(),
            rewrite_rec_id,
            &params,
            simplified,
        );

        let (flattened_param_binders, flattened_body) =
            Self::flatten_curried_lambda_chain(params.clone(), simplified_body.clone());
        let mut params = params;
        if flattened_param_binders.len() > params.len()
            && Self::recursive_calls_have_arity(
                &flattened_body,
                rewrite_rec_id,
                name.as_str(),
                flattened_param_binders.len(),
            )
        {
            // Clone to preserve each flattened Binder's original VarId:
            // `.map(Binder::synthetic)` would go through
            // `impl From<Binder> for String` and allocate a FRESH id,
            // desyncing from body refs that still use the original.
            params.extend(flattened_param_binders[params.len()..].iter().cloned());
            simplified_body = flattened_body;
        }
        let param_ids = Self::existing_binding_ref_ids(&simplified_body, &params);

        for (n, shadow) in lexical_shadows {
            self.restore_lexical_name(&n, shadow);
        }

        // Rename unused params to _ and reuse the same traversal to check
        // whether the recursive self-name is referenced at all.
        let mut usage_binders = params.clone();
        usage_binders.push(name.clone());
        let mut usage_ids = param_ids;
        usage_ids.push(rec_id);
        let mut usage_counts =
            Self::count_binding_uses_by_id(&simplified_body, &usage_binders, &usage_ids);
        let rec_use_count = usage_counts.pop().unwrap_or(0);
        let param_use_counts = usage_counts;

        let new_params: Vec<Binder> = params
            .iter()
            .zip(param_use_counts.iter())
            .map(|(p, use_count)| {
                if *use_count > 0 {
                    p.clone()
                } else {
                    p.renamed("_")
                }
            })
            .collect();

        let name = rec_id
            .map(|id| Binder::new(name.as_str(), id))
            .unwrap_or(name);

        if params.iter().all(|param| param.as_str() != "_") && rec_use_count == 0 {
            return PseudoExpr::Lambda {
                params: new_params,
                body: PBox::new(simplified_body),
            };
        }

        PseudoExpr::RecFn {
            name,
            params: new_params,
            body: PBox::new(simplified_body),
        }
    }
}
