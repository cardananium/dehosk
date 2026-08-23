use std::collections::{HashMap, HashSet};

use super::{BindingTarget, LiftedLet, var_is_referenced, var_is_referenced_id_aware};
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
use crate::pseudo::var_id::VarId;

pub(super) fn binding_references_any(binding: &LiftedLet, targets: &[BindingTarget]) -> bool {
    targets
        .iter()
        .any(|target| var_is_referenced_id_aware(&binding.value, target.id, target.name.as_str()))
}

pub(super) fn binding_references_any_names(binding: &LiftedLet, names: &[String]) -> bool {
    names
        .iter()
        .any(|name| var_is_referenced(&binding.value, name.as_str()))
}

#[derive(Default)]
struct HelperFreeVars {
    ids: HashSet<VarId>,
    compat_names: HashSet<String>,
}

fn helper_value_free_vars(expr: &PseudoExpr) -> HelperFreeVars {
    fn push_bound(
        bound_ids: &mut HashSet<VarId>,
        bound_names: &mut HashMap<String, usize>,
        name: &str,
        id: VarId,
    ) -> bool {
        *bound_names.entry(name.to_string()).or_default() += 1;
        bound_ids.insert(id)
    }

    fn pop_bound(
        bound_ids: &mut HashSet<VarId>,
        bound_names: &mut HashMap<String, usize>,
        name: &str,
        id: VarId,
        inserted_id: bool,
    ) {
        if let Some(count) = bound_names.get_mut(name) {
            if *count == 1 {
                bound_names.remove(name);
            } else {
                *count -= 1;
            }
        }
        if inserted_id {
            bound_ids.remove(&id);
        }
    }

    /// One pending step of `go`'s explicit stack.
    ///
    /// `EnterLetBody` carries the RAW `id`, not a resolved one: the
    /// original calls `VarId::fresh_compat_placeholder()` (a global
    /// counter) only after `value` is walked, so that allocation has to
    /// stay a step of its own rather than happen when the `Let` is entered.
    /// `PopOne`/`PopMany` carry exactly the binder(s) `push_bound` added
    /// (name, id, whether the id itself was newly inserted) so `pop_bound`
    /// unwinds precisely what was pushed, in reverse.
    enum Step<'a> {
        Visit(&'a PseudoExpr),
        EnterLetBody {
            name: &'a str,
            id: Option<VarId>,
            body: &'a PseudoExpr,
        },
        PopOne {
            name: String,
            id: VarId,
            inserted_id: bool,
        },
        EnterLambdaBody {
            params: &'a [Binder],
            body: &'a PseudoExpr,
        },
        EnterRecFnBody {
            name: &'a Binder,
            params: &'a [Binder],
            body: &'a PseudoExpr,
        },
        PopMany(Vec<(String, VarId, bool)>),
        EnterClause {
            subject_name: Option<&'a Binder>,
            clause: &'a crate::pseudo::ast::WhenClause,
        },
    }

    fn go(
        expr: &PseudoExpr,
        bound_ids: &mut HashSet<VarId>,
        bound_names: &mut HashMap<String, usize>,
        free: &mut HelperFreeVars,
    ) {
        let mut pending: Vec<Step<'_>> = vec![Step::Visit(expr)];
        while let Some(step) = pending.pop() {
            match step {
                Step::Visit(expr) => match expr {
                    PseudoExpr::Var { name, id, .. } => match id.get() {
                        Some(real_id) => {
                            if !bound_ids.contains(&real_id) {
                                free.ids.insert(real_id);
                            }
                        }
                        None => {
                            if bound_names.get(name).copied().unwrap_or(0) == 0 {
                                free.compat_names.insert(name.clone());
                            }
                        }
                    },
                    PseudoExpr::Lambda { params, body } => {
                        pending.push(Step::EnterLambdaBody { params, body });
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        pending.push(Step::EnterRecFnBody { name, params, body });
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                        ..
                    } => {
                        pending.push(Step::EnterLetBody {
                            name: name.as_str(),
                            id: *id,
                            body,
                        });
                        pending.push(Step::Visit(value));
                    }
                    PseudoExpr::Apply { function, args } => {
                        for arg in args.iter().rev() {
                            pending.push(Step::Visit(arg));
                        }
                        pending.push(Step::Visit(function));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        pending.push(Step::Visit(else_branch));
                        pending.push(Step::Visit(then_branch));
                        pending.push(Step::Visit(condition));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        for clause in clauses.iter().rev() {
                            pending.push(Step::EnterClause {
                                subject_name: subject_name.as_ref(),
                                clause,
                            });
                        }
                        pending.push(Step::Visit(subject));
                    }
                    PseudoExpr::List { elements, tail } => {
                        if let Some(tail) = tail {
                            pending.push(Step::Visit(tail));
                        }
                        for element in elements.iter().rev() {
                            pending.push(Step::Visit(element));
                        }
                    }
                    PseudoExpr::Tuple(items) => {
                        for item in items.iter().rev() {
                            pending.push(Step::Visit(item));
                        }
                    }
                    PseudoExpr::Pair(a, b) => {
                        pending.push(Step::Visit(b));
                        pending.push(Step::Visit(a));
                    }
                    PseudoExpr::Constr { fields, .. } => {
                        for field in fields.iter().rev() {
                            pending.push(Step::Visit(field));
                        }
                    }
                    PseudoExpr::FieldAccess { record, .. } => pending.push(Step::Visit(record)),
                    PseudoExpr::IndexAccess { collection, .. } => {
                        pending.push(Step::Visit(collection))
                    }
                    PseudoExpr::BinOp { left, right, .. } => {
                        pending.push(Step::Visit(right));
                        pending.push(Step::Visit(left));
                    }
                    PseudoExpr::UnOp { operand, .. }
                    | PseudoExpr::Delay(operand)
                    | PseudoExpr::Force(operand) => pending.push(Step::Visit(operand)),
                    PseudoExpr::Trace { message, value } => {
                        pending.push(Step::Visit(value));
                        pending.push(Step::Visit(message));
                    }
                    PseudoExpr::BuiltinCall { args, .. } => {
                        for arg in args.iter().rev() {
                            pending.push(Step::Visit(arg));
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
                },
                Step::EnterLetBody { name, id, body } => {
                    let concrete_id = id.unwrap_or_else(VarId::fresh_compat_placeholder);
                    let inserted_id = push_bound(bound_ids, bound_names, name, concrete_id);
                    pending.push(Step::PopOne {
                        name: name.to_string(),
                        id: concrete_id,
                        inserted_id,
                    });
                    pending.push(Step::Visit(body));
                }
                Step::PopOne {
                    name,
                    id,
                    inserted_id,
                } => {
                    pop_bound(bound_ids, bound_names, &name, id, inserted_id);
                }
                Step::EnterLambdaBody { params, body } => {
                    let inserted: Vec<(String, VarId, bool)> = params
                        .iter()
                        .map(|param| {
                            (
                                param.name.clone(),
                                param.id,
                                push_bound(bound_ids, bound_names, param.as_str(), param.id),
                            )
                        })
                        .collect();
                    pending.push(Step::PopMany(inserted));
                    pending.push(Step::Visit(body));
                }
                Step::EnterRecFnBody { name, params, body } => {
                    let mut inserted = vec![(
                        name.name.clone(),
                        name.id,
                        push_bound(bound_ids, bound_names, name.as_str(), name.id),
                    )];
                    inserted.extend(params.iter().map(|param| {
                        (
                            param.name.clone(),
                            param.id,
                            push_bound(bound_ids, bound_names, param.as_str(), param.id),
                        )
                    }));
                    pending.push(Step::PopMany(inserted));
                    pending.push(Step::Visit(body));
                }
                Step::PopMany(inserted) => {
                    for (name, id, inserted_id) in inserted.into_iter().rev() {
                        pop_bound(bound_ids, bound_names, &name, id, inserted_id);
                    }
                }
                Step::EnterClause {
                    subject_name,
                    clause,
                } => {
                    let mut inserted = Vec::new();
                    if let Some(subject_name) = subject_name {
                        inserted.push((
                            subject_name.name.clone(),
                            subject_name.id,
                            push_bound(
                                bound_ids,
                                bound_names,
                                subject_name.as_str(),
                                subject_name.id,
                            ),
                        ));
                    }
                    inserted.extend(pattern_bound_binders(&clause.pattern).into_iter().map(
                        |binder| {
                            let inserted_id =
                                push_bound(bound_ids, bound_names, binder.as_str(), binder.id);
                            (binder.name.clone(), binder.id, inserted_id)
                        },
                    ));
                    pending.push(Step::PopMany(inserted));
                    pending.push(Step::Visit(&clause.body));
                    if let Some(guard) = &clause.guard {
                        pending.push(Step::Visit(guard));
                    }
                }
            }
        }
    }

    let mut free = HelperFreeVars::default();
    go(expr, &mut HashSet::new(), &mut HashMap::new(), &mut free);
    free
}

pub(super) fn helper_value_is_closed(expr: &PseudoExpr) -> bool {
    let free = helper_value_free_vars(expr);
    free.ids.is_empty() && free.compat_names.is_empty()
}

pub(super) fn helper_value_free_vars_within(expr: &PseudoExpr, allowed: &[BindingTarget]) -> bool {
    let free = helper_value_free_vars(expr);
    let allowed_ids: HashSet<VarId> = allowed.iter().map(|allowed| allowed.id).collect();
    let allowed_names: HashSet<&str> = allowed
        .iter()
        .map(|allowed| allowed.name.as_str())
        .collect();
    free.ids.iter().all(|id| allowed_ids.contains(id))
        && free
            .compat_names
            .iter()
            .all(|name| allowed_names.contains(name.as_str()))
}

/// Per-binding dependency analysis result for a `let` chain: which
/// earlier chain entries and which outer-scope variables each binding
/// references. Read by rollback and co-location to place lifts safely.
#[derive(Debug, Clone)]
pub(crate) struct BindingDependencies {
    #[allow(dead_code)] // exercised only by tests
    pub(crate) target: BindingTarget,
    /// Indexes (into the input chain slice) of earlier entries this
    /// binding's value references, sorted ascending.
    pub(crate) captures_in_chain: Vec<usize>,
    /// Free VarIds of the value that are **not** bound by any earlier
    /// chain entry. Must be in scope at the binding's lift destination.
    pub(crate) external_free_ids: HashSet<VarId>,
    /// Free compat-placeholder names of the value that are **not** matched
    /// by any earlier chain entry's name. Same role as `external_free_ids`
    /// but for references that still carry a compat-placeholder id.
    pub(crate) external_free_compat_names: HashSet<String>,
}

#[allow(dead_code)] // exercised only by tests
impl BindingDependencies {
    /// True when the value has no free variables — safe to lift past the
    /// chain's enclosing scope with no repair.
    pub(crate) fn is_closed(&self) -> bool {
        self.captures_in_chain.is_empty()
            && self.external_free_ids.is_empty()
            && self.external_free_compat_names.is_empty()
    }

    /// True when every free variable of the value is bound by an earlier
    /// chain entry. Safe to lift within the chain (possibly co-located with
    /// its captors) but not past the enclosing scope without carrying those
    /// captors along.
    pub(crate) fn is_closed_over_chain(&self) -> bool {
        self.external_free_ids.is_empty() && self.external_free_compat_names.is_empty()
    }
}

/// Chain-wide dependency analysis output.
#[derive(Debug, Clone, Default)]
pub(crate) struct HelperDependencies {
    pub(crate) bindings: Vec<BindingDependencies>,
}

#[allow(dead_code)] // exercised only by tests
impl HelperDependencies {
    pub(crate) fn len(&self) -> usize {
        self.bindings.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }
}

/// Pure dependency analysis over a chain of leading `let` bindings.
///
/// The chain is assumed to be in source order and topologically sorted
/// (no forward references — only `rec fn` can self-reference, which
/// `helper_value_free_vars` handles internally).
///
/// Capture detection mirrors `helper_value_free_vars_within`: an earlier
/// entry `j` is treated as captured by entry `i` when the free-variable
/// set of `chain[i].value` contains either `chain[j].id` or
/// `chain[j].name` (through a compat-placeholder reference).
pub(crate) fn analyze_dependencies(chain: &[LiftedLet]) -> HelperDependencies {
    let mut bindings = Vec::with_capacity(chain.len());

    for (i, entry) in chain.iter().enumerate() {
        let free = helper_value_free_vars(&entry.value);
        let mut captures_in_chain = Vec::new();
        let mut external_free_ids = free.ids.clone();
        let mut external_free_compat_names = free.compat_names.clone();

        for (j, earlier) in chain[..i].iter().enumerate() {
            let earlier_id = earlier
                .id
                .get()
                .unwrap_or_else(VarId::fresh_compat_placeholder);
            let captures_by_id = free.ids.contains(&earlier_id);
            let captures_by_name = free.compat_names.contains(earlier.name.as_str());

            if captures_by_id || captures_by_name {
                captures_in_chain.push(j);
            }
            if captures_by_id {
                external_free_ids.remove(&earlier_id);
            }
            if captures_by_name {
                external_free_compat_names.remove(earlier.name.as_str());
            }
        }

        bindings.push(BindingDependencies {
            target: BindingTarget::from(entry),
            captures_in_chain,
            external_free_ids,
            external_free_compat_names,
        });
    }

    HelperDependencies { bindings }
}

/// Reverse hoist decisions whose lifted bindings would capture a variable
/// in `forbidden` (typically the enclosing lambda's params, or the recfn's
/// name plus params — binders that are NOT in scope at the lift
/// destination above that lambda/recfn).
///
/// Returns `(safe_lifted, rolled_back)`. Both lists preserve the original
/// chain order; `wrap_lifted_lets(rolled_back, body)` re-attaches the
/// rolled-back bindings to the inside of the surrounding scope.
///
/// Rollback is transitively closed: if binding *j* captures (in-chain) an
/// already-rolled-back earlier binding *i*, then *j* is rolled back too,
/// otherwise *j* would be left with a dangling reference to *i* (which is
/// now back inside the original scope rather than at the lift destination).
///
/// Defense in depth: `split_entry_lambda_helper_chain` only lifts bindings
/// whose free vars are all bound by earlier siblings, so under that
/// pre-condition the rollback set is empty. The check catches a bug in
/// `helper_value_free_vars` and keeps the guarantee explicit should the
/// pre-condition be relaxed.
pub(crate) fn rollback_unsafe_lifts(
    chain: Vec<LiftedLet>,
    forbidden: &[BindingTarget],
) -> (Vec<LiftedLet>, Vec<LiftedLet>) {
    if chain.is_empty() || forbidden.is_empty() {
        return (chain, Vec::new());
    }

    let deps = analyze_dependencies(&chain);
    let forbidden_ids: HashSet<VarId> = forbidden.iter().map(|t| t.id).collect();
    let forbidden_names: HashSet<&str> = forbidden.iter().map(|t| t.name.as_str()).collect();
    let forbidden_name_list: Vec<String> = forbidden.iter().map(|t| t.name.clone()).collect();

    let mut rolled_back = vec![false; chain.len()];

    for (i, dep) in deps.bindings.iter().enumerate() {
        let captures_id = dep
            .external_free_ids
            .iter()
            .any(|id| forbidden_ids.contains(id));
        let captures_name = dep
            .external_free_compat_names
            .iter()
            .any(|name| forbidden_names.contains(name.as_str()));
        // Defensive textual scan: a Var use can carry an authoritative VarId
        // that matches no current binder (a rename updated the binder id but
        // not the use), and `external_free_compat_names` tracks only
        // compat-placeholder refs, so such a use slips past both the id and
        // the compat-name check. `binding_references_any_names` handles
        // shadowing, so inner binders of the same name don't false-trip.
        let captures_by_textual_name =
            binding_references_any_names(&chain[i], &forbidden_name_list);
        if captures_id || captures_name || captures_by_textual_name {
            rolled_back[i] = true;
        }
    }

    loop {
        let mut changed = false;
        for (i, dep) in deps.bindings.iter().enumerate() {
            if rolled_back[i] {
                continue;
            }
            if dep.captures_in_chain.iter().any(|&j| rolled_back[j]) {
                rolled_back[i] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut safe = Vec::new();
    let mut rolled = Vec::new();
    for (i, binding) in chain.into_iter().enumerate() {
        if rolled_back[i] {
            rolled.push(binding);
        } else {
            safe.push(binding);
        }
    }

    (safe, rolled)
}

fn pattern_bound_binders(pattern: &WhenPattern) -> Vec<&Binder> {
    match pattern {
        WhenPattern::Constructor { fields, .. } => fields.iter().collect(),
        WhenPattern::List { elements, tail } => {
            let mut binders: Vec<&Binder> = elements.iter().collect();
            if let Some(tail) = tail {
                binders.push(tail);
            }
            binders
        }
        WhenPattern::Tuple(fields) => fields.iter().collect(),
        WhenPattern::Pair(a, b) => vec![a, b],
        WhenPattern::Var(v) => vec![v],
        WhenPattern::Wildcard | WhenPattern::Literal(_) => Vec::new(),
    }
}
