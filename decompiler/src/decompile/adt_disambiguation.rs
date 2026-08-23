use crate::pseudo::ast::PBox;
use std::rc::Rc;

use crate::decompile::{BlueprintHintRegistry, TypeHintId};
use crate::pseudo::ast::{Binder, PseudoExpr, PseudoType, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};

/// Build a `WhenPattern::Constructor` whose `shape` is pinned to `Known`
/// when `(name, tag, arity)` resolves to a closed-set constructor
/// (Bool/Option/Result/Ordering/List/Pair); otherwise the node relies on
/// the render-time [`BlueprintHintRegistry`], consulted via `type_hint`,
/// to supply the user-ADT name.
fn build_pattern_known_or_named(
    name: &str,
    tag: usize,
    fields: Vec<Binder>,
    type_hint: Option<TypeHintId>,
) -> WhenPattern {
    if let Some(kc) = KnownConstructor::from_str_and_tag(name, tag)
        && kc.expected_arity() == fields.len()
        && kc.pretty_name() == name
    {
        return WhenPattern::Constructor {
            type_hint,
            tag: kc.expected_tag(),
            fields,
            shape: ConstructorShape::Known(kc),
        };
    }
    let arity = fields.len();
    WhenPattern::constructor_with_hint(
        ConstructorShape::unknown_data(tag, arity),
        fields,
        type_hint,
    )
}

/// Build a `PseudoExpr::Constr` whose `shape` is pinned to `Known` when
/// `(name, tag, arity)` resolves to a closed-set constructor. Mirror of
/// [`build_pattern_known_or_named`] for expression construction.
fn build_constr_known_or_named(
    name: &str,
    tag: usize,
    fields: Vec<PseudoExpr>,
    type_hint: Option<TypeHintId>,
) -> PseudoExpr {
    if let Some(kc) = KnownConstructor::from_str_and_tag(name, tag)
        && kc.expected_arity() == fields.len()
        && kc.pretty_name() == name
    {
        return PseudoExpr::Constr {
            type_hint,
            tag: kc.expected_tag(),
            fields: fields.into(),
            shape: ConstructorShape::Known(kc),
        };
    }
    let arity = fields.len();
    PseudoExpr::constr_with_hint(
        ConstructorShape::unknown_data(tag, arity),
        fields,
        type_hint,
    )
}

// Constructor Disambiguation by Arity Patterns (Type Inference)
//
// Scans `when` expressions, collects the (tag, field_count) set across all
// branches, and matches it against known ADT signatures to name the
// constructors and the bare `Constr<N>` nodes in branch bodies.

/// Known ADT signature: sorted `(tag, field_count)` pairs → type name and
/// constructor names indexed by tag.
struct AdtSignature {
    /// Sorted (tag, field_count) pairs that uniquely identify the type.
    pattern: &'static [(usize, usize)],
    /// Human-readable type name (e.g. "Bool").
    type_name: &'static str,
    /// Constructor names indexed by tag. E.g. for Bool: index 0 = "False",
    /// index 1 = "True".
    ctor_names: &'static [&'static str],
    /// The PseudoType to assign to the subject variable.
    pseudo_type_fn: fn() -> Rc<PseudoType>,
}

fn adt_signatures() -> Vec<AdtSignature> {
    use crate::pseudo::ast::PseudoType;
    use std::rc::Rc;

    vec![
        // Bool: False = tag 0 (0 fields), True = tag 1 (0 fields)
        AdtSignature {
            pattern: &[(0, 0), (1, 0)],
            type_name: "Bool",
            ctor_names: &["False", "True"],
            pseudo_type_fn: || Rc::new(PseudoType::Bool),
        },
        // Option: Some = tag 0 (1 field), None = tag 1 (0 fields)
        AdtSignature {
            pattern: &[(0, 1), (1, 0)],
            type_name: "Option",
            ctor_names: &["Some", "None"],
            pseudo_type_fn: || Rc::new(PseudoType::Option(Rc::new(PseudoType::Unknown))),
        },
        // Option (reversed / PlutusTx): None = tag 0 (0 fields), Some = tag 1 (1 field)
        AdtSignature {
            pattern: &[(0, 0), (1, 1)],
            type_name: "Option",
            ctor_names: &["None", "Some"],
            pseudo_type_fn: || Rc::new(PseudoType::Option(Rc::new(PseudoType::Unknown))),
        },
        // Result: Ok = tag 0 (1 field), Error = tag 1 (1 field)
        AdtSignature {
            pattern: &[(0, 1), (1, 1)],
            type_name: "Result",
            ctor_names: &["Ok", "Error"],
            pseudo_type_fn: || {
                Rc::new(PseudoType::Result(
                    Rc::new(PseudoType::Unknown),
                    Rc::new(PseudoType::Unknown),
                ))
            },
        },
        // Ordering: Less = tag 0 (0), Equal = tag 1 (0), Greater = tag 2 (0)
        AdtSignature {
            pattern: &[(0, 0), (1, 0), (2, 0)],
            type_name: "Ordering",
            ctor_names: &["Less", "Equal", "Greater"],
            pseudo_type_fn: || Rc::new(PseudoType::Named("Ordering".to_string())),
        },
        // List: [] = tag 0 (empty), Cons = tag 1 (head, tail).
        // The other encoding (Cons at 0, [] at 1) is the next row.
        AdtSignature {
            pattern: &[(0, 0), (1, 2)],
            type_name: "List",
            ctor_names: &["Nil", "Cons"],
            pseudo_type_fn: || Rc::new(PseudoType::List(Rc::new(PseudoType::Unknown))),
        },
        // List (reversed): Cons = tag 0 (2 fields), Nil = tag 1 (0 fields)
        AdtSignature {
            pattern: &[(0, 2), (1, 0)],
            type_name: "List",
            ctor_names: &["Cons", "Nil"],
            pseudo_type_fn: || Rc::new(PseudoType::List(Rc::new(PseudoType::Unknown))),
        },
        // Pair (single-branch): Pair = tag 0 (2 fields)
        AdtSignature {
            pattern: &[(0, 2)],
            type_name: "Pair",
            ctor_names: &["Pair"],
            pseudo_type_fn: || {
                Rc::new(PseudoType::Pair(
                    Rc::new(PseudoType::Unknown),
                    Rc::new(PseudoType::Unknown),
                ))
            },
        },
    ]
}

/// Look up a sorted set of (tag, field_count) pairs in the signature table.
/// Returns `(type_name, ctor_names_by_tag, pseudo_type)` on match.
fn lookup_adt_signature(
    pairs: &[(usize, usize)],
    ordering_names: bool,
) -> Option<(&'static str, &'static [&'static str], Rc<PseudoType>)> {
    for sig in adt_signatures().iter() {
        // The Ordering signature ({(0,0),(1,0),(2,0)}) is opt-in
        // (`DecompileOptions::ordering_names`, default OFF): naming ANY
        // 3-nullary-variant shape `Less/Equal/Greater` paints comparison
        // semantics onto enums that are not comparisons at all (a
        // governance-parameter selector), and lies outright on scrambled
        // comparators.
        if sig.type_name == "Ordering" && !ordering_names {
            continue;
        }
        if sig.pattern == pairs {
            return Some((sig.type_name, sig.ctor_names, (sig.pseudo_type_fn)()));
        }
    }
    None
}

/// A body PROVABLY aborts when it is `Error` (rendered `fail`), possibly
/// behind `Trace`/`Force`/`Delay` wrappers, a reference to a fail-LABEL
/// binding (`let a = fail @"PT1"` — `fail_labels` carries those
/// `VarId`s), or an application whose head is one (applying an abort
/// aborts). Anything else is treated as LIVE — fail-closed.
///
/// `rename_constrs_positioned` renames an unnamed `Constr<tag>` only when
/// its field count matches the one expected for that tag, so a
/// `Constr<0>(x)` is never relabeled `False` (0 fields). A `type_hint`,
/// when given, is attached to every renamed node so the render-time
/// [`BlueprintHintRegistry`] can supply user-ADT names without the
/// inline `display_name`.
///
/// POSITION GATE: a bare Constr inside a data-literal container (a field
/// of another `Constr`, a `List` element/tail, a `Tuple`/`Pair`
/// component) is an element of an unrelated structure, not a branch
/// value of the enum this `when` proved; relabeling it splits one
/// constructor across two names, since CSE-hoisted siblings of the same
/// shape stay raw. Descending into a data container disables the relabel
/// for the subtree until a control-flow node (`when` arm, `if` branch,
/// `let` body, lambda body, call argument) resets the context.
fn is_aborting_body(
    e: &PseudoExpr,
    fail_labels: &std::collections::HashSet<crate::pseudo::var_id::VarId>,
) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![e];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Error { .. } => return true,
            PseudoExpr::Trace { value, .. } => pending.push(value),
            PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => pending.push(inner),
            // A let whose BODY aborts never yields a value, whatever the
            // value binding computes (`let v4 = <trace noise>; fail`).
            PseudoExpr::Let { body, .. } => pending.push(body),
            PseudoExpr::Var { id: Some(vid), .. } => {
                if fail_labels.contains(vid) {
                    return true;
                }
            }
            PseudoExpr::Apply { function, .. } => pending.push(function),
            _ => {}
        }
    }
    false
}

/// `VarId`s of `let`/`const` bindings whose value provably aborts —
/// the fail-label idiom (`let a = fail @"PT1"; … _ -> a(…)`).
fn collect_fail_label_ids(
    expr: &PseudoExpr,
) -> std::collections::HashSet<crate::pseudo::var_id::VarId> {
    fn walk(e: &PseudoExpr, out: &mut std::collections::HashSet<crate::pseudo::var_id::VarId>) {
        let mut pending: Vec<&PseudoExpr> = vec![e];
        while let Some(cur) = pending.pop() {
            if let PseudoExpr::Let {
                id: Some(vid),
                value,
                ..
            } = cur
            {
                if is_aborting_body(value, out) {
                    out.insert(*vid);
                }
            }
            pending.extend(
                crate::decompile::render_prep::scope_recurse::children(cur)
                    .into_iter()
                    .rev(),
            );
        }
    }
    let mut out = std::collections::HashSet::new();
    walk(expr, &mut out);
    out
}

fn rename_constrs_in_expr(
    expr: PseudoExpr,
    tag_to_info: &std::collections::HashMap<usize, (String, usize)>,
    type_hint: Option<TypeHintId>,
) -> PseudoExpr {
    rename_constrs_positioned(expr, tag_to_info, &type_hint, false)
}

enum RenameJob {
    /// Rewrite this node in the given position context.
    Visit(PseudoExpr, bool),
    /// A `Constr` whose rewritten fields sit on `done`. The node's own
    /// rename runs after those fields.
    Constr {
        node_hint: Option<TypeHintId>,
        tag: usize,
        shape: ConstructorShape,
        count: usize,
        in_data_literal: bool,
    },
    /// Any other node: its rewritten children sit on `done`; put them back
    /// into the shell they were taken out of.
    Rebuild { shell: PseudoExpr, count: usize },
}

/// Split a node into a SHELL — every immediate child replaced by a `Unit`
/// placeholder — plus those children in `map_children` order. The shell is
/// refilled by [`join_children`], which re-walks the same slots in the same
/// order, so the placeholders are never observed.
fn split_children(expr: PseudoExpr) -> (PseudoExpr, Vec<PseudoExpr>) {
    let mut kids: Vec<PseudoExpr> = Vec::new();
    let shell = crate::decompile::render_prep::scope_recurse::map_children(expr, |c| {
        kids.push(c);
        PseudoExpr::Unit
    });
    (shell, kids)
}

/// Put rewritten children back into a shell from [`split_children`].
fn join_children(shell: PseudoExpr, kids: Vec<PseudoExpr>) -> PseudoExpr {
    let mut kids = kids.into_iter();
    crate::decompile::render_prep::scope_recurse::map_children(shell, |_| {
        kids.next().expect("split_children left one child per slot")
    })
}

/// Takes the last `n` items off `done` — the children of the node being
/// reassembled, left there in source order by the walk.
fn take_done(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
    let at = done.len() - n;
    done.split_off(at)
}

fn rename_constrs_positioned(
    expr: PseudoExpr,
    tag_to_info: &std::collections::HashMap<usize, (String, usize)>,
    type_hint: &Option<TypeHintId>,
    in_data_literal: bool,
) -> PseudoExpr {
    let mut jobs: Vec<RenameJob> = vec![RenameJob::Visit(expr, in_data_literal)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(job) = jobs.pop() {
        match job {
            RenameJob::Visit(expr, in_data_literal) => match expr {
                PseudoExpr::Constr {
                    type_hint: node_hint,
                    tag,
                    fields,
                    shape,
                } => {
                    let fields = fields.into_vec();
                    jobs.push(RenameJob::Constr {
                        node_hint,
                        tag,
                        shape,
                        count: fields.len(),
                        in_data_literal,
                    });
                    // Constr fields are data-literal positions for the subtree.
                    // Reversed so they pop — and so land on `done` — in order.
                    for f in fields.into_iter().rev() {
                        jobs.push(RenameJob::Visit(f, true));
                    }
                }
                other @ (PseudoExpr::List { .. } | PseudoExpr::Tuple(_) | PseudoExpr::Pair(..)) => {
                    let (shell, kids) = split_children(other);
                    jobs.push(RenameJob::Rebuild {
                        shell,
                        count: kids.len(),
                    });
                    for k in kids.into_iter().rev() {
                        jobs.push(RenameJob::Visit(k, true));
                    }
                }
                // Every other node is a control-flow / expression position —
                // descend with the data-literal context RESET (a `when` inside
                // a list element legitimately re-enters branch-value
                // territory).
                other => {
                    let (shell, kids) = split_children(other);
                    jobs.push(RenameJob::Rebuild {
                        shell,
                        count: kids.len(),
                    });
                    for k in kids.into_iter().rev() {
                        jobs.push(RenameJob::Visit(k, false));
                    }
                }
            },
            RenameJob::Constr {
                node_hint,
                tag,
                shape,
                count,
                in_data_literal,
            } => {
                let fields = take_done(&mut done, count);
                if !in_data_literal
                    && !shape.is_known()
                    && let Some((ctor_name, expected_fields)) = tag_to_info.get(&tag)
                    && fields.len() == *expected_fields
                {
                    done.push(build_constr_known_or_named(
                        ctor_name,
                        tag,
                        fields,
                        type_hint.clone(),
                    ));
                    continue;
                }
                done.push(PseudoExpr::Constr {
                    type_hint: node_hint,
                    tag,
                    fields: fields.into(),
                    shape,
                });
            }
            RenameJob::Rebuild { shell, count } => {
                let kids = take_done(&mut done, count);
                done.push(join_children(shell, kids));
            }
        }
    }

    done.pop()
        .expect("rename_constrs_positioned leaves exactly one result")
}

/// Conservatively detect whether an expression still treats `var_id` as
/// a raw Data/constructor value by reading `.fields` from it. When it
/// does, the hardcoded arity fallback (`Constr<0/1>` -> Bool,
/// `Constr<0>(x)/Constr<1>` -> Option) is suppressed: `False`/`True` or
/// `Some`/`None` would be misleading there.
fn expr_accesses_fields_of_var(expr: &PseudoExpr, var_id: crate::pseudo::var_id::VarId) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::FieldAccess {
                record, selector, ..
            } => {
                if selector.as_pretty_name() == "fields"
                    && matches!(record.as_ref(), PseudoExpr::Var { id, .. } if *id == Some(var_id))
                {
                    return true;
                }
                pending.push(record);
            }
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
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
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for clause in clauses.iter().rev() {
                    pending.push(&clause.body);
                    if let Some(guard) = &clause.guard {
                        pending.push(guard);
                    }
                }
                pending.push(subject);
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            PseudoExpr::Apply { function, args } => {
                for arg in args.iter().rev() {
                    pending.push(arg);
                }
                pending.push(function);
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args.iter().rev() {
                    pending.push(arg);
                }
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail.as_deref() {
                    pending.push(t);
                }
                for element in elements.iter().rev() {
                    pending.push(element);
                }
            }
            PseudoExpr::Tuple(items) => {
                for item in items.iter().rev() {
                    pending.push(item);
                }
            }
            PseudoExpr::Pair(first, second) => {
                pending.push(second);
                pending.push(first);
            }
            PseudoExpr::Constr { fields, .. } => {
                for field in fields.iter().rev() {
                    pending.push(field);
                }
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            _ => {}
        }
    }
    false
}

/// Main constructor disambiguation pass.
///
/// Walks the AST bottom-up. For each `When` expression:
/// 1. Collect `(tag, field_count)` from Constructor patterns (skip Wildcard).
/// 2. Sort by tag and look up in the signature table.
/// 3. On match: name each Constructor pattern and rename bare Constr
///    nodes in branch bodies.
///
/// A blueprint-hint match also registers the user-ADT type name with
/// `registry` as a `TypeHintId` and attaches the hint to every rewritten
/// node, so render resolves constructor names through the registry
/// rather than the inline `display_name` field.
pub(crate) fn disambiguate_constructors(
    expr: PseudoExpr,
    blueprint_hints: Option<&crate::cardano::BlueprintHints>,
    registry: &mut BlueprintHintRegistry,
    ordering_names: bool,
) -> PseudoExpr {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::fold::ExprFolder;
    use std::collections::HashMap;

    struct Disambiguator<'a> {
        blueprint_hints: Option<&'a crate::cardano::BlueprintHints>,
        registry: &'a mut BlueprintHintRegistry,
        ordering_names: bool,
        /// Fail-label binding ids — wildcard arms referencing/applying
        /// these abort, keeping the closed-enum reading honest.
        fail_labels: &'a std::collections::HashSet<crate::pseudo::var_id::VarId>,
    }

    /// Try to match a set of (tag, field_count) pairs against blueprint type definitions.
    /// Returns `(type_name, tag_to_ctor_name_map)` if exactly one type matches.
    fn try_blueprint_lookup(
        hints: &crate::cardano::BlueprintHints,
        pairs: &[(usize, usize)],
    ) -> Option<(String, HashMap<usize, String>)> {
        let mut matched_type: Option<(String, HashMap<usize, String>)> = None;

        for (type_name, type_def) in &hints.types {
            // Check: do ALL branch (tag, field_count) pairs match this type's constructors?
            let all_match = pairs.iter().all(|&(tag, field_count)| {
                type_def
                    .constructors
                    .iter()
                    .any(|c| c.tag == tag && c.fields.len() == field_count)
            });

            if all_match {
                // Build tag → constructor_name map
                let mut tag_to_name = HashMap::new();
                for &(tag, _field_count) in pairs {
                    if let Some(ctor) = type_def.constructors.iter().find(|c| c.tag == tag) {
                        tag_to_name.insert(tag, ctor.name.clone());
                    }
                }

                if matched_type.is_some() {
                    // Ambiguous: more than one type matches. Don't use blueprint.
                    return None;
                }
                matched_type = Some((type_name.clone(), tag_to_name));
            }
        }

        matched_type
    }

    impl<'a> ExprFolder for Disambiguator<'a> {
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
            // 1. Collect (tag, field_count) from Constructor patterns
            let mut pairs: Vec<(usize, usize)> = Vec::new();
            let mut has_wildcard = false;
            let mut has_live_wildcard = false;
            for clause in &clauses {
                match &clause.pattern {
                    WhenPattern::Constructor { tag, fields, .. } => {
                        pairs.push((*tag, fields.len()));
                    }
                    WhenPattern::Wildcard => {
                        has_wildcard = true;
                        if !is_aborting_body(&clause.body, self.fail_labels) {
                            has_live_wildcard = true;
                        }
                    }
                    _ => {}
                }
            }

            // Skip if no constructor patterns found
            if pairs.is_empty() {
                return PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                };
            }

            // A single-branch expect (1 constructor + wildcard) is ambiguous
            // (Some, Ok, Pair), so the arity table is skipped — but only the
            // arity fallback: blueprint hints can still resolve it.
            //
            // A LIVE wildcard arm (body is not a structural fail) vetoes the
            // fallback too: the signatures are CLOSED enum shapes, so a
            // reachable third outcome proves the subject is not that enum.
            // An open integer-tag dispatch — `when v.3rd is { Constr<0> -> …;
            // Constr<1> -> …; _ -> a(…) }` — is otherwise painted False/True
            // by the Bool signature although tags beyond {0,1} reach the live
            // `_` arm. An exhaustive-or-fail wildcard (`_ -> fail`) keeps the
            // honest closed reading.
            let skip_arity_fallback = (pairs.len() == 1 && has_wildcard) || has_live_wildcard;
            let subject_fields_accessed_in_bodies =
                subject_name
                    .as_ref()
                    .map(|binder| binder.var_id())
                    .or(match &subject {
                        PseudoExpr::Var { id, .. } => *id,
                        _ => None,
                    })
                    .is_some_and(|subject_var_id| {
                        clauses.iter().any(|clause| {
                            clause.guard.as_ref().is_some_and(|guard| {
                                expr_accesses_fields_of_var(guard, subject_var_id)
                            }) || expr_accesses_fields_of_var(&clause.body, subject_var_id)
                        })
                    });

            // 2. Sort by tag
            pairs.sort_by_key(|&(tag, _)| tag);
            pairs.dedup();

            // 3a. Try blueprint hints FIRST (higher fidelity)
            if let Some(hints) = self.blueprint_hints
                && let Some((type_name, tag_to_name)) = try_blueprint_lookup(hints, &pairs)
            {
                let _tipo = Rc::new(PseudoType::Named(type_name.clone()));

                // Register the resolved user-ADT constructors with the
                // render-time registry `pretty.rs`/`ast::to_string`
                // consult instead of `display_name`.
                let type_hint = TypeHintId::new(type_name);
                for (&tag, ctor_name) in &tag_to_name {
                    self.registry
                        .register_user(type_hint.clone(), tag, ctor_name.clone());
                }

                // Build tag → (name, expected_field_count) map
                let mut tag_to_info: HashMap<usize, (String, usize)> = HashMap::new();
                for &(tag, field_count) in &pairs {
                    if let Some(ctor_name) = tag_to_name.get(&tag) {
                        tag_to_info.insert(tag, (ctor_name.clone(), field_count));
                    }
                }

                let clauses: Vec<WhenClause> = clauses
                    .into_iter()
                    .map(|clause| {
                        let pattern = match clause.pattern {
                            WhenPattern::Constructor {
                                tag,
                                fields,
                                type_hint: None,
                                ..
                            } => {
                                if let Some((ctor_name, _)) = tag_to_info.get(&tag) {
                                    build_pattern_known_or_named(
                                        ctor_name,
                                        tag,
                                        fields,
                                        Some(type_hint.clone()),
                                    )
                                } else {
                                    let arity = fields.len();
                                    WhenPattern::constructor(
                                        ConstructorShape::unknown_data(tag, arity),
                                        fields,
                                    )
                                }
                            }
                            other => other,
                        };

                        let body = rename_constrs_in_expr(
                            clause.body,
                            &tag_to_info,
                            Some(type_hint.clone()),
                        );

                        WhenClause {
                            pattern,
                            guard: clause.guard,
                            body,
                        }
                    })
                    .collect();

                let subject = match subject {
                    PseudoExpr::Var { name, id, .. } => PseudoExpr::Var { name, id },
                    other => other,
                };

                return PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                };
            }

            // 3b. Fall back to hardcoded arity-signature matching
            if skip_arity_fallback || subject_fields_accessed_in_bodies {
                return PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                };
            }

            let lookup = lookup_adt_signature(&pairs, self.ordering_names);

            if let Some((_type_name, ctor_names, _tipo)) = lookup {
                // Build tag → (name, expected_field_count) map
                let mut tag_to_info: HashMap<usize, (String, usize)> = HashMap::new();
                for &(tag, field_count) in &pairs {
                    if tag < ctor_names.len() {
                        tag_to_info.insert(tag, (ctor_names[tag].to_string(), field_count));
                    }
                }

                // 4. Name each Constructor pattern and rename matching Constrs
                //    in branch bodies
                let clauses: Vec<WhenClause> = clauses
                    .into_iter()
                    .map(|clause| {
                        let pattern = match clause.pattern {
                            WhenPattern::Constructor {
                                type_hint: None,
                                tag,
                                fields,
                                shape,
                                ..
                            } if !shape.is_known() => {
                                if let Some((ctor_name, _)) = tag_to_info.get(&tag) {
                                    build_pattern_known_or_named(ctor_name, tag, fields, None)
                                } else {
                                    let arity = fields.len();
                                    WhenPattern::constructor(
                                        ConstructorShape::unknown_data(tag, arity),
                                        fields,
                                    )
                                }
                            }
                            // Don't overwrite already-named patterns
                            other => other,
                        };

                        // Rename matching Constrs in the body
                        let body = rename_constrs_in_expr(clause.body, &tag_to_info, None);

                        WhenClause {
                            pattern,
                            guard: clause.guard,
                            body,
                        }
                    })
                    .collect();

                let subject = match subject {
                    PseudoExpr::Var { name, id, .. } => PseudoExpr::Var { name, id },
                    other => other,
                };

                PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                }
            } else {
                // No match — return unchanged
                PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                }
            }
        }
    }

    // No global pass renames every bare `Constr<0/1>` to True/False:
    // `Constr<0>` could be Ok, Some, Less or Nil. The later
    // `simplify_boolean_and_identity` pass does Bool detection with
    // context analysis.
    let fail_labels = collect_fail_label_ids(&expr);
    Disambiguator {
        blueprint_hints,
        registry,
        ordering_names,
        fail_labels: &fail_labels,
    }
    .fold(expr)
}
