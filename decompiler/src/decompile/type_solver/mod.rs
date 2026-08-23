//! Constraint-based type inference.
//!
//! Generates and solves unification constraints over the final
//! `PseudoExpr` AST to refine parameterised types such as `Option<?>`,
//! `Result<?, ?>`, `Pair<?, ?>`, and `List<?>`. The pipeline is:
//!
//! 1. Assign type variables and generate forward unification constraints
//!    in one pass.
//! 2. Solve those constraints with a union-find.
//! 3. Generate backward constraints (field types → container types) and
//!    run a second solve round.
//! 4. Harvest a declaration-keyed `FinalTypeTable` from the solver state.
//! 5. Seed Cardano-context and monomorphic builtin arg types, then
//!    enrich `Function` entries to a fixed point.

use std::rc::Rc;

use crate::builtins::BuiltinId;
use crate::decompile::final_type_table::FinalTypeTable;
use crate::pseudo::ast::{BinaryOp, PseudoExpr, PseudoType, UnaryOp, WhenPattern};
use crate::pseudo::constructor::KnownConstructor;
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

mod backward;
mod core;
mod enrich;
mod harvest;
mod seed_builtin_args;
mod seed_cardano;

use self::backward::generate_backward_constraints;
use self::core::{BindingKey, LexicalEnv, TypeExpr, TypeSolver, TypeVarId};
use self::enrich::enrich_function_types;
use self::harvest::harvest_final_type_table;
use self::seed_builtin_args::seed_builtin_arg_types;
use self::seed_cardano::seed_cardano_context_types;

fn child_path(path: &[u32], index: u32) -> Vec<u32> {
    let mut child = path.to_vec();
    child.push(index);
    child
}

fn let_binding_key(id: Option<VarId>) -> BindingKey {
    BindingKey::VarId(id.unwrap_or_else(VarId::fresh_compat_placeholder))
}

fn pattern_binders(pattern: &WhenPattern) -> Vec<crate::pseudo::ast::Binder> {
    let mut binders = Vec::new();
    match pattern {
        WhenPattern::Constructor { fields, .. } => binders.extend(fields.iter().cloned()),
        WhenPattern::List { elements, tail } => {
            binders.extend(elements.iter().cloned());
            if let Some(tail) = tail {
                binders.push(tail.clone());
            }
        }
        WhenPattern::Tuple(fields) => binders.extend(fields.iter().cloned()),
        WhenPattern::Pair(a, b) => binders.extend([a.clone(), b.clone()]),
        WhenPattern::Var(name) => binders.push(name.clone()),
        WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
    }
    binders
}

// Constraint generation: assign type variables + generate constraints in one pass

/// Infer a type variable for an arbitrary expression.
/// For Var/Let nodes returns their named var. For other expressions
/// returns a fresh var constrained to the expression's obvious type.
fn expr_type_var(
    expr: &PseudoExpr,
    solver: &mut TypeSolver,
    env: &LexicalEnv,
    path: &[u32],
) -> TypeVarId {
    // Constr::Some/Cons and List each wrap a single non-tail recursive
    // call whose result feeds only a fresh-var + constrain_eq (or is
    // discarded); the wrapper always returns its own pre-allocated `tv`.
    enum Frame {
        ConstrUnify { tv: TypeVarId },
        Discard { tv: TypeVarId },
    }

    let mut stack: Vec<Frame> = Vec::new();
    let mut cur_expr = expr;
    let mut cur_env: std::borrow::Cow<LexicalEnv> = std::borrow::Cow::Borrowed(env);
    let mut cur_path: Vec<u32> = path.to_vec();

    let leaf_value: TypeVarId = 'descend: loop {
        let value = match cur_expr {
            PseudoExpr::Var { name, id, .. } => {
                solver.resolve_binding_in_env(name, id.get(), &cur_env)
            }
            PseudoExpr::Let { name, id, body, .. } => {
                let binding_key = let_binding_key(*id);
                cur_env.to_mut().push(name.clone(), binding_key);
                cur_path = child_path(&cur_path, 1);
                cur_expr = body;
                continue 'descend;
            }
            PseudoExpr::Int(_) => {
                let tv = solver.fresh();
                solver.constrain_known(tv, PseudoType::Int);
                tv
            }
            PseudoExpr::ByteArray(_) => {
                let tv = solver.fresh();
                solver.constrain_known(tv, PseudoType::ByteArray);
                tv
            }
            PseudoExpr::String(_) => {
                let tv = solver.fresh();
                solver.constrain_known(tv, PseudoType::String);
                tv
            }
            PseudoExpr::Bool(_) => {
                let tv = solver.fresh();
                solver.constrain_known(tv, PseudoType::Bool);
                tv
            }
            PseudoExpr::Unit => {
                let tv = solver.fresh();
                solver.constrain_known(tv, PseudoType::Unit);
                tv
            }
            PseudoExpr::Constr { shape, fields, .. } => {
                let tv = solver.fresh();
                match shape.as_known() {
                    Some(KnownConstructor::Some) => {
                        stack.push(Frame::ConstrUnify { tv });
                        cur_path = child_path(&cur_path, 0);
                        cur_expr = &fields[0];
                        continue 'descend;
                    }
                    Some(KnownConstructor::None) => {
                        solver
                            .constrain_known(tv, PseudoType::Option(Rc::new(PseudoType::Unknown)));
                        tv
                    }
                    Some(KnownConstructor::True | KnownConstructor::False) => {
                        solver.constrain_known(tv, PseudoType::Bool);
                        tv
                    }
                    Some(KnownConstructor::Nil) => {
                        solver.constrain_known(tv, PseudoType::List(Rc::new(PseudoType::Unknown)));
                        tv
                    }
                    Some(KnownConstructor::Cons) => {
                        stack.push(Frame::ConstrUnify { tv });
                        cur_path = child_path(&cur_path, 0);
                        cur_expr = &fields[0];
                        continue 'descend;
                    }
                    Some(
                        KnownConstructor::Less
                        | KnownConstructor::Equal
                        | KnownConstructor::Greater,
                    ) => {
                        solver.constrain_known(tv, PseudoType::Named("Ordering".to_string()));
                        tv
                    }
                    Some(
                        KnownConstructor::Ok | KnownConstructor::Error | KnownConstructor::Pair,
                    )
                    | None => tv,
                    // Cardano-purpose variants — no `PseudoType` representation.
                    Some(_) => tv,
                }
            }
            PseudoExpr::BinOp { op, .. } => {
                let tv = solver.fresh();
                match op {
                    BinaryOp::Add
                    | BinaryOp::Sub
                    | BinaryOp::Mul
                    | BinaryOp::Div
                    | BinaryOp::Mod => {
                        solver.constrain_known(tv, PseudoType::Int);
                    }
                    BinaryOp::Eq
                    | BinaryOp::Neq
                    | BinaryOp::Lt
                    | BinaryOp::Lte
                    | BinaryOp::Gt
                    | BinaryOp::Gte
                    | BinaryOp::And
                    | BinaryOp::Or => {
                        solver.constrain_known(tv, PseudoType::Bool);
                    }
                    BinaryOp::Cons | BinaryOp::Concat => {}
                }
                tv
            }
            PseudoExpr::UnOp { op, .. } => {
                let tv = solver.fresh();
                match op {
                    UnaryOp::Not => solver.constrain_known(tv, PseudoType::Bool),
                    UnaryOp::Negate | UnaryOp::Length => {
                        solver.constrain_known(tv, PseudoType::Int)
                    }
                }
                tv
            }
            // Then-branch type; the else branch is constrained equal.
            PseudoExpr::If { then_branch, .. } => {
                cur_path = child_path(&cur_path, 1);
                cur_expr = then_branch;
                continue 'descend;
            }
            PseudoExpr::FieldAccess { selector, .. } => {
                let tv = solver.fresh();
                match selector.as_pretty_name() {
                    "fields" => {
                        solver.constrain_known(tv, PseudoType::List(Rc::new(PseudoType::Data)));
                    }
                    "tag" => {
                        solver.constrain_known(tv, PseudoType::Int);
                    }
                    "head" => {
                        solver.constrain_known(tv, PseudoType::Data);
                    }
                    "tail" => {
                        solver.constrain_known(tv, PseudoType::List(Rc::new(PseudoType::Unknown)));
                    }
                    _ => {}
                }
                tv
            }
            PseudoExpr::IndexAccess { collection, .. } => {
                let tv = solver.fresh();
                if let PseudoExpr::FieldAccess { selector, .. } = collection.as_ref()
                    && selector.as_pretty_name() == "fields"
                {
                    solver.constrain_known(tv, PseudoType::Data);
                }
                tv
            }
            PseudoExpr::When { clauses, .. } => {
                // Type of when = type of first non-error clause body
                let mut child_index = 1;
                let mut matched = None;
                for clause in clauses {
                    if matches!(&clause.pattern, WhenPattern::Literal(_)) {
                        child_index += 1;
                    }
                    if clause.guard.is_some() {
                        child_index += 1;
                    }
                    if !matches!(&clause.body, PseudoExpr::Error { .. }) {
                        matched = Some((&clause.body, child_index));
                        break;
                    }
                    child_index += 1;
                }
                match matched {
                    Some((body, child_index)) => {
                        cur_path = child_path(&cur_path, child_index);
                        cur_expr = body;
                        continue 'descend;
                    }
                    None => solver.fresh(),
                }
            }
            PseudoExpr::Trace {
                value: trace_value, ..
            } => {
                cur_path = child_path(&cur_path, 1);
                cur_expr = trace_value;
                continue 'descend;
            }
            PseudoExpr::List { elements, .. } => {
                let tv = solver.fresh();
                match elements.first() {
                    Some(first) => {
                        // No List(Var) form exists here, so the element
                        // type is left to `generate_constraints`; only
                        // walked for its constraint side effects.
                        stack.push(Frame::Discard { tv });
                        cur_path = child_path(&cur_path, 0);
                        cur_expr = first;
                        continue 'descend;
                    }
                    None => tv,
                }
            }
            PseudoExpr::Pair(_a, _b) => solver.fresh(),
            PseudoExpr::BuiltinCall { name, args } => {
                let tv = solver.fresh();
                // Constrain based on known builtin return types.
                if let Some(t) = infer_builtin_return_type(name, args) {
                    solver.constrain(tv, TypeExpr::Known(Rc::new(t)));
                }
                tv
            }
            // Lambda/RecFn get a Function type of matching arity with
            // all children Unknown; `enrich.rs` fills in the param/ret
            // children after the solve.
            PseudoExpr::Lambda { params, .. } => {
                let tv = solver.fresh();
                solver.constrain_known(tv, unknown_function_type(params.len()));
                tv
            }
            PseudoExpr::RecFn { name, params, .. } => {
                // RecFn's name binds the function itself, so re-use the
                // name's tv instead of allocating an unrelated fresh one.
                let tv = solver.var_for_var_id(name.id);
                solver.constrain_known(tv, unknown_function_type(params.len()));
                tv
            }
            _ => solver.fresh(),
        };
        break value;
    };

    // Propagate the leaf's value up through any pending frames — the
    // "return to caller" half of each Constr::Some/Cons/List recursive
    // call above, in the same order those calls would have unwound.
    let mut value = leaf_value;
    while let Some(frame) = stack.pop() {
        value = match frame {
            Frame::ConstrUnify { tv } => {
                let fresh = solver.fresh();
                solver.constrain_eq(fresh, value);
                tv
            }
            Frame::Discard { tv } => tv,
        };
    }
    value
}

/// Build a Function type with `param_count` Unknown params and
/// Unknown ret. The constraint system has no type-var-bearing
/// Function representation, so every Lambda emits this same
/// arity-only shape; the renderer maps nested Unknowns to `_`.
fn unknown_function_type(param_count: usize) -> PseudoType {
    PseudoType::Function {
        params: (0..param_count)
            .map(|_| Rc::new(PseudoType::Unknown))
            .collect(),
        ret: Rc::new(PseudoType::Unknown),
    }
}

/// Return type for known builtins.
///
/// Monomorphic cases delegate to [`BuiltinId::monomorphic_return_type`] so
/// the knowledge lives in one place. Polymorphic `List.head` falls back to
/// `Data` because the solver context carries no element-type information.
pub(crate) fn infer_builtin_return_type(name: &str, args: &[PseudoExpr]) -> Option<PseudoType> {
    let builtin = BuiltinId::from_name(name)?;
    if let Some(ty) = builtin.monomorphic_return_type() {
        return Some(ty);
    }
    let n = args.len();
    match builtin {
        BuiltinId::ListHead if n >= 1 => Some(PseudoType::Data),
        // ListTail is intentionally unresolved — element type propagated via
        // constraints elsewhere in the solver.
        _ => None,
    }
}

/// Whether an expression is Bool by its own structure, not merely because
/// it sits in an `if` condition.
///
/// UPLC's `ifThenElse` dispatches on Data constructor tags (0 = True,
/// non-0 = False), so a plain variable in condition position need not be Bool.
fn is_inherently_bool(expr: &PseudoExpr) -> bool {
    match expr {
        // Comparisons always produce Bool
        PseudoExpr::BinOp { op, .. } => matches!(
            op,
            BinaryOp::Eq
                | BinaryOp::Neq
                | BinaryOp::Lt
                | BinaryOp::Lte
                | BinaryOp::Gt
                | BinaryOp::Gte
                | BinaryOp::And
                | BinaryOp::Or
        ),
        // Logical negation produces Bool
        PseudoExpr::UnOp {
            op: UnaryOp::Not, ..
        } => true,
        // Bool literal
        PseudoExpr::Bool(_) => true,
        // Builtin calls that return Bool (e.g. List.is_empty, Int.eq, ...)
        PseudoExpr::BuiltinCall { name, .. } => {
            BuiltinId::from_name(name.as_str()).is_some_and(BuiltinId::returns_bool)
        }
        // A variable with an already-known Bool type (via type_resolution())
        PseudoExpr::Var { .. }
            if expr
                .type_resolution()
                .as_known()
                .is_some_and(|t| **t == PseudoType::Bool) =>
        {
            true
        }
        // Everything else (plain Var, FieldAccess, Apply, etc.) — not inherently Bool
        _ => false,
    }
}

/// Walk the AST: assign type variables (seeding from existing tipos) and
/// generate forward unification constraints in a single pass.
fn generate_constraints(
    expr: &PseudoExpr,
    solver: &mut TypeSolver,
    env: &mut LexicalEnv,
    path: &[u32],
) {
    use crate::pseudo::ast::{Binder, WhenClause};

    enum Step<'a> {
        /// Walk one node: its own constraint work, then its children.
        Visit {
            expr: &'a PseudoExpr,
            path: Vec<u32>,
        },
        /// `env.push` sitting between a `Let`'s value and body descents.
        PushBinding { name: String, key: BindingKey },
        /// Matching `env.pop`s, after the scoped child.
        PopEnv { count: usize },
        /// Pre-work for one `when` clause: binder scope + pattern constraints,
        /// then the clause's own children.
        WhenClausePre {
            clauses: &'a [WhenClause],
            index: usize,
            subject_name: Option<&'a Binder>,
            subject_tv: TypeVarId,
            /// Path of the `when` node itself.
            path: Vec<u32>,
            /// Running child index at clause entry.
            child_index: u32,
        },
        /// `body_tvs.push(expr_type_var(body))`, between the guard and body
        /// descents of a clause.
        WhenBodyTv {
            body: &'a PseudoExpr,
            path: Vec<u32>,
        },
        /// Cross-clause body unification, then the subject descent — both run
        /// after every clause, as in the recursive original.
        WhenFinish {
            subject: &'a PseudoExpr,
            path: Vec<u32>,
        },
    }

    fn visit<'a>(expr: &'a PseudoExpr, path: Vec<u32>) -> Step<'a> {
        Step::Visit { expr, path }
    }

    let mut stack: Vec<Step<'_>> = vec![visit(expr, path.to_vec())];
    let mut body_tvs_stack: Vec<Vec<TypeVarId>> = Vec::new();

    while let Some(step) = stack.pop() {
        match step {
            Step::PushBinding { name, key } => env.push(name, key),
            Step::PopEnv { count } => {
                for _ in 0..count {
                    env.pop();
                }
            }
            Step::WhenBodyTv { body, path } => {
                if !matches!(body, PseudoExpr::Error { .. }) {
                    let tv = expr_type_var(body, solver, env, &path);
                    if let Some(body_tvs) = body_tvs_stack.last_mut() {
                        body_tvs.push(tv);
                    }
                }
            }
            Step::WhenFinish { subject, path } => {
                let body_tvs = body_tvs_stack.pop().unwrap_or_default();
                for pair in body_tvs.windows(2) {
                    solver.constrain_eq(pair[0], pair[1]);
                }
                stack.push(visit(subject, path));
            }
            Step::WhenClausePre {
                clauses,
                index,
                subject_name,
                subject_tv,
                path,
                child_index,
            } => {
                let clause = &clauses[index];
                let next_clause = |child_index: u32| {
                    (index + 1 < clauses.len()).then(|| Step::WhenClausePre {
                        clauses,
                        index: index + 1,
                        subject_name,
                        subject_tv,
                        path: path.clone(),
                        child_index,
                    })
                };
                // Set by the `Literal` arm; every other arm leaves the clause's
                // first child index untouched.
                let mut literal: Option<(&PseudoExpr, Vec<u32>)> = None;
                let mut child_index = child_index;

                if let Some(subject_name) = subject_name {
                    env.push(subject_name.to_string(), BindingKey::VarId(subject_name.id));
                }
                let binders = pattern_binders(&clause.pattern);
                for binder in &binders {
                    solver.var_for_var_id(binder.id);
                    env.push(binder.name.clone(), BindingKey::VarId(binder.id));
                }

                match &clause.pattern {
                    WhenPattern::List { .. } => {
                        solver.constrain_known(
                            subject_tv,
                            PseudoType::List(Rc::new(PseudoType::Unknown)),
                        );
                    }
                    WhenPattern::Tuple(fields) => {
                        solver.constrain_known(
                            subject_tv,
                            PseudoType::Tuple(
                                fields
                                    .iter()
                                    .map(|_| Rc::new(PseudoType::Unknown))
                                    .collect(),
                            ),
                        );
                    }
                    WhenPattern::Constructor { shape, fields, .. } => {
                        if matches!(shape.as_known(), Some(KnownConstructor::Pair)) {
                            solver.constrain_known(
                                subject_tv,
                                PseudoType::Pair(
                                    Rc::new(PseudoType::Unknown),
                                    Rc::new(PseudoType::Unknown),
                                ),
                            );

                            let left_tv = solver.resolve_binding_in_env(
                                fields[0].as_str(),
                                Some(fields[0].id),
                                env,
                            );
                            let right_tv = solver.resolve_binding_in_env(
                                fields[1].as_str(),
                                Some(fields[1].id),
                                env,
                            );

                            let left_res = solver.find(left_tv);
                            let right_res = solver.find(right_tv);
                            if let (TypeExpr::Known(left), TypeExpr::Known(right)) =
                                (&left_res, &right_res)
                            {
                                solver.constrain(
                                    subject_tv,
                                    TypeExpr::Known(Rc::new(PseudoType::Pair(
                                        left.clone(),
                                        right.clone(),
                                    ))),
                                );
                            }

                            let subj_res = solver.find(subject_tv);
                            if let TypeExpr::Known(st) = subj_res
                                && let PseudoType::Pair(left, right) = st.as_ref()
                            {
                                solver.constrain(left_tv, TypeExpr::Known(left.clone()));
                                solver.constrain(right_tv, TypeExpr::Known(right.clone()));
                            }
                            // No children, no `child_index` bump, and no
                            // `env.pop` for this clause's binders.
                            if let Some(next) = next_clause(child_index) {
                                stack.push(next);
                            }
                            continue;
                        }

                        solver.constrain_known(subject_tv, PseudoType::Data);
                        match shape.as_known() {
                            Some(KnownConstructor::Some) => {
                                // subject = Option(typeof(field))
                                let field_tv = solver.resolve_binding_in_env(
                                    fields[0].as_str(),
                                    Some(fields[0].id),
                                    env,
                                );
                                let resolved = solver.find(field_tv);
                                if let TypeExpr::Known(t) = resolved {
                                    solver.constrain(
                                        subject_tv,
                                        TypeExpr::Known(Rc::new(PseudoType::Option(t))),
                                    );
                                }
                                // Also, if subject already has a known Option type,
                                // constrain the field to the inner type
                                let subj_resolved = solver.find(subject_tv);
                                if let TypeExpr::Known(st) = subj_resolved
                                    && let PseudoType::Option(inner) = st.as_ref()
                                {
                                    solver.constrain(field_tv, TypeExpr::Known(inner.clone()));
                                }
                            }
                            Some(KnownConstructor::None) => {
                                // subject = Option<?>
                                // Don't overwrite a more specific type
                            }
                            Some(KnownConstructor::Ok) => {
                                let field_tv = solver.resolve_binding_in_env(
                                    fields[0].as_str(),
                                    Some(fields[0].id),
                                    env,
                                );
                                let resolved = solver.find(field_tv);
                                if let TypeExpr::Known(t) = resolved {
                                    solver.constrain(
                                        subject_tv,
                                        TypeExpr::Known(Rc::new(PseudoType::Result(
                                            t,
                                            Rc::new(PseudoType::Unknown),
                                        ))),
                                    );
                                }
                                let subj_resolved = solver.find(subject_tv);
                                if let TypeExpr::Known(st) = subj_resolved
                                    && let PseudoType::Result(ok, _) = st.as_ref()
                                {
                                    solver.constrain(field_tv, TypeExpr::Known(ok.clone()));
                                }
                            }
                            Some(KnownConstructor::Error) => {
                                let field_tv = solver.resolve_binding_in_env(
                                    fields[0].as_str(),
                                    Some(fields[0].id),
                                    env,
                                );
                                let resolved = solver.find(field_tv);
                                if let TypeExpr::Known(t) = resolved {
                                    solver.constrain(
                                        subject_tv,
                                        TypeExpr::Known(Rc::new(PseudoType::Result(
                                            Rc::new(PseudoType::Unknown),
                                            t,
                                        ))),
                                    );
                                }
                                let subj_resolved = solver.find(subject_tv);
                                if let TypeExpr::Known(st) = subj_resolved
                                    && let PseudoType::Result(_, err) = st.as_ref()
                                {
                                    solver.constrain(field_tv, TypeExpr::Known(err.clone()));
                                }
                            }
                            Some(
                                KnownConstructor::True
                                | KnownConstructor::False
                                | KnownConstructor::Pair
                                | KnownConstructor::Nil
                                | KnownConstructor::Cons
                                | KnownConstructor::Less
                                | KnownConstructor::Equal
                                | KnownConstructor::Greater,
                            )
                            | None => {}
                            // Cardano-purpose variants — no `PseudoType` rep.
                            Some(_) => {}
                        }
                    }
                    WhenPattern::Pair(a, b) => {
                        solver.constrain_known(
                            subject_tv,
                            PseudoType::Pair(
                                Rc::new(PseudoType::Unknown),
                                Rc::new(PseudoType::Unknown),
                            ),
                        );
                        let a_tv = solver.resolve_binding_in_env(a, Some(a.id), env);
                        let b_tv = solver.resolve_binding_in_env(b, Some(b.id), env);
                        // subject = Pair(typeof(a), typeof(b))
                        let a_res = solver.find(a_tv);
                        let b_res = solver.find(b_tv);
                        if let (TypeExpr::Known(at), TypeExpr::Known(bt)) = (&a_res, &b_res) {
                            solver.constrain(
                                subject_tv,
                                TypeExpr::Known(Rc::new(PseudoType::Pair(at.clone(), bt.clone()))),
                            );
                        }
                        // Reverse: if subject is Pair, push into binders
                        let subj_res = solver.find(subject_tv);
                        if let TypeExpr::Known(st) = subj_res
                            && let PseudoType::Pair(fst, snd) = st.as_ref()
                        {
                            solver.constrain(a_tv, TypeExpr::Known(fst.clone()));
                            solver.constrain(b_tv, TypeExpr::Known(snd.clone()));
                        }
                    }
                    WhenPattern::Literal(lit) => {
                        let lit_path = child_path(&path, child_index);
                        let lit_tv = expr_type_var(lit, solver, env, &lit_path);
                        solver.constrain_eq(subject_tv, lit_tv);
                        literal = Some((lit, lit_path));
                        child_index += 1;
                    }
                    _ => {}
                }

                let guard = if let Some(guard) = clause.guard.as_ref() {
                    let guard_path = child_path(&path, child_index);
                    child_index += 1;
                    Some((guard, guard_path))
                } else {
                    None
                };
                let body_path = child_path(&path, child_index);
                child_index += 1;

                let pop_count = binders.len() + usize::from(subject_name.is_some());

                // Pushed in reverse of the order they run: literal, guard, body
                // type var, body, the clause's `env.pop`s, then the next clause.
                if let Some(next) = next_clause(child_index) {
                    stack.push(next);
                }
                stack.push(Step::PopEnv { count: pop_count });
                stack.push(visit(&clause.body, body_path.clone()));
                stack.push(Step::WhenBodyTv {
                    body: &clause.body,
                    path: body_path,
                });
                if let Some((guard, guard_path)) = guard {
                    stack.push(visit(guard, guard_path));
                }
                if let Some((lit, lit_path)) = literal {
                    stack.push(visit(lit, lit_path));
                }
            }

            Step::Visit { expr, path } => match expr {
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    // A plain Var condition may be Data checked by constructor tag, so
                    // only inherently-boolean conditions are constrained to Bool.
                    if is_inherently_bool(condition) {
                        let cond_tv = expr_type_var(condition, solver, env, &child_path(&path, 0));
                        solver.constrain_known(cond_tv, PseudoType::Bool);
                    }

                    // Both branches share a type unless one is Error.
                    let then_tv = expr_type_var(then_branch, solver, env, &child_path(&path, 1));
                    let else_tv = expr_type_var(else_branch, solver, env, &child_path(&path, 2));
                    if !matches!(then_branch.as_ref(), PseudoExpr::Error { .. })
                        && !matches!(else_branch.as_ref(), PseudoExpr::Error { .. })
                    {
                        solver.constrain_eq(then_tv, else_tv);
                    }

                    // Recurse
                    stack.push(visit(else_branch, child_path(&path, 2)));
                    stack.push(visit(then_branch, child_path(&path, 1)));
                    stack.push(visit(condition, child_path(&path, 0)));
                }

                PseudoExpr::BinOp { op, left, right } => {
                    let left_tv = expr_type_var(left, solver, env, &child_path(&path, 0));
                    let right_tv = expr_type_var(right, solver, env, &child_path(&path, 1));

                    match op {
                        BinaryOp::Add
                        | BinaryOp::Sub
                        | BinaryOp::Mul
                        | BinaryOp::Div
                        | BinaryOp::Mod => {
                            solver.constrain_known(left_tv, PseudoType::Int);
                            solver.constrain_known(right_tv, PseudoType::Int);
                        }
                        BinaryOp::And | BinaryOp::Or => {
                            solver.constrain_known(left_tv, PseudoType::Bool);
                            solver.constrain_known(right_tv, PseudoType::Bool);
                        }
                        BinaryOp::Eq
                        | BinaryOp::Neq
                        | BinaryOp::Lt
                        | BinaryOp::Lte
                        | BinaryOp::Gt
                        | BinaryOp::Gte => {
                            // Both sides share a type; which one is unknown.
                            solver.constrain_eq(left_tv, right_tv);
                        }
                        BinaryOp::Cons => {
                            // `head :: tail`: no constraint ties the
                            // tail to List<typeof(head)>.
                        }
                        BinaryOp::Concat => {
                            // Both sides same type (ByteArray or String)
                            solver.constrain_eq(left_tv, right_tv);
                        }
                    }

                    stack.push(visit(right, child_path(&path, 1)));
                    stack.push(visit(left, child_path(&path, 0)));
                }

                PseudoExpr::UnOp { op, operand } => {
                    let operand_tv = expr_type_var(operand, solver, env, &child_path(&path, 0));
                    match op {
                        UnaryOp::Not => solver.constrain_known(operand_tv, PseudoType::Bool),
                        UnaryOp::Negate => solver.constrain_known(operand_tv, PseudoType::Int),
                        UnaryOp::Length => {} // operand could be ByteArray or List
                    }
                    stack.push(visit(operand, child_path(&path, 0)));
                }

                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                    ..
                } => {
                    let binding_key = let_binding_key(*id);
                    let name_tv = solver.var_for_binding_key(binding_key.clone());
                    let value_tv = expr_type_var(value, solver, env, &child_path(&path, 0));
                    solver.constrain_eq(name_tv, value_tv);

                    // The binding lands between the two descents: the body must
                    // see it, the value must not.
                    stack.push(Step::PopEnv { count: 1 });
                    stack.push(visit(body, child_path(&path, 1)));
                    stack.push(Step::PushBinding {
                        name: name.clone(),
                        key: binding_key,
                    });
                    stack.push(visit(value, child_path(&path, 0)));
                }

                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let subject_tv = expr_type_var(subject, solver, env, &child_path(&path, 0));
                    if let Some(subject_name) = subject_name {
                        let subject_name_tv = solver.var_for_var_id(subject_name.id);
                        solver.constrain_eq(subject_name_tv, subject_tv);
                    }

                    body_tvs_stack.push(Vec::new());
                    stack.push(Step::WhenFinish {
                        subject,
                        path: child_path(&path, 0),
                    });
                    if !clauses.is_empty() {
                        stack.push(Step::WhenClausePre {
                            clauses: clauses.as_slice(),
                            index: 0,
                            subject_name: subject_name.as_ref(),
                            subject_tv,
                            path,
                            child_index: 1,
                        });
                    }
                }

                PseudoExpr::Constr { shape, fields, .. } => {
                    // Build a refined type from the field types and constrain the
                    // constructor's own type variable — Let bindings unify with it.

                    let constr_tv = expr_type_var(expr, solver, env, &path);

                    match shape.as_known() {
                        Some(KnownConstructor::Some) => {
                            let inner_tv =
                                expr_type_var(&fields[0], solver, env, &child_path(&path, 0));
                            // Build Option(typeof(field)) and constrain the constr to it.
                            let inner_resolved = solver.find(inner_tv);
                            let inner_type = match inner_resolved {
                                TypeExpr::Known(t) => t,
                                TypeExpr::Var(_) => Rc::new(PseudoType::Unknown),
                            };
                            solver.constrain(
                                constr_tv,
                                TypeExpr::Known(Rc::new(PseudoType::Option(inner_type))),
                            );
                        }
                        Some(KnownConstructor::Ok) => {
                            let inner_tv =
                                expr_type_var(&fields[0], solver, env, &child_path(&path, 0));
                            let inner_resolved = solver.find(inner_tv);
                            let ok_type = match inner_resolved {
                                TypeExpr::Known(t) => t,
                                TypeExpr::Var(_) => Rc::new(PseudoType::Unknown),
                            };
                            let err_type: Rc<PseudoType> = Rc::new(PseudoType::Unknown);
                            solver.constrain(
                                constr_tv,
                                TypeExpr::Known(Rc::new(PseudoType::Result(ok_type, err_type))),
                            );
                        }
                        Some(KnownConstructor::Error) => {
                            let inner_tv =
                                expr_type_var(&fields[0], solver, env, &child_path(&path, 0));
                            let inner_resolved = solver.find(inner_tv);
                            let err_type = match inner_resolved {
                                TypeExpr::Known(t) => t,
                                TypeExpr::Var(_) => Rc::new(PseudoType::Unknown),
                            };
                            let ok_type: Rc<PseudoType> = Rc::new(PseudoType::Unknown);
                            solver.constrain(
                                constr_tv,
                                TypeExpr::Known(Rc::new(PseudoType::Result(ok_type, err_type))),
                            );
                        }
                        Some(KnownConstructor::Pair) => {
                            let a_tv =
                                expr_type_var(&fields[0], solver, env, &child_path(&path, 0));
                            let b_tv =
                                expr_type_var(&fields[1], solver, env, &child_path(&path, 1));
                            let a_resolved = solver.find(a_tv);
                            let b_resolved = solver.find(b_tv);
                            let fst_type = match a_resolved {
                                TypeExpr::Known(t) => t,
                                TypeExpr::Var(_) => Rc::new(PseudoType::Unknown),
                            };
                            let snd_type = match b_resolved {
                                TypeExpr::Known(t) => t,
                                TypeExpr::Var(_) => Rc::new(PseudoType::Unknown),
                            };
                            solver.constrain(
                                constr_tv,
                                TypeExpr::Known(Rc::new(PseudoType::Pair(fst_type, snd_type))),
                            );
                        }
                        Some(KnownConstructor::None) => {
                            // None -> Option<?> but don't overwrite a more specific existing type
                            solver.constrain(
                                constr_tv,
                                TypeExpr::Known(Rc::new(PseudoType::Option(Rc::new(
                                    PseudoType::Unknown,
                                )))),
                            );
                        }
                        Some(KnownConstructor::Nil) => {
                            solver.constrain(
                                constr_tv,
                                TypeExpr::Known(Rc::new(PseudoType::List(Rc::new(
                                    PseudoType::Unknown,
                                )))),
                            );
                        }
                        Some(KnownConstructor::Cons) => {
                            let head_tv =
                                expr_type_var(&fields[0], solver, env, &child_path(&path, 0));
                            let head_resolved = solver.find(head_tv);
                            let head_type = match head_resolved {
                                TypeExpr::Known(t) => t,
                                TypeExpr::Var(_) => Rc::new(PseudoType::Unknown),
                            };
                            solver.constrain(
                                constr_tv,
                                TypeExpr::Known(Rc::new(PseudoType::List(head_type))),
                            );
                        }
                        Some(
                            KnownConstructor::True
                            | KnownConstructor::False
                            | KnownConstructor::Less
                            | KnownConstructor::Equal
                            | KnownConstructor::Greater,
                        )
                        | None => {}
                        // Cardano-purpose variants — no `PseudoType` representation.
                        Some(_) => {}
                    }

                    for (index, field) in fields.iter().enumerate().rev() {
                        stack.push(visit(field, child_path(&path, index as u32)));
                    }
                }

                PseudoExpr::BuiltinCall { name, args } => {
                    // Constrain arguments based on known builtin signatures.
                    let n = args.len();
                    if let Some(builtin) = BuiltinId::from_name(name.as_str()) {
                        match builtin {
                            BuiltinId::ListIsEmpty | BuiltinId::ListHead | BuiltinId::ListTail
                                if n >= 1 =>
                            {
                                let arg_tv =
                                    expr_type_var(&args[0], solver, env, &child_path(&path, 0));
                                solver.constrain_known(
                                    arg_tv,
                                    PseudoType::List(Rc::new(PseudoType::Unknown)),
                                );
                            }
                            BuiltinId::DataUnInt
                            | BuiltinId::DataToInt
                            | BuiltinId::DataUnByteArray
                            | BuiltinId::DataToBytes
                            | BuiltinId::DataUnList
                            | BuiltinId::DataToList
                            | BuiltinId::DataUnMap
                            | BuiltinId::DataToMap
                            | BuiltinId::ConstrUnpack
                            | BuiltinId::DataUnConstr
                                if n >= 1 =>
                            {
                                let arg_tv =
                                    expr_type_var(&args[0], solver, env, &child_path(&path, 0));
                                solver.constrain_known(arg_tv, PseudoType::Data);
                            }
                            BuiltinId::DataInt | BuiltinId::IntToData if n >= 1 => {
                                let arg_tv =
                                    expr_type_var(&args[0], solver, env, &child_path(&path, 0));
                                solver.constrain_known(arg_tv, PseudoType::Int);
                            }
                            BuiltinId::DataByteArray | BuiltinId::ByteArrayToData if n >= 1 => {
                                let arg_tv =
                                    expr_type_var(&args[0], solver, env, &child_path(&path, 0));
                                solver.constrain_known(arg_tv, PseudoType::ByteArray);
                            }
                            BuiltinId::DataList | BuiltinId::ListToData if n >= 1 => {
                                let arg_tv =
                                    expr_type_var(&args[0], solver, env, &child_path(&path, 0));
                                solver.constrain_known(
                                    arg_tv,
                                    PseudoType::List(Rc::new(PseudoType::Data)),
                                );
                            }
                            BuiltinId::DataMap | BuiltinId::MapToData if n >= 1 => {
                                let arg_tv =
                                    expr_type_var(&args[0], solver, env, &child_path(&path, 0));
                                solver.constrain_known(
                                    arg_tv,
                                    PseudoType::List(Rc::new(PseudoType::Pair(
                                        Rc::new(PseudoType::Data),
                                        Rc::new(PseudoType::Data),
                                    ))),
                                );
                            }
                            BuiltinId::DataConstr if n >= 2 => {
                                let tag_tv =
                                    expr_type_var(&args[0], solver, env, &child_path(&path, 0));
                                solver.constrain_known(tag_tv, PseudoType::Int);

                                let fields_tv =
                                    expr_type_var(&args[1], solver, env, &child_path(&path, 1));
                                solver.constrain_known(
                                    fields_tv,
                                    PseudoType::List(Rc::new(PseudoType::Data)),
                                );
                            }
                            _ => {}
                        }
                    }

                    for (index, arg) in args.iter().enumerate().rev() {
                        stack.push(visit(arg, child_path(&path, index as u32)));
                    }
                }

                PseudoExpr::Apply { function, args } => {
                    for (index, arg) in args.iter().enumerate().rev() {
                        stack.push(visit(arg, child_path(&path, index as u32 + 1)));
                    }
                    stack.push(visit(function, child_path(&path, 0)));
                }
                PseudoExpr::Lambda { body, params, .. } => {
                    for param in params {
                        solver.var_for_var_id(param.id);
                        env.push(param.to_string(), BindingKey::VarId(param.id));
                    }
                    stack.push(Step::PopEnv {
                        count: params.len(),
                    });
                    stack.push(visit(body, child_path(&path, 0)));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    solver.var_for_var_id(name.id);
                    env.push(name.to_string(), BindingKey::VarId(name.id));
                    for param in params {
                        solver.var_for_var_id(param.id);
                        env.push(param.to_string(), BindingKey::VarId(param.id));
                    }
                    stack.push(Step::PopEnv {
                        count: params.len() + 1,
                    });
                    stack.push(visit(body, child_path(&path, 0)));
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail {
                        stack.push(visit(t, child_path(&path, elements.len() as u32)));
                    }
                    for (index, element) in elements.iter().enumerate().rev() {
                        stack.push(visit(element, child_path(&path, index as u32)));
                    }
                }
                PseudoExpr::Tuple(elements) => {
                    for (index, element) in elements.iter().enumerate().rev() {
                        stack.push(visit(element, child_path(&path, index as u32)));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    stack.push(visit(b, child_path(&path, 1)));
                    stack.push(visit(a, child_path(&path, 0)));
                }
                PseudoExpr::FieldAccess {
                    record, selector, ..
                } => {
                    let record_tv = expr_type_var(record, solver, env, &child_path(&path, 0));
                    match selector.as_pretty_name() {
                        "fields" | "tag" => {
                            solver.constrain_known(record_tv, PseudoType::Data);
                        }
                        "fst" | "snd" | "first" | "second" | "1st" | "2nd" => {
                            solver.constrain_known(
                                record_tv,
                                PseudoType::Pair(
                                    Rc::new(PseudoType::Unknown),
                                    Rc::new(PseudoType::Unknown),
                                ),
                            );
                        }
                        "head" | "tail" => {
                            solver.constrain_known(
                                record_tv,
                                PseudoType::List(Rc::new(PseudoType::Unknown)),
                            );
                        }
                        _ => {}
                    }
                    stack.push(visit(record, child_path(&path, 0)));
                }
                PseudoExpr::IndexAccess { collection, .. } => {
                    let collection_tv =
                        expr_type_var(collection, solver, env, &child_path(&path, 0));
                    solver.constrain_known(
                        collection_tv,
                        PseudoType::List(Rc::new(PseudoType::Unknown)),
                    );
                    stack.push(visit(collection, child_path(&path, 0)));
                }
                PseudoExpr::Trace { message, value } => {
                    stack.push(visit(value, child_path(&path, 1)));
                    stack.push(visit(message, child_path(&path, 0)));
                }
                PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                    stack.push(visit(inner, child_path(&path, 0)));
                }
                PseudoExpr::Var { name, id, .. } => {
                    let _tv = solver.resolve_binding_in_env(name, id.get(), env);
                }
                _ => {}
            },
        }
    }
}

// Public entry point

/// Run the constraint-based type solver on the AST.
///
/// This refines parameterised types like `Option<?>` → `Option<ByteArray>`
/// by generating and solving unification constraints across the AST. The
/// returned [`FinalTypeTable`] is keyed by the `VarId`s of declaration sites
/// (let, lambda/recfn params, when subject name, pattern binders); reference
/// sites are not populated, so display/render-prep rewrites must re-map or
/// re-solve the table before relying on complete coverage.
///
/// Seeds no version-gated Cardano context; callers with a `ScriptVersion`
/// use [`solve_type_constraints_with_final_table_versioned`].
#[allow(dead_code)]
pub(crate) fn solve_type_constraints_with_final_table(
    expr: PseudoExpr,
) -> (PseudoExpr, FinalTypeTable) {
    solve_type_constraints_with_final_table_versioned(expr, None)
}

/// Solve with version-gated Cardano-context seeding. Under
/// `Some(PlutusV3)` the seeder runs, typing `script_context` as
/// `Named("ScriptContext")` per CIP-0035. V1/V2 and unknown
/// versions skip it: V2's `script_context` is Data at the
/// protocol level and is sometimes pair-pattern-matched after
/// simplifier inlining, which contradicts a named type.
pub(crate) fn solve_type_constraints_with_final_table_versioned(
    expr: PseudoExpr,
    version: Option<crate::decompile::ScriptVersion>,
) -> (PseudoExpr, FinalTypeTable) {
    let mut solver = TypeSolver::new();
    let mut env = LexicalEnv::default();

    // Pass 1: Assign type variables + generate forward constraints
    generate_constraints(&expr, &mut solver, &mut env, &[]);

    // Solve round 1 (forward)
    solver.solve();

    // Pass 2: Generate backward constraints (field types → container types)
    generate_backward_constraints(&expr, &mut solver, &mut env, &[]);

    // Solve round 2 (backward)
    solver.solve();

    // Pass 3: substitution is a no-op since `PseudoExpr::{Var,Let,Constr}`
    // carry no `tipo` fields.

    // Pass 4: harvest a final-AST-keyed side table of solved declaration
    // types. Only declaration sites are recorded here.
    let mut final_types = harvest_final_type_table(&expr, &solver);

    // Pass 4.5: seed Cardano-context types before enrichment, so
    // the fixed-point can propagate them through Apply chains and
    // body derivation. V3 only; `seed_cardano.rs` explains V2.
    if matches!(version, Some(crate::decompile::ScriptVersion::PlutusV3)) {
        seed_cardano_context_types(&expr, &mut final_types);
    }

    // Pass 4.6: seed monomorphic builtin argument types. AddInteger,
    // Sha256 and the like have one signature across Plutus versions,
    // so this is version-agnostic; enrichment propagates the seeds.
    seed_builtin_arg_types(&expr, &mut final_types);

    // Pass 5: post-solve enrichment of Function entries. Binders
    // arrive as `Function { params: [Unknown; N], ret: Unknown }`;
    // this pass refines params from harvested param IDs and ret
    // from structural body-type derivation.
    enrich_function_types(&expr, &mut final_types);
    final_types.freeze();

    (expr, final_types)
}

/// Test-only wrapper that discards the solved side table. Production
/// callers use [`solve_type_constraints_with_final_table`] so solved
/// types reach render and invariant consumers.
#[cfg(test)]
pub(crate) fn solve_type_constraints(expr: PseudoExpr) -> PseudoExpr {
    solve_type_constraints_with_final_table(expr).0
}

#[cfg(test)]
mod tests;
