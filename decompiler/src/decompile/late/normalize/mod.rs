//! Late semantic and display normalization.
//!
//! The final cleanup layer, run once the structural/type pipeline has
//! produced a stable pseudo AST: end-of-pipeline semantic cleanup plus the
//! display normalization/rewrite entry points and their orchestration.

use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

use super::super::constructor_data::{
    extract_constr_unpack_tag_eq, is_bool_false_like, make_standard_option_none,
};
use super::super::mid::type_env::TypeEnvironment;
use super::super::naming::render_improve_variable_names;
use super::super::simplify::convert_expect_tag_to_constr_when;
use super::super::{DecompileOptions, eliminate_var_aliases, normalize_list_cons_literals};
use super::list_alias::repair_list_prepend_alias_lets;
use super::option_cps::rewrite_option_cps_calls;

mod bool_option_confusion;
mod boolish_data_if;
mod constructor_field_access;
mod display_polish_layer;
mod forward_let_dependencies;
mod option;
mod tail_helpers;
mod validator;

pub(crate) use self::bool_option_confusion::fix_bool_option_confusion;
pub(crate) use self::boolish_data_if::rewrite_boolish_data_ifs;
use self::constructor_field_access::{
    rewrite_constructor_subject_field_accesses_to_pattern_binders, subject_supports_data_fields,
};
pub(crate) use self::display_polish_layer::run_display_polish_layer;
pub(crate) use self::forward_let_dependencies::repair_forward_let_dependencies;
use self::option::like_detection::{collect_option_like_function_names, is_option_like_value};
use self::option::pattern_naming::{fill_option_wildcard_pattern, rename_option_pattern};
use self::option::payload_access::replace_subject_payload_access;
use self::option::payload_binder_recovery::recover_missing_option_payload_binders;
pub(crate) use self::tail_helpers::{hoist_let_from_expect, normalize_data_constr_calls};
use self::validator::constructor_recovery::try_recover_generated_constructor_fields;
use self::validator::env::{ValidatorEnv, infer_root_validator_env};
use self::validator::expr::{field_binder_expr, redeemer_field_expr, script_context_field_expr};
use self::validator::helpers::{collect_pattern_binders, generated_field_index, list_pattern_head};
use self::validator::scope::{
    ScopeFrame, binder_matches_var, find_subject_binder, is_bound, nearest_constructor_field,
    nearest_constructor_subject, nearest_list_head,
};

/// Run the final semantic cleanup layer after structural/type recovery.
pub(crate) fn run_structural_final_cleanup(
    mut expr: PseudoExpr,
    env: Option<&TypeEnvironment>,
    options: &DecompileOptions,
    kind_annotations: &std::collections::HashMap<
        crate::pseudo::var_id::VarId,
        crate::pseudo::nameless::VarKind,
    >,
) -> PseudoExpr {
    if options.simplify_passes.any_enabled() {
        expr = run_late_structural_repairs(expr, env, options, kind_annotations);
    }

    if !options.safe_mode && options.readability_passes.any_enabled() {
        expr = run_late_semantic_fixpoint(expr, env, options, kind_annotations);
    }

    retarget_final_scope_refs(expr)
}

fn retarget_final_scope_refs(expr: PseudoExpr) -> PseudoExpr {
    super::super::ref_retarget::retarget_refs_by_scope(expr)
}

/// Early structural repair for free generated constructor carriers that can
/// already appear during the first simplify fixed point.
pub(crate) fn repair_free_generated_constructor_carriers(
    expr: PseudoExpr,
    kind_annotations: &std::collections::HashMap<
        crate::pseudo::var_id::VarId,
        crate::pseudo::nameless::VarKind,
    >,
    use_varkind_recovery: bool,
) -> PseudoExpr {
    recover_free_validator_carriers(expr, kind_annotations, use_varkind_recovery)
}

fn run_late_structural_repairs(
    mut expr: PseudoExpr,
    _env: Option<&TypeEnvironment>,
    options: &DecompileOptions,
    kind_annotations: &std::collections::HashMap<
        crate::pseudo::var_id::VarId,
        crate::pseudo::nameless::VarKind,
    >,
) -> PseudoExpr {
    let simplify_passes = &options.simplify_passes;
    let polish = &options.display_polish_passes;

    if simplify_passes.dead_let_elim {
        expr = eliminate_var_aliases(expr);
    }
    if simplify_passes.dead_let_elim {
        expr = repair_free_generated_constructor_carriers(
            expr,
            kind_annotations,
            options.use_varkind_recovery,
        );
    }
    if simplify_passes.dead_let_elim {
        expr = repair_forward_let_dependencies(expr);
    }
    if simplify_passes.collapse_tail_chains {
        expr = repair_list_prepend_alias_lets(expr);
    }
    // Alias elimination can expose fresh `List.prepend()(...)` / `List.cons(...)`
    // call sites late in the pipeline, so normalize list literals again here.
    if polish.normalize_list_cons_literals {
        expr = normalize_list_cons_literals(expr);
    }
    if polish.normalize_display_rewrites {
        expr = normalize_data_constr_calls(expr);
    }
    expr
}

fn run_late_semantic_fixpoint(
    mut expr: PseudoExpr,
    env: Option<&TypeEnvironment>,
    options: &DecompileOptions,
    kind_annotations: &std::collections::HashMap<
        crate::pseudo::var_id::VarId,
        crate::pseudo::nameless::VarKind,
    >,
) -> PseudoExpr {
    const MAX_LATE_SEMANTIC_ROUNDS: usize = 4;

    for _ in 0..MAX_LATE_SEMANTIC_ROUNDS {
        let before = expr.clone();
        expr = run_late_semantic_round(expr, env, options, kind_annotations);
        if expr.structural_eq(&before) {
            break;
        }
    }

    run_late_naming_fixpoint(expr)
}

fn run_late_semantic_round(
    mut expr: PseudoExpr,
    env: Option<&TypeEnvironment>,
    options: &DecompileOptions,
    kind_annotations: &std::collections::HashMap<
        crate::pseudo::var_id::VarId,
        crate::pseudo::nameless::VarKind,
    >,
) -> PseudoExpr {
    let polish = &options.display_polish_passes;
    let readability = &options.readability_passes;
    let structural = &options.structural_recovery_passes;
    let simplify_passes = &options.simplify_passes;

    if polish.simplify_boolean_and_identity {
        expr = rewrite_boolish_data_ifs(expr, env);
    }
    expr = run_option_like_semantic_round(expr, options, kind_annotations);
    if readability.hoist_local_helpers {
        expr = hoist_let_from_expect(expr);
    }
    if polish.eliminate_cps_selectors {
        expr = rewrite_option_cps_calls(expr, env);
    }
    // Run after option-CPS normalization so freshly exposed constructor/tag
    // surfaces re-enter the canonical option-like path in the same round.
    if structural.resolve_data_case {
        expr = convert_expect_tag_to_constr_when(expr);
    }
    if structural.extract_complex_when_subjects {
        expr = rewrite_constructor_subject_field_accesses_to_pattern_binders(expr);
    }
    expr = run_option_like_semantic_round(expr, options, kind_annotations);
    if simplify_passes.dead_let_elim {
        recover_free_validator_carriers(expr, kind_annotations, options.use_varkind_recovery)
    } else {
        expr
    }
}

fn run_option_like_semantic_round(
    mut expr: PseudoExpr,
    options: &DecompileOptions,
    kind_annotations: &std::collections::HashMap<
        crate::pseudo::var_id::VarId,
        crate::pseudo::nameless::VarKind,
    >,
) -> PseudoExpr {
    // `normalize_data_constr_calls` ran in the structural repair, so
    // `Data.Constr(0, ...)` builtins are already canonical here.
    expr = fix_bool_option_confusion(expr);
    expr = rename_option_like_patterns(expr, options, kind_annotations);
    expr
}

fn run_late_naming_fixpoint(mut expr: PseudoExpr) -> PseudoExpr {
    const MAX_LATE_NAMING_ROUNDS: usize = 3;

    for _ in 0..MAX_LATE_NAMING_ROUNDS {
        let updated = render_improve_variable_names(expr.clone());
        if updated.structural_eq(&expr) {
            return expr;
        }
        expr = updated;
    }

    expr
}

/// Recover free-looking validator names that should still be explicit field
/// accesses on root validator parameters — fields an earlier pass renamed
/// semantically (`inputs`, `outputs`, `mint`, `redeemer_fields_0`, ...) whose
/// carrier binding then disappeared.
fn recover_free_validator_carriers(
    expr: PseudoExpr,
    kind_annotations: &std::collections::HashMap<
        crate::pseudo::var_id::VarId,
        crate::pseudo::nameless::VarKind,
    >,
    use_varkind_recovery: bool,
) -> PseudoExpr {
    fn rewrite(
        expr: PseudoExpr,
        env: &ValidatorEnv,
        scopes: &mut Vec<ScopeFrame>,
        kind_annotations: &std::collections::HashMap<
            crate::pseudo::var_id::VarId,
            crate::pseudo::nameless::VarKind,
        >,
        use_varkind_recovery: bool,
    ) -> PseudoExpr {
        use crate::builtins::BuiltinId;
        use crate::pseudo::ast::{BinaryOp, UnaryOp, WhenClause};
        use crate::pseudo::field_selector::FieldSelector;
        use crate::pseudo::type_hint::TypeHintId;

        /// A `when` under construction: the locals held across
        /// its clause loop.
        struct WhenFrame {
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            effective_subject_binder: Option<Binder>,
            clauses: Vec<WhenClause>,
        }

        enum Task {
            /// Take the node apart; queue its children and its own steps.
            Enter(PseudoExpr),
            /// The value is on `done`: mint the binder id and open the
            /// binding, which only the body may see.
            LetBody {
                name: String,
                id: Option<VarId>,
                body: PBox,
            },
            LetPost {
                name: String,
                id: Option<VarId>,
            },
            /// The subject is on `done`: derive the subject binder (minting a
            /// placeholder id here) and queue the clauses left to right.
            WhenClauses {
                subject_name: Option<Binder>,
                clauses: Vec<WhenClause>,
            },
            /// One clause: build and push its scope frame, recover generated
            /// constructor fields into it, then walk guard then body.
            Clause(WhenClause),
            ClauseDone {
                pattern: WhenPattern,
                has_guard: bool,
            },
            WhenPost,
            /// `expect!`: the condition is on `done`, so the payload subject
            /// it names comes into scope for the second argument only.
            ExpectEnv,
            PopEnv,
            /// `expect!` rebuild — its function was walked LAST.
            ExpectPost,
            Lambda {
                params: Vec<Binder>,
            },
            RecFn {
                name: Binder,
                params: Vec<Binder>,
            },
            Apply {
                argc: usize,
            },
            If,
            List {
                count: usize,
                has_tail: bool,
            },
            Tuple {
                count: usize,
            },
            Pair,
            Constr {
                type_hint: Option<TypeHintId>,
                tag: usize,
                count: usize,
                shape: ConstructorShape,
            },
            FieldAccess {
                selector: FieldSelector,
            },
            IndexAccess {
                index: usize,
            },
            BinOp {
                op: BinaryOp,
            },
            UnOp {
                op: UnaryOp,
            },
            BuiltinCall {
                name: BuiltinId,
                argc: usize,
            },
            Delay,
            Force,
            Trace,
        }

        fn take(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
            let at = done.len() - n;
            done.split_off(at)
        }

        /// The `Var` arm verbatim, lifted out only so its early returns still
        /// read as early returns from inside the machine.
        fn rewrite_var(
            name: String,
            id: Option<VarId>,
            env: &ValidatorEnv,
            scopes: &[ScopeFrame],
        ) -> PseudoExpr {
            if is_bound(scopes, &name) {
                return PseudoExpr::Var { name, id };
            }

            if let Some(script_context) = &env.script_context {
                let field = match name.as_str() {
                    "inputs" => Some("inputs"),
                    "reference_inputs" => Some("reference_inputs"),
                    "outputs" => Some("outputs"),
                    "fee" => Some("fee"),
                    "mint" | "mint_" => Some("mint"),
                    "certificates" => Some("certificates"),
                    "withdrawals" => Some("withdrawals"),
                    "valid_range" => Some("valid_range"),
                    "signatories" => Some("signatories"),
                    "redeemers" => Some("redeemers"),
                    "data" => Some("data"),
                    "id" | "transaction_id" => Some("transaction_id"),
                    _ => None,
                };
                if let Some(field) = field {
                    return script_context_field_expr(script_context, field);
                }
            }

            if let Some(redeemer) = &env.redeemer
                && let Some(index) = name
                    .strip_prefix("redeemer_fields_")
                    .and_then(|suffix| suffix.parse::<usize>().ok())
            {
                return redeemer_field_expr(redeemer, index);
            }

            if let Some(index) = name
                .strip_prefix("fields_")
                .and_then(|suffix| suffix.parse::<usize>().ok())
                && let Some(list_head) = nearest_list_head(scopes)
            {
                return field_binder_expr(list_head, index);
            }

            if let Some(index) = name
                .strip_prefix("fields_")
                .and_then(|suffix| suffix.parse::<usize>().ok())
                && let Some(subject) = env.expect_payload_subjects.last()
            {
                return field_binder_expr(subject, index);
            }

            if let Some(index) = generated_field_index(&name) {
                if let Some(binder) = nearest_constructor_field(scopes, index) {
                    return PseudoExpr::var_with_id(binder.name.clone(), binder.id);
                }
                if let Some(subject) = nearest_constructor_subject(scopes) {
                    return field_binder_expr(subject, index);
                }
            }

            PseudoExpr::Var { name, id }
        }

        let mut tasks: Vec<Task> = vec![Task::Enter(expr)];
        let mut done: Vec<PseudoExpr> = Vec::new();
        // The env is a stack because `expect!` extends it for one child only.
        let mut envs: Vec<ValidatorEnv> = vec![env.clone()];
        let mut when_frames: Vec<WhenFrame> = Vec::new();

        while let Some(task) = tasks.pop() {
            match task {
                Task::Enter(expr) => match expr {
                    PseudoExpr::Var { name, id } => {
                        let rewritten =
                            rewrite_var(name, id, envs.last().expect("validator env"), scopes);
                        done.push(rewritten);
                    }
                    PseudoExpr::Lambda { params, body } => {
                        scopes.push(ScopeFrame {
                            bound: params.iter().map(|binder| binder.name.clone()).collect(),
                            binders: params.clone(),
                            list_head: None,
                            constructor_subject: None,
                            constructor_fields: Vec::new(),
                        });
                        tasks.push(Task::Lambda { params });
                        tasks.push(Task::Enter(body.into_inner()));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let mut scope = HashSet::from([name.name.clone()]);
                        scope.extend(params.iter().map(|binder| binder.name.clone()));
                        scopes.push(ScopeFrame {
                            bound: scope,
                            binders: std::iter::once(name.clone())
                                .chain(params.iter().cloned())
                                .collect(),
                            list_head: None,
                            constructor_subject: None,
                            constructor_fields: Vec::new(),
                        });
                        tasks.push(Task::RecFn { name, params });
                        tasks.push(Task::Enter(body.into_inner()));
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        tasks.push(Task::LetBody { name, id, body });
                        tasks.push(Task::Enter(value.into_inner()));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        tasks.push(Task::WhenClauses {
                            subject_name,
                            clauses,
                        });
                        tasks.push(Task::Enter(subject.into_inner()));
                    }
                    PseudoExpr::Apply { function, args } => {
                        if matches!(&*function, PseudoExpr::Var { name, .. } if name == "expect!")
                            && args.len() == 2
                        {
                            let mut args = args.into_iter();
                            let condition = args.next().expect("expect! condition");
                            let payload = args.next().expect("expect! body");
                            // Order: condition, then the body
                            // under the extended env, then the function last.
                            tasks.push(Task::ExpectPost);
                            tasks.push(Task::Enter(function.into_inner()));
                            tasks.push(Task::PopEnv);
                            tasks.push(Task::Enter(payload));
                            tasks.push(Task::ExpectEnv);
                            tasks.push(Task::Enter(condition));
                        } else {
                            tasks.push(Task::Apply { argc: args.len() });
                            for arg in args.into_iter().rev() {
                                tasks.push(Task::Enter(arg));
                            }
                            tasks.push(Task::Enter(function.into_inner()));
                        }
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        tasks.push(Task::If);
                        tasks.push(Task::Enter(else_branch.into_inner()));
                        tasks.push(Task::Enter(then_branch.into_inner()));
                        tasks.push(Task::Enter(condition.into_inner()));
                    }
                    PseudoExpr::List { elements, tail } => {
                        tasks.push(Task::List {
                            count: elements.len(),
                            has_tail: tail.is_some(),
                        });
                        if let Some(tail) = tail {
                            tasks.push(Task::Enter(tail.into_inner()));
                        }
                        for element in elements.into_iter().rev() {
                            tasks.push(Task::Enter(element));
                        }
                    }
                    PseudoExpr::Tuple(elements) => {
                        tasks.push(Task::Tuple {
                            count: elements.len(),
                        });
                        for element in elements.into_iter().rev() {
                            tasks.push(Task::Enter(element));
                        }
                    }
                    PseudoExpr::Pair(left, right) => {
                        tasks.push(Task::Pair);
                        tasks.push(Task::Enter(right.into_inner()));
                        tasks.push(Task::Enter(left.into_inner()));
                    }
                    PseudoExpr::Constr {
                        type_hint,
                        tag,
                        fields,
                        shape,
                    } => {
                        tasks.push(Task::Constr {
                            type_hint,
                            tag,
                            count: fields.len(),
                            shape,
                        });
                        for field in fields.into_iter().rev() {
                            tasks.push(Task::Enter(field));
                        }
                    }
                    PseudoExpr::FieldAccess {
                        record, selector, ..
                    } => {
                        tasks.push(Task::FieldAccess { selector });
                        tasks.push(Task::Enter(record.into_inner()));
                    }
                    PseudoExpr::IndexAccess { collection, index } => {
                        tasks.push(Task::IndexAccess { index });
                        tasks.push(Task::Enter(collection.into_inner()));
                    }
                    PseudoExpr::BinOp { op, left, right } => {
                        tasks.push(Task::BinOp { op });
                        tasks.push(Task::Enter(right.into_inner()));
                        tasks.push(Task::Enter(left.into_inner()));
                    }
                    PseudoExpr::UnOp { op, operand } => {
                        tasks.push(Task::UnOp { op });
                        tasks.push(Task::Enter(operand.into_inner()));
                    }
                    PseudoExpr::BuiltinCall { name, args } => {
                        tasks.push(Task::BuiltinCall {
                            name,
                            argc: args.len(),
                        });
                        for arg in args.into_iter().rev() {
                            tasks.push(Task::Enter(arg));
                        }
                    }
                    PseudoExpr::Delay(inner) => {
                        tasks.push(Task::Delay);
                        tasks.push(Task::Enter(inner.into_inner()));
                    }
                    PseudoExpr::Force(inner) => {
                        tasks.push(Task::Force);
                        tasks.push(Task::Enter(inner.into_inner()));
                    }
                    PseudoExpr::Trace { message, value } => {
                        tasks.push(Task::Trace);
                        tasks.push(Task::Enter(value.into_inner()));
                        tasks.push(Task::Enter(message.into_inner()));
                    }
                    other => done.push(other),
                },
                Task::LetBody { name, id, body } => {
                    let binder_id = id.unwrap_or_else(VarId::fresh_compat_placeholder);
                    scopes.push(ScopeFrame {
                        bound: HashSet::from([name.clone()]),
                        binders: vec![Binder::new(name.clone(), binder_id)],
                        list_head: None,
                        constructor_subject: None,
                        constructor_fields: Vec::new(),
                    });
                    tasks.push(Task::LetPost { name, id });
                    tasks.push(Task::Enter(body.into_inner()));
                }
                Task::LetPost { name, id } => {
                    let body = done.pop().expect("let body");
                    let value = done.pop().expect("let value");
                    scopes.pop();
                    done.push(PseudoExpr::Let {
                        name,
                        id,
                        value: PBox::new(value),
                        body: PBox::new(body),
                    });
                }
                Task::WhenClauses {
                    subject_name,
                    clauses,
                } => {
                    let subject = done.pop().expect("when subject");
                    let effective_subject_binder =
                        subject_name.clone().or_else(|| match &subject {
                            PseudoExpr::Var { name, id, .. } => Some(Binder::new(
                                name.clone(),
                                id.unwrap_or_else(VarId::fresh_compat_placeholder),
                            )),
                            _ => None,
                        });
                    when_frames.push(WhenFrame {
                        subject,
                        subject_name,
                        effective_subject_binder,
                        clauses: Vec::new(),
                    });
                    tasks.push(Task::WhenPost);
                    for clause in clauses.into_iter().rev() {
                        tasks.push(Task::Clause(clause));
                    }
                }
                Task::Clause(clause) => {
                    let frame = when_frames.last().expect("when frame");
                    let effective_subject_binder = frame.effective_subject_binder.clone();

                    let mut bound = HashSet::new();
                    if let Some(subject_name) = &effective_subject_binder
                        && subject_name.name != "_"
                    {
                        bound.insert(subject_name.name.clone());
                    }
                    let mut pattern_names = Vec::new();
                    collect_pattern_binders(&clause.pattern, &mut pattern_names);
                    for name in pattern_names {
                        bound.insert(name);
                    }
                    let list_head = list_pattern_head(&clause.pattern);
                    let mut binders = Vec::new();
                    if let Some(subject_name) = &effective_subject_binder {
                        binders.push(subject_name.clone());
                    }
                    let subject_supports_fields =
                        subject_supports_data_fields(&frame.subject, None);
                    let (constructor_subject, constructor_fields) = if subject_supports_fields {
                        match &clause.pattern {
                            WhenPattern::Constructor { fields, .. } => {
                                (effective_subject_binder.clone(), fields.clone())
                            }
                            _ => (None, Vec::new()),
                        }
                    } else {
                        (None, Vec::new())
                    };
                    match &clause.pattern {
                        WhenPattern::Constructor { fields, .. } => {
                            binders.extend(fields.iter().cloned());
                        }
                        WhenPattern::List { elements, tail } => {
                            binders.extend(elements.iter().cloned());
                            if let Some(tail) = tail {
                                binders.push(tail.clone());
                            }
                        }
                        WhenPattern::Tuple(elements) => binders.extend(elements.iter().cloned()),
                        WhenPattern::Pair(left, right) => {
                            binders.push(left.clone());
                            binders.push(right.clone());
                        }
                        WhenPattern::Var(binder) => binders.push(binder.clone()),
                        WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
                    }
                    scopes.push(ScopeFrame {
                        bound,
                        binders,
                        list_head,
                        constructor_subject,
                        constructor_fields,
                    });
                    let (pattern, clause_body) = try_recover_generated_constructor_fields(
                        clause.pattern,
                        effective_subject_binder.as_ref(),
                        subject_supports_fields,
                        clause.body,
                        scopes,
                        kind_annotations,
                        use_varkind_recovery,
                    );
                    if let Some(scope) = scopes.last_mut()
                        && subject_supports_fields
                        && let WhenPattern::Constructor { fields, .. } = &pattern
                    {
                        scope.constructor_subject = effective_subject_binder.clone();
                        scope.constructor_fields = fields.clone();
                        for field in fields {
                            if field.name != "_" {
                                scope.bound.insert(field.name.clone());
                            }
                            if !scope.binders.iter().any(|binder| binder.id == field.id) {
                                scope.binders.push(field.clone());
                            }
                        }
                    }
                    let has_guard = clause.guard.is_some();
                    tasks.push(Task::ClauseDone { pattern, has_guard });
                    tasks.push(Task::Enter(clause_body));
                    if let Some(guard) = clause.guard {
                        tasks.push(Task::Enter(guard));
                    }
                }
                Task::ClauseDone { pattern, has_guard } => {
                    let body = done.pop().expect("clause body");
                    let guard = has_guard.then(|| done.pop().expect("clause guard"));
                    scopes.pop();
                    when_frames
                        .last_mut()
                        .expect("when frame")
                        .clauses
                        .push(WhenClause {
                            pattern,
                            guard,
                            body,
                        });
                }
                Task::WhenPost => {
                    let frame = when_frames.pop().expect("when frame");
                    done.push(PseudoExpr::When {
                        subject: PBox::new(frame.subject),
                        subject_name: frame.subject_name,
                        clauses: frame.clauses,
                    });
                }
                Task::ExpectEnv => {
                    let condition = done.last().expect("expect! condition");
                    let mut next_env = envs.last().expect("validator env").clone();
                    if let Some((subject_expr, tag)) = extract_constr_unpack_tag_eq(condition)
                        && tag == 0
                        && subject_supports_data_fields(subject_expr, None)
                        && let PseudoExpr::Var {
                            name: subject_name,
                            id: Some(subject_id),
                        } = subject_expr
                    {
                        let binder = find_subject_binder(scopes, subject_name, Some(*subject_id));
                        next_env.expect_payload_subjects.push(binder);
                    }
                    envs.push(next_env);
                }
                Task::PopEnv => {
                    envs.pop();
                }
                Task::ExpectPost => {
                    let function = done.pop().expect("expect! function");
                    let body = done.pop().expect("expect! body");
                    let condition = done.pop().expect("expect! condition");
                    done.push(PseudoExpr::Apply {
                        function: PBox::new(function),
                        args: vec![condition, body].into(),
                    });
                }
                Task::Lambda { params } => {
                    let body = done.pop().expect("lambda body");
                    scopes.pop();
                    done.push(PseudoExpr::Lambda {
                        params,
                        body: PBox::new(body),
                    });
                }
                Task::RecFn { name, params } => {
                    let body = done.pop().expect("recfn body");
                    scopes.pop();
                    done.push(PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(body),
                    });
                }
                Task::Apply { argc } => {
                    let args = take(&mut done, argc);
                    let function = done.pop().expect("apply function");
                    done.push(PseudoExpr::Apply {
                        function: PBox::new(function),
                        args: args.into(),
                    });
                }
                Task::If => {
                    let else_branch = done.pop().expect("if else");
                    let then_branch = done.pop().expect("if then");
                    let condition = done.pop().expect("if condition");
                    done.push(PseudoExpr::If {
                        condition: PBox::new(condition),
                        then_branch: PBox::new(then_branch),
                        else_branch: PBox::new(else_branch),
                    });
                }
                Task::List { count, has_tail } => {
                    let tail = has_tail.then(|| PBox::new(done.pop().expect("list tail")));
                    let elements = take(&mut done, count);
                    done.push(PseudoExpr::List {
                        elements: elements.into(),
                        tail,
                    });
                }
                Task::Tuple { count } => {
                    let elements = take(&mut done, count);
                    done.push(PseudoExpr::Tuple(elements.into()));
                }
                Task::Pair => {
                    let right = done.pop().expect("pair right");
                    let left = done.pop().expect("pair left");
                    done.push(PseudoExpr::Pair(PBox::new(left), PBox::new(right)));
                }
                Task::Constr {
                    type_hint,
                    tag,
                    count,
                    shape,
                } => {
                    let fields = take(&mut done, count);
                    done.push(PseudoExpr::Constr {
                        type_hint,
                        tag,
                        fields: fields.into(),
                        shape,
                    });
                }
                Task::FieldAccess { selector } => {
                    let record = done.pop().expect("field access record");
                    done.push(PseudoExpr::field_access_typed(record, selector));
                }
                Task::IndexAccess { index } => {
                    let collection = done.pop().expect("index access collection");
                    let recovered = if let PseudoExpr::FieldAccess {
                        record, selector, ..
                    } = &collection
                        && selector.as_pretty_name() == "fields"
                        && let PseudoExpr::Var { name, id, .. } = record.as_ref()
                        && nearest_constructor_subject(scopes)
                            .is_some_and(|subject| binder_matches_var(subject, name, *id))
                        && let Some(binder) = nearest_constructor_field(scopes, index)
                    {
                        Some(PseudoExpr::var_with_id(binder.name.clone(), binder.id))
                    } else {
                        None
                    };
                    match recovered {
                        Some(expr) => done.push(expr),
                        None => done.push(PseudoExpr::IndexAccess {
                            collection: PBox::new(collection),
                            index,
                        }),
                    }
                }
                Task::BinOp { op } => {
                    let right = done.pop().expect("binop right");
                    let left = done.pop().expect("binop left");
                    done.push(PseudoExpr::BinOp {
                        op,
                        left: PBox::new(left),
                        right: PBox::new(right),
                    });
                }
                Task::UnOp { op } => {
                    let operand = done.pop().expect("unop operand");
                    done.push(PseudoExpr::UnOp {
                        op,
                        operand: PBox::new(operand),
                    });
                }
                Task::BuiltinCall { name, argc } => {
                    let args = take(&mut done, argc);
                    done.push(PseudoExpr::BuiltinCall {
                        name,
                        args: args.into(),
                    });
                }
                Task::Delay => {
                    let inner = done.pop().expect("delay inner");
                    done.push(PseudoExpr::Delay(PBox::new(inner)));
                }
                Task::Force => {
                    let inner = done.pop().expect("force inner");
                    done.push(PseudoExpr::Force(PBox::new(inner)));
                }
                Task::Trace => {
                    let value = done.pop().expect("trace value");
                    let message = done.pop().expect("trace message");
                    done.push(PseudoExpr::Trace {
                        message: PBox::new(message),
                        value: PBox::new(value),
                    });
                }
            }
        }

        debug_assert_eq!(done.len(), 1, "the rewrite machine must leave one result");
        done.pop().expect("rewrite result")
    }

    let env = infer_root_validator_env(&expr);
    rewrite(
        expr,
        &env,
        &mut Vec::new(),
        kind_annotations,
        use_varkind_recovery,
    )
}

pub(crate) fn rename_option_like_patterns(
    expr: PseudoExpr,
    options: &DecompileOptions,
    kind_annotations: &std::collections::HashMap<
        crate::pseudo::var_id::VarId,
        crate::pseudo::nameless::VarKind,
    >,
) -> PseudoExpr {
    fn extract_expect_some_payload_subject_and_binder(
        expr: &PseudoExpr,
    ) -> Option<(crate::pseudo::var_id::VarId, Binder)> {
        let PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } = expr
        else {
            return None;
        };

        let subject_id = subject_name
            .as_ref()
            .and_then(|binder| binder.id.get())
            .or_else(|| match subject.as_ref() {
                PseudoExpr::Var { id, .. } => id.get(),
                _ => None,
            })?;

        let mut payload_binder = None;
        for clause in clauses {
            if clause.guard.is_some() {
                return None;
            }
            if matches!(clause.body, PseudoExpr::Error { .. }) {
                continue;
            }
            if payload_binder.is_some() {
                return None;
            }
            let WhenPattern::Constructor {
                tag: 0,
                fields,
                shape,
                ..
            } = &clause.pattern
            else {
                return None;
            };
            let is_some = matches!(shape, ConstructorShape::Known(KnownConstructor::Some));
            if !is_some || fields.len() != 1 || fields[0].name == "_" {
                return None;
            }
            payload_binder = Some(fields[0].clone());
        }

        payload_binder.map(|binder| (subject_id, binder))
    }

    fn rewrite(
        expr: PseudoExpr,
        option_like_functions: &HashSet<String>,
        option_like_vars: &mut Vec<HashSet<String>>,
    ) -> PseudoExpr {
        use crate::builtins::BuiltinId;
        use crate::pseudo::ast::{BinaryOp, UnaryOp, WhenClause};
        use crate::pseudo::field_selector::FieldSelector;

        /// A `when` under construction: the locals held across
        /// its clause loop.
        struct WhenFrame {
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            option_like_subject: bool,
            option_like_subject_id: Option<VarId>,
            clauses: Vec<WhenClause>,
        }

        enum Task {
            /// Take the node apart; queue its children and its own steps.
            Enter(PseudoExpr),
            /// The value is on `done`: decide whether it makes the binding
            /// option-like and open that scope, which only the body sees.
            LetBody {
                name: String,
                id: Option<VarId>,
                body: PBox,
            },
            LetPost {
                name: String,
                id: Option<VarId>,
            },
            /// The subject is on `done`: classify it once, then run the
            /// clauses left to right.
            WhenClauses {
                subject_name: Option<Binder>,
                clauses: Vec<WhenClause>,
            },
            /// One clause: rename its pattern (before its body is walked),
            /// then walk the body.
            Clause(WhenClause),
            /// The body is on `done`: apply the `None`-arm fix, then walk the
            /// guard — walked AFTER the body.
            ClauseGuard {
                pattern: WhenPattern,
                guard: Option<PseudoExpr>,
            },
            ClauseDone {
                pattern: WhenPattern,
                body: PseudoExpr,
                has_guard: bool,
            },
            WhenPost,
            If,
            Apply {
                argc: usize,
            },
            Lambda {
                params: Vec<Binder>,
            },
            RecFn {
                name: Binder,
                params: Vec<Binder>,
            },
            Trace,
            Delay,
            Force,
            BuiltinCall {
                name: BuiltinId,
                argc: usize,
            },
            List {
                count: usize,
                has_tail: bool,
            },
            Tuple {
                count: usize,
            },
            Pair,
            FieldAccess {
                selector: FieldSelector,
            },
            IndexAccess {
                index: usize,
            },
            BinOp {
                op: BinaryOp,
            },
            UnOp {
                op: UnaryOp,
            },
        }

        fn take(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
            let at = done.len() - n;
            done.split_off(at)
        }

        let mut tasks: Vec<Task> = vec![Task::Enter(expr)];
        let mut done: Vec<PseudoExpr> = Vec::new();
        let mut when_frames: Vec<WhenFrame> = Vec::new();

        while let Some(task) = tasks.pop() {
            match task {
                Task::Enter(expr) => match expr {
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        tasks.push(Task::LetBody { name, id, body });
                        tasks.push(Task::Enter(value.into_inner()));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        tasks.push(Task::WhenClauses {
                            subject_name,
                            clauses,
                        });
                        tasks.push(Task::Enter(subject.into_inner()));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        tasks.push(Task::If);
                        tasks.push(Task::Enter(else_branch.into_inner()));
                        tasks.push(Task::Enter(then_branch.into_inner()));
                        tasks.push(Task::Enter(condition.into_inner()));
                    }
                    PseudoExpr::Apply { function, args } => {
                        tasks.push(Task::Apply { argc: args.len() });
                        for arg in args.into_iter().rev() {
                            tasks.push(Task::Enter(arg));
                        }
                        tasks.push(Task::Enter(function.into_inner()));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        tasks.push(Task::Lambda { params });
                        tasks.push(Task::Enter(body.into_inner()));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        tasks.push(Task::RecFn { name, params });
                        tasks.push(Task::Enter(body.into_inner()));
                    }
                    PseudoExpr::Trace { message, value } => {
                        tasks.push(Task::Trace);
                        tasks.push(Task::Enter(value.into_inner()));
                        tasks.push(Task::Enter(message.into_inner()));
                    }
                    PseudoExpr::Delay(inner) => {
                        tasks.push(Task::Delay);
                        tasks.push(Task::Enter(inner.into_inner()));
                    }
                    PseudoExpr::Force(inner) => {
                        tasks.push(Task::Force);
                        tasks.push(Task::Enter(inner.into_inner()));
                    }
                    PseudoExpr::BuiltinCall { name, args } => {
                        tasks.push(Task::BuiltinCall {
                            name,
                            argc: args.len(),
                        });
                        for arg in args.into_iter().rev() {
                            tasks.push(Task::Enter(arg));
                        }
                    }
                    PseudoExpr::List { elements, tail } => {
                        tasks.push(Task::List {
                            count: elements.len(),
                            has_tail: tail.is_some(),
                        });
                        if let Some(tail) = tail {
                            tasks.push(Task::Enter(tail.into_inner()));
                        }
                        for element in elements.into_iter().rev() {
                            tasks.push(Task::Enter(element));
                        }
                    }
                    PseudoExpr::Tuple(elements) => {
                        tasks.push(Task::Tuple {
                            count: elements.len(),
                        });
                        for element in elements.into_iter().rev() {
                            tasks.push(Task::Enter(element));
                        }
                    }
                    PseudoExpr::Pair(first, second) => {
                        tasks.push(Task::Pair);
                        tasks.push(Task::Enter(second.into_inner()));
                        tasks.push(Task::Enter(first.into_inner()));
                    }
                    PseudoExpr::FieldAccess {
                        record, selector, ..
                    } => {
                        tasks.push(Task::FieldAccess { selector });
                        tasks.push(Task::Enter(record.into_inner()));
                    }
                    PseudoExpr::IndexAccess { collection, index } => {
                        tasks.push(Task::IndexAccess { index });
                        tasks.push(Task::Enter(collection.into_inner()));
                    }
                    PseudoExpr::BinOp { op, left, right } => {
                        tasks.push(Task::BinOp { op });
                        tasks.push(Task::Enter(right.into_inner()));
                        tasks.push(Task::Enter(left.into_inner()));
                    }
                    PseudoExpr::UnOp { op, operand } => {
                        tasks.push(Task::UnOp { op });
                        tasks.push(Task::Enter(operand.into_inner()));
                    }
                    other => done.push(other),
                },
                Task::LetBody { name, id, body } => {
                    let value = done.last().expect("let value");
                    let mut scope = HashSet::new();
                    if is_option_like_value(value, option_like_functions, option_like_vars) {
                        scope.insert(name.clone());
                    }
                    option_like_vars.push(scope);
                    tasks.push(Task::LetPost { name, id });
                    tasks.push(Task::Enter(body.into_inner()));
                }
                Task::LetPost { name, id } => {
                    let body = done.pop().expect("let body");
                    let value = done.pop().expect("let value");
                    option_like_vars.pop();
                    done.push(PseudoExpr::Let {
                        name,
                        id,
                        value: PBox::new(value),
                        body: PBox::new(body),
                    });
                }
                Task::WhenClauses {
                    subject_name,
                    clauses,
                } => {
                    let subject = done.pop().expect("when subject");
                    let option_like_subject =
                        is_option_like_value(&subject, option_like_functions, option_like_vars);
                    let option_like_subject_id: Option<VarId> = subject_name
                        .as_ref()
                        .and_then(|binder| binder.id.get())
                        .or(match &subject {
                            PseudoExpr::Var { id, .. } => id.get(),
                            _ => None,
                        });
                    when_frames.push(WhenFrame {
                        subject,
                        subject_name,
                        option_like_subject,
                        option_like_subject_id,
                        clauses: Vec::new(),
                    });
                    tasks.push(Task::WhenPost);
                    for clause in clauses.into_iter().rev() {
                        tasks.push(Task::Clause(clause));
                    }
                }
                Task::Clause(clause) => {
                    let option_like_subject =
                        when_frames.last().expect("when frame").option_like_subject;
                    let pattern = if option_like_subject {
                        rename_option_pattern(clause.pattern)
                    } else {
                        clause.pattern
                    };
                    tasks.push(Task::ClauseGuard {
                        pattern,
                        guard: clause.guard,
                    });
                    tasks.push(Task::Enter(clause.body));
                }
                Task::ClauseGuard { pattern, guard } => {
                    let mut body = done.pop().expect("clause body");
                    let option_like_subject =
                        when_frames.last().expect("when frame").option_like_subject;
                    if option_like_subject
                        && matches!(
                            &pattern,
                            WhenPattern::Constructor {
                                tag: 1,
                                fields,
                                shape,
                                ..
                            } if matches!(shape, ConstructorShape::Known(KnownConstructor::None))
                                && fields.is_empty()
                        )
                        && is_bool_false_like(&body)
                    {
                        body = make_standard_option_none();
                    }
                    let has_guard = guard.is_some();
                    tasks.push(Task::ClauseDone {
                        pattern,
                        body,
                        has_guard,
                    });
                    if let Some(guard) = guard {
                        tasks.push(Task::Enter(guard));
                    }
                }
                Task::ClauseDone {
                    pattern,
                    mut body,
                    has_guard,
                } => {
                    let mut guard = has_guard.then(|| done.pop().expect("clause guard"));
                    let frame = when_frames.last().expect("when frame");
                    let option_like_subject = frame.option_like_subject;
                    let option_like_subject_id = frame.option_like_subject_id;
                    if option_like_subject
                        && let (
                            Some(subject_id),
                            WhenPattern::Constructor {
                                tag: 0,
                                fields,
                                shape,
                                ..
                            },
                        ) = (option_like_subject_id, &pattern)
                    {
                        let is_some =
                            matches!(shape, ConstructorShape::Known(KnownConstructor::Some));
                        if is_some && fields.len() == 1 && fields[0].name != "_" {
                            let (rewritten_body, _) =
                                replace_subject_payload_access(body, Some(subject_id), &fields[0]);
                            body = rewritten_body;
                            if let Some(guard_expr) = guard.take() {
                                let (rewritten_guard, _) = replace_subject_payload_access(
                                    guard_expr,
                                    Some(subject_id),
                                    &fields[0],
                                );
                                guard = Some(rewritten_guard);
                            }
                        }
                    }
                    when_frames
                        .last_mut()
                        .expect("when frame")
                        .clauses
                        .push(WhenClause {
                            pattern,
                            guard,
                            body,
                        });
                }
                Task::WhenPost => {
                    let frame = when_frames.pop().expect("when frame");
                    let mut clauses = frame.clauses;
                    if frame.option_like_subject {
                        fill_option_wildcard_pattern(&mut clauses);
                    }
                    done.push(PseudoExpr::When {
                        subject: PBox::new(frame.subject),
                        subject_name: frame.subject_name,
                        clauses,
                    });
                }
                Task::If => {
                    let else_branch = done.pop().expect("if else");
                    let then_branch = done.pop().expect("if then");
                    let condition = done.pop().expect("if condition");
                    done.push(PseudoExpr::If {
                        condition: PBox::new(condition),
                        then_branch: PBox::new(then_branch),
                        else_branch: PBox::new(else_branch),
                    });
                }
                Task::Apply { argc } => {
                    let mut args = take(&mut done, argc);
                    let function = done.pop().expect("apply function");
                    if matches!(&function, PseudoExpr::Var { name, .. } if name == "expect!")
                        && args.len() == 2
                        && let Some((subject_id, binder)) =
                            extract_expect_some_payload_subject_and_binder(&args[0])
                    {
                        let (rewritten_body, changed) = replace_subject_payload_access(
                            args[1].clone(),
                            Some(subject_id),
                            &binder,
                        );
                        if changed {
                            args[1] = rewritten_body;
                        }
                    }
                    done.push(PseudoExpr::Apply {
                        function: PBox::new(function),
                        args: args.into(),
                    });
                }
                Task::Lambda { params } => {
                    let body = done.pop().expect("lambda body");
                    done.push(PseudoExpr::Lambda {
                        params,
                        body: PBox::new(body),
                    });
                }
                Task::RecFn { name, params } => {
                    let body = done.pop().expect("recfn body");
                    done.push(PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(body),
                    });
                }
                Task::Trace => {
                    let value = done.pop().expect("trace value");
                    let message = done.pop().expect("trace message");
                    done.push(PseudoExpr::Trace {
                        message: PBox::new(message),
                        value: PBox::new(value),
                    });
                }
                Task::Delay => {
                    let inner = done.pop().expect("delay inner");
                    done.push(PseudoExpr::Delay(PBox::new(inner)));
                }
                Task::Force => {
                    let inner = done.pop().expect("force inner");
                    done.push(PseudoExpr::Force(PBox::new(inner)));
                }
                Task::BuiltinCall { name, argc } => {
                    let args = take(&mut done, argc);
                    done.push(PseudoExpr::BuiltinCall {
                        name,
                        args: args.into(),
                    });
                }
                Task::List { count, has_tail } => {
                    let tail = has_tail.then(|| PBox::new(done.pop().expect("list tail")));
                    let elements = take(&mut done, count);
                    done.push(PseudoExpr::List {
                        elements: elements.into(),
                        tail,
                    });
                }
                Task::Tuple { count } => {
                    let elements = take(&mut done, count);
                    done.push(PseudoExpr::Tuple(elements.into()));
                }
                Task::Pair => {
                    let second = done.pop().expect("pair second");
                    let first = done.pop().expect("pair first");
                    done.push(PseudoExpr::Pair(PBox::new(first), PBox::new(second)));
                }
                Task::FieldAccess { selector } => {
                    let record = done.pop().expect("field access record");
                    done.push(PseudoExpr::field_access_typed(record, selector));
                }
                Task::IndexAccess { index } => {
                    let collection = done.pop().expect("index access collection");
                    done.push(PseudoExpr::IndexAccess {
                        collection: PBox::new(collection),
                        index,
                    });
                }
                Task::BinOp { op } => {
                    let right = done.pop().expect("binop right");
                    let left = done.pop().expect("binop left");
                    done.push(PseudoExpr::BinOp {
                        op,
                        left: PBox::new(left),
                        right: PBox::new(right),
                    });
                }
                Task::UnOp { op } => {
                    let operand = done.pop().expect("unop operand");
                    done.push(PseudoExpr::UnOp {
                        op,
                        operand: PBox::new(operand),
                    });
                }
            }
        }

        debug_assert_eq!(done.len(), 1, "the rewrite machine must leave one result");
        done.pop().expect("rewrite result")
    }

    let mut option_like_functions = HashSet::new();
    collect_option_like_function_names(&expr, &mut option_like_functions);
    let expr = rewrite(expr, &option_like_functions, &mut Vec::new());
    recover_missing_option_payload_binders(expr, kind_annotations, options.use_varkind_recovery)
}

#[cfg(test)]
mod tests;
