use crate::decompile::helper::hoist::var_is_referenced_id_aware;
use crate::decompile::mid::type_env::TypeEnvironment;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, PseudoType, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

pub(crate) fn rewrite_boolish_data_ifs(
    expr: PseudoExpr,
    env: Option<&TypeEnvironment>,
) -> PseudoExpr {
    struct BoolishDataIfRewriter<'a> {
        env: Option<&'a TypeEnvironment>,
    }

    fn binder_shadows_field_fallback(
        name: &str,
        id: VarId,
        target_name: &str,
        target_id: VarId,
    ) -> bool {
        id != target_id && name == target_name
    }

    fn opt_binder_shadows_field_fallback(
        name: &str,
        id: Option<VarId>,
        target_name: &str,
        target_id: VarId,
    ) -> bool {
        let concrete = id.unwrap_or_else(VarId::fresh_compat_placeholder);
        binder_shadows_field_fallback(name, concrete, target_name, target_id)
    }

    fn pattern_shadows_field_fallback(
        pattern: &WhenPattern,
        target_name: &str,
        target_id: VarId,
    ) -> bool {
        match pattern {
            WhenPattern::Constructor { fields, .. } => fields.iter().any(|field| {
                binder_shadows_field_fallback(field.as_str(), field.id, target_name, target_id)
            }),
            WhenPattern::List { elements, tail } => {
                elements.iter().any(|element| {
                    binder_shadows_field_fallback(
                        element.as_str(),
                        element.id,
                        target_name,
                        target_id,
                    )
                }) || tail.as_ref().is_some_and(|tail| {
                    binder_shadows_field_fallback(tail.as_str(), tail.id, target_name, target_id)
                })
            }
            WhenPattern::Tuple(fields) => fields.iter().any(|field| {
                binder_shadows_field_fallback(field.as_str(), field.id, target_name, target_id)
            }),
            WhenPattern::Pair(left, right) => {
                binder_shadows_field_fallback(left.as_str(), left.id, target_name, target_id)
                    || binder_shadows_field_fallback(
                        right.as_str(),
                        right.id,
                        target_name,
                        target_id,
                    )
            }
            WhenPattern::Var(binder) => {
                binder_shadows_field_fallback(binder.as_str(), binder.id, target_name, target_id)
            }
            WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
        }
    }

    fn expr_accesses_fields_of(expr: &PseudoExpr, var_name: &str, var_id: VarId) -> bool {
        let mut stack = vec![(expr, false)];

        while let Some((current, fallback_shadowed)) = stack.pop() {
            match current {
                PseudoExpr::FieldAccess {
                    record, selector, ..
                } => {
                    if selector.as_pretty_name() == "fields"
                        && matches!(
                            record.as_ref(),
                            PseudoExpr::Var { name, id, .. }
                                if *id == Some(var_id)
                                    || (!fallback_shadowed
                                        && id.get().is_none()
                                        && name == var_name)
                        )
                    {
                        return true;
                    }
                    stack.push((record.as_ref(), fallback_shadowed));
                }
                PseudoExpr::IndexAccess { collection, .. } => {
                    stack.push((collection.as_ref(), fallback_shadowed));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                    ..
                } => {
                    stack.push((value.as_ref(), fallback_shadowed));
                    let body_shadowed = fallback_shadowed
                        || opt_binder_shadows_field_fallback(name, *id, var_name, var_id);
                    stack.push((body.as_ref(), body_shadowed));
                }
                PseudoExpr::Lambda { params, body } => {
                    let body_shadowed = fallback_shadowed
                        || params.iter().any(|param| {
                            binder_shadows_field_fallback(
                                param.as_str(),
                                param.id,
                                var_name,
                                var_id,
                            )
                        });
                    stack.push((body.as_ref(), body_shadowed));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    let body_shadowed = fallback_shadowed
                        || binder_shadows_field_fallback(name.as_str(), name.id, var_name, var_id)
                        || params.iter().any(|param| {
                            binder_shadows_field_fallback(
                                param.as_str(),
                                param.id,
                                var_name,
                                var_id,
                            )
                        });
                    stack.push((body.as_ref(), body_shadowed));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    stack.push((condition.as_ref(), fallback_shadowed));
                    stack.push((then_branch.as_ref(), fallback_shadowed));
                    stack.push((else_branch.as_ref(), fallback_shadowed));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    stack.push((subject.as_ref(), fallback_shadowed));
                    for clause in clauses {
                        let clause_shadowed = fallback_shadowed
                            || subject_name.as_ref().is_some_and(|subject_name| {
                                binder_shadows_field_fallback(
                                    subject_name.as_str(),
                                    subject_name.id,
                                    var_name,
                                    var_id,
                                )
                            })
                            || pattern_shadows_field_fallback(&clause.pattern, var_name, var_id);
                        if let Some(guard) = &clause.guard {
                            stack.push((guard, clause_shadowed));
                        }
                        stack.push((&clause.body, clause_shadowed));
                        if let WhenPattern::Literal(lit) = &clause.pattern {
                            stack.push((lit, fallback_shadowed));
                        }
                    }
                }
                PseudoExpr::Apply { function, args } => {
                    stack.push((function.as_ref(), fallback_shadowed));
                    for arg in args {
                        stack.push((arg, fallback_shadowed));
                    }
                }
                PseudoExpr::BuiltinCall { args, .. } => {
                    for arg in args {
                        stack.push((arg, fallback_shadowed));
                    }
                }
                PseudoExpr::BinOp { left, right, .. } | PseudoExpr::Pair(left, right) => {
                    stack.push((left.as_ref(), fallback_shadowed));
                    stack.push((right.as_ref(), fallback_shadowed));
                }
                PseudoExpr::UnOp { operand, .. }
                | PseudoExpr::Delay(operand)
                | PseudoExpr::Force(operand) => stack.push((operand.as_ref(), fallback_shadowed)),
                PseudoExpr::Trace { message, value } => {
                    stack.push((message.as_ref(), fallback_shadowed));
                    stack.push((value.as_ref(), fallback_shadowed));
                }
                PseudoExpr::List { elements, tail } => {
                    for element in elements {
                        stack.push((element, fallback_shadowed));
                    }
                    if let Some(tail) = tail {
                        stack.push((tail.as_ref(), fallback_shadowed));
                    }
                }
                PseudoExpr::Tuple(elements)
                | PseudoExpr::Constr {
                    fields: elements, ..
                } => {
                    for element in elements {
                        stack.push((element, fallback_shadowed));
                    }
                }
                PseudoExpr::Int(_)
                | PseudoExpr::Var { .. }
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

    impl ExprFolder for BoolishDataIfRewriter<'_> {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_if(
            &mut self,
            condition: PseudoExpr,
            then_branch: PseudoExpr,
            else_branch: PseudoExpr,
        ) -> PseudoExpr {
            if let PseudoExpr::Var { name, id, .. } = &condition {
                let concrete_id = id.unwrap_or_else(VarId::fresh_compat_placeholder);
                let resolved_type = self.env.and_then(|env| env.type_of_var(concrete_id));
                let is_data_typed = matches!(
                    resolved_type.as_deref(),
                    None | Some(PseudoType::Data | PseudoType::Unknown)
                );
                let uses_fields = expr_accesses_fields_of(&then_branch, name, concrete_id)
                    || expr_accesses_fields_of(&else_branch, name, concrete_id);
                let branch_refs_var = var_is_referenced_id_aware(&then_branch, concrete_id, name)
                    || var_is_referenced_id_aware(&else_branch, concrete_id, name);

                if is_data_typed && (uses_fields || !branch_refs_var) {
                    return PseudoExpr::When {
                        subject: PBox::new(condition),
                        subject_name: None,
                        clauses: vec![
                            WhenClause {
                                pattern: WhenPattern::constructor(
                                    ConstructorShape::unknown_data(1, 0),
                                    vec![],
                                ),
                                guard: None,
                                body: then_branch,
                            },
                            WhenClause {
                                pattern: WhenPattern::Wildcard,
                                guard: None,
                                body: else_branch,
                            },
                        ],
                    };
                }
            }

            PseudoExpr::If {
                condition: PBox::new(condition),
                then_branch: PBox::new(then_branch),
                else_branch: PBox::new(else_branch),
            }
        }
    }

    BoolishDataIfRewriter { env }.fold(expr)
}
