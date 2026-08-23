use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, WhenClause};
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

use super::super::super::super::Simplifier;
use super::projections::{RootStep, simplify_field_access_root, simplify_index_access_root};
use super::{count_var_usages, expr_binds_name, strip_force_on_var};

fn alias_substitution_would_capture(body: &PseudoExpr, aliased: &str) -> bool {
    expr_binds_name(body, aliased)
}

fn ref_matches_binding(
    ref_name: &str,
    ref_id: &Option<VarId>,
    binding_name: &str,
    binding_id: Option<VarId>,
) -> bool {
    crate::decompile::var_match::refs_match(ref_name, ref_id.get(), binding_name, binding_id.get())
}

pub(super) fn normalize_cancel_root(mut expr: PseudoExpr) -> PseudoExpr {
    loop {
        match expr {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                if let PseudoExpr::Delay(inner) = value.as_ref() {
                    let binding_id = id.get();
                    let (force_uses, total_uses) = count_var_usages(&body, &name, binding_id);
                    if total_uses > 0 && force_uses == total_uses {
                        let stripped_body =
                            strip_force_on_var(body.into_inner(), &name, binding_id);
                        let new_value = inner.as_ref().clone();

                        if let PseudoExpr::Var {
                            name: aliased,
                            id: alias_id,
                        } = &new_value
                            && !alias_substitution_would_capture(&stripped_body, aliased)
                        {
                            // substitute both name AND VarId so body refs end up
                            // bound by the aliased binder, not a dangling ref to the removed let.
                            expr = Simplifier::substitute_var_for_var(
                                &stripped_body,
                                &name,
                                id.get(),
                                aliased,
                                alias_id.unwrap_or_else(VarId::fresh_compat_placeholder),
                            );
                            continue;
                        }

                        if let PseudoExpr::Var {
                            name: body_var,
                            id: body_id,
                            ..
                        } = &stripped_body
                            && ref_matches_binding(body_var, body_id, &name, id)
                        {
                            expr = new_value;
                            continue;
                        }

                        if !Simplifier::is_var_used(&stripped_body, &name) {
                            expr = stripped_body;
                            continue;
                        }

                        expr = PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(new_value),
                            body: PBox::new(stripped_body),
                        };
                        continue;
                    }
                }

                // Collapse identity value lets inside binding values:
                // Let x = (let y = e in y) in body -> let x = e in body
                if let PseudoExpr::Let {
                    name: inner_name,
                    value: inner_value,
                    body: inner_body,
                    id: inner_id,
                } = value.as_ref()
                    && let PseudoExpr::Var {
                        name: inner_body_var,
                        id: inner_body_id,
                        ..
                    } = inner_body.as_ref()
                    && ref_matches_binding(inner_body_var, inner_body_id, inner_name, *inner_id)
                {
                    expr = PseudoExpr::Let {
                        name,
                        id,
                        value: inner_value.clone(),
                        body,
                    };
                    continue;
                }

                // Generic alias collapse:
                // Let x = y in body -> body[x := y]
                if let PseudoExpr::Var {
                    name: aliased,
                    id: alias_id,
                } = value.as_ref()
                    && aliased != &name
                    && !alias_substitution_would_capture(body.as_ref(), aliased)
                {
                    // substitute VarId too.
                    expr = Simplifier::substitute_var_for_var(
                        body.as_ref(),
                        &name,
                        id.get(),
                        aliased,
                        alias_id.unwrap_or_else(VarId::fresh_compat_placeholder),
                    );
                    continue;
                }

                // Trivial let inlining:
                // Let x = e in x -> e
                if let PseudoExpr::Var {
                    name: body_var,
                    id: body_id,
                    ..
                } = body.as_ref()
                    && ref_matches_binding(body_var, body_id, &name, id)
                {
                    expr = value.as_ref().clone();
                    continue;
                }

                return PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                };
            }
            PseudoExpr::Force(inner) => {
                let inner = inner.into_inner();

                if let PseudoExpr::Delay(body) = inner {
                    expr = body.into_inner();
                    continue;
                }

                if let PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } = inner
                {
                    expr = PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body: PBox::new(PseudoExpr::Force(body)),
                    };
                    continue;
                }

                if let PseudoExpr::Trace { message, value } = inner {
                    expr = PseudoExpr::Trace {
                        message,
                        value: PBox::new(PseudoExpr::Force(value)),
                    };
                    continue;
                }

                if let PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } = inner
                {
                    let clauses = clauses
                        .into_iter()
                        .map(|c| {
                            let body = if let PseudoExpr::Delay(inner) = c.body {
                                inner.into_inner()
                            } else {
                                c.body
                            };
                            WhenClause {
                                pattern: c.pattern,
                                guard: c.guard,
                                body,
                            }
                        })
                        .collect();
                    return PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    };
                }

                if matches!(
                    &inner,
                    PseudoExpr::If { .. }
                        | PseudoExpr::BinOp { .. }
                        | PseudoExpr::Bool(_)
                        | PseudoExpr::Int(_)
                        | PseudoExpr::Unit
                        | PseudoExpr::Constr { .. }
                        | PseudoExpr::Error { .. }
                ) {
                    expr = inner;
                    continue;
                }

                return PseudoExpr::Force(PBox::new(inner));
            }
            PseudoExpr::Apply { function, args } => {
                if let PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } = function.as_ref()
                {
                    expr = PseudoExpr::Let {
                        name: name.clone(),
                        id: *id,
                        value: value.clone(),
                        body: PBox::new(PseudoExpr::Apply {
                            function: body.clone(),
                            args,
                        }),
                    };
                    continue;
                }
                return PseudoExpr::Apply { function, args };
            }
            PseudoExpr::FieldAccess {
                record, selector, ..
            } => match simplify_field_access_root(record.into_inner(), selector) {
                RootStep::Continue(next) => {
                    expr = next;
                    continue;
                }
                RootStep::Return(done) => return done,
            },
            PseudoExpr::IndexAccess { collection, index } => {
                match simplify_index_access_root(collection.into_inner(), index) {
                    RootStep::Continue(next) => {
                        expr = next;
                        continue;
                    }
                    RootStep::Return(done) => return done,
                }
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                return PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                };
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                return PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                };
            }
            PseudoExpr::Lambda { params, body } => {
                return PseudoExpr::Lambda { params, body };
            }
            PseudoExpr::RecFn { name, params, body } => {
                return PseudoExpr::RecFn { name, params, body };
            }
            PseudoExpr::UnOp { op, operand } => {
                return PseudoExpr::UnOp { op, operand };
            }
            PseudoExpr::BinOp { op, left, right } => {
                return PseudoExpr::BinOp { op, left, right };
            }
            PseudoExpr::BuiltinCall { name, args } => {
                return PseudoExpr::BuiltinCall { name, args };
            }
            PseudoExpr::List { elements, tail } => {
                return PseudoExpr::List { elements, tail };
            }
            PseudoExpr::Constr {
                type_hint,
                tag,
                fields,
                shape,
            } => {
                return PseudoExpr::Constr {
                    type_hint,
                    tag,
                    fields,
                    shape,
                };
            }
            PseudoExpr::Trace { message, value } => {
                return PseudoExpr::Trace { message, value };
            }
            PseudoExpr::Tuple(items) => {
                return PseudoExpr::Tuple(items);
            }
            PseudoExpr::Pair(a, b) => {
                return PseudoExpr::Pair(a, b);
            }
            PseudoExpr::Delay(inner) => {
                return PseudoExpr::Delay(inner);
            }
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Var { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::HelperSymbol(_) => return expr,
        }
    }
}
