use crate::decompile::constructor_data::is_standard_option_none_candidate;
use crate::decompile::helper::hoist::var_is_referenced_id_aware;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, PseudoExpr};
use crate::pseudo::var_id::VarId;

pub(crate) fn try_reorder_inverted_if_arg_lets(
    outer_name: String,
    outer_id: VarId,
    outer_value: PseudoExpr,
    outer_body: PseudoExpr,
) -> Option<PseudoExpr> {
    let PseudoExpr::Let {
        name: inner_name,
        id: Some(inner_id),
        value: inner_value,
        body: inner_body,
    } = outer_value
    else {
        return None;
    };

    if !matches!(inner_value.as_ref(), PseudoExpr::If { .. }) {
        return None;
    }

    if !var_is_referenced_id_aware(inner_value.as_ref(), outer_id, &outer_name)
        || !var_is_referenced_id_aware(inner_value.as_ref(), inner_id, &inner_name)
    {
        return None;
    }

    if var_is_referenced_id_aware(inner_body.as_ref(), outer_id, &outer_name)
        || var_is_referenced_id_aware(inner_body.as_ref(), inner_id, &inner_name)
        || var_is_referenced_id_aware(&outer_body, outer_id, &outer_name)
        || var_is_referenced_id_aware(&outer_body, inner_id, &inner_name)
    {
        return None;
    }

    Some(PseudoExpr::Let {
        name: outer_name,
        id: Some(outer_id),
        value: PBox::new(outer_body),
        body: PBox::new(PseudoExpr::Let {
            name: inner_name,
            id: Some(inner_id),
            value: inner_body,
            body: inner_value,
        }),
    })
}

pub(crate) fn try_repair_self_referenced_let(
    name: String,
    id: VarId,
    value: PseudoExpr,
    body: PseudoExpr,
) -> Option<PseudoExpr> {
    if !var_is_referenced_id_aware(&value, id, &name)
        || var_is_referenced_id_aware(&body, id, &name)
    {
        return None;
    }

    Some(PseudoExpr::Let {
        name,
        id: Some(id),
        value: PBox::new(body),
        body: PBox::new(value),
    })
}

pub(crate) fn try_inline_when_adapter_let(
    let_name: String,
    let_value: PseudoExpr,
    let_body: PseudoExpr,
) -> Option<PseudoExpr> {
    let PseudoExpr::When {
        subject,
        subject_name,
        clauses,
    } = let_value
    else {
        return None;
    };

    if subject_name.is_some() {
        return None;
    }
    let PseudoExpr::Var {
        name: subject_var_name,
        id: subject_var_id,
        ..
    } = subject.as_ref()
    else {
        return None;
    };
    // A `Var` subject may carry `id: None`. Pass a fresh placeholder so
    // `var_is_referenced_id_aware` receives a concrete VarId; that function
    // matches an id-less reference by name on its own.
    let subject_var_id = subject_var_id.unwrap_or_else(VarId::fresh_compat_placeholder);

    let PseudoExpr::Lambda {
        params,
        body: adapter_body,
    } = let_body
    else {
        return None;
    };

    let PseudoExpr::Apply { function, args } = adapter_body.as_ref() else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    let PseudoExpr::Var {
        name: called_name, ..
    } = function.as_ref()
    else {
        return None;
    };
    if called_name != &let_name {
        return None;
    }

    for clause in &clauses {
        if var_is_referenced_id_aware(&clause.body, subject_var_id, subject_var_name) {
            return None;
        }
        if let Some(guard) = &clause.guard
            && var_is_referenced_id_aware(guard, subject_var_id, subject_var_name)
        {
            return None;
        }
    }

    Some(PseudoExpr::Lambda {
        params,
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(args[0].clone()),
            subject_name: None,
            clauses,
        }),
    })
}

pub(crate) fn try_normalize_sorted_assoc_lookup_if(
    condition: PseudoExpr,
    then_branch: PseudoExpr,
    else_branch: PseudoExpr,
) -> Option<PseudoExpr> {
    let (lt_op, left, right) = match &condition {
        PseudoExpr::BinOp { op, left, right } => match op {
            BinaryOp::Lte => (BinaryOp::Lt, left.as_ref(), right.as_ref()),
            BinaryOp::Gte => (BinaryOp::Gt, left.as_ref(), right.as_ref()),
            _ => return None,
        },
        _ => return None,
    };

    let PseudoExpr::If {
        condition: inner_condition,
        then_branch: inner_then,
        else_branch: inner_else,
    } = &then_branch
    else {
        return None;
    };

    if !is_standard_option_none_candidate(inner_else.as_ref()) {
        return None;
    }
    if !matches_same_equality_operands(inner_condition, left, right) {
        return None;
    }

    Some(PseudoExpr::If {
        condition: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(left.clone()),
            right: PBox::new(right.clone()),
        }),
        then_branch: PBox::new((**inner_then).clone()),
        else_branch: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::BinOp {
                op: lt_op,
                left: PBox::new(left.clone()),
                right: PBox::new(right.clone()),
            }),
            then_branch: PBox::new((**inner_else).clone()),
            else_branch: PBox::new(else_branch),
        }),
    })
}

fn matches_same_equality_operands(
    expr: &PseudoExpr,
    left: &PseudoExpr,
    right: &PseudoExpr,
) -> bool {
    matches!(
        expr,
        PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: eq_left,
            right: eq_right,
        } if (eq_left.as_ref().structural_eq(left) && eq_right.as_ref().structural_eq(right))
            || (eq_left.as_ref().structural_eq(right) && eq_right.as_ref().structural_eq(left))
    )
}

#[cfg(test)]
mod tests;
