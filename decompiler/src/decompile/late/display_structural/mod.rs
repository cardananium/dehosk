use crate::decompile::constructor_data::is_standard_option_none_candidate;
use crate::decompile::helper::hoist::var_is_referenced_id_aware;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, PseudoExpr};
use crate::pseudo::var_id::VarId;

/// The parts of a `let` a rewrite here hands back untouched when it does not
/// apply: name, value, body.
///
/// The rewrites take a `let` apart by value instead of reading a copy: the
/// body is the rest of a chain as long as the script makes it, so copying it
/// per `let` would cost the square of the chain.
pub(crate) type LetParts = (String, PseudoExpr, PseudoExpr);

pub(crate) fn try_reorder_inverted_if_arg_lets(
    outer_name: String,
    outer_id: VarId,
    outer_value: PseudoExpr,
    outer_body: PseudoExpr,
) -> Result<PseudoExpr, LetParts> {
    let PseudoExpr::Let {
        name: inner_name,
        id: Some(inner_id),
        value: inner_value,
        body: inner_body,
    } = outer_value
    else {
        return Err((outer_name, outer_value, outer_body));
    };

    let applies = matches!(inner_value.as_ref(), PseudoExpr::If { .. })
        && var_is_referenced_id_aware(inner_value.as_ref(), outer_id, &outer_name)
        && var_is_referenced_id_aware(inner_value.as_ref(), inner_id, &inner_name)
        && !(var_is_referenced_id_aware(inner_body.as_ref(), outer_id, &outer_name)
            || var_is_referenced_id_aware(inner_body.as_ref(), inner_id, &inner_name)
            || var_is_referenced_id_aware(&outer_body, outer_id, &outer_name)
            || var_is_referenced_id_aware(&outer_body, inner_id, &inner_name));
    if !applies {
        let outer_value = PseudoExpr::Let {
            name: inner_name,
            id: Some(inner_id),
            value: inner_value,
            body: inner_body,
        };
        return Err((outer_name, outer_value, outer_body));
    }

    Ok(PseudoExpr::Let {
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
) -> Result<PseudoExpr, LetParts> {
    if !var_is_referenced_id_aware(&value, id, &name)
        || var_is_referenced_id_aware(&body, id, &name)
    {
        return Err((name, value, body));
    }

    Ok(PseudoExpr::Let {
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
) -> Result<PseudoExpr, LetParts> {
    if !inlines_when_adapter(&let_name, &let_value, &let_body) {
        return Err((let_name, let_value, let_body));
    }
    let (
        PseudoExpr::When { clauses, .. },
        PseudoExpr::Lambda {
            params,
            body: adapter_body,
        },
    ) = (let_value, let_body)
    else {
        unreachable!("inlines_when_adapter checked both shapes");
    };
    let PseudoExpr::Apply { args, .. } = adapter_body.as_ref() else {
        unreachable!("inlines_when_adapter checked the adapter body");
    };

    Ok(PseudoExpr::Lambda {
        params,
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(args[0].clone()),
            subject_name: None,
            clauses,
        }),
    })
}

/// Whether `let let_name = when subject { … } in fn(x) { let_name(arg) }`
/// can drop the `let` and match on `arg` directly: the adapter only
/// forwards its argument, and no clause still refers to the subject.
fn inlines_when_adapter(let_name: &str, let_value: &PseudoExpr, let_body: &PseudoExpr) -> bool {
    let PseudoExpr::When {
        subject,
        subject_name,
        clauses,
    } = let_value
    else {
        return false;
    };

    if subject_name.is_some() {
        return false;
    }
    let PseudoExpr::Var {
        name: subject_var_name,
        id: subject_var_id,
        ..
    } = subject.as_ref()
    else {
        return false;
    };
    // A `Var` subject may carry `id: None`. Pass a fresh placeholder so
    // `var_is_referenced_id_aware` receives a concrete VarId; that function
    // matches an id-less reference by name on its own.
    let subject_var_id = subject_var_id.unwrap_or_else(VarId::fresh_compat_placeholder);

    let PseudoExpr::Lambda {
        body: adapter_body, ..
    } = let_body
    else {
        return false;
    };

    let PseudoExpr::Apply { function, args } = adapter_body.as_ref() else {
        return false;
    };
    if args.len() != 1 {
        return false;
    }
    let PseudoExpr::Var {
        name: called_name, ..
    } = function.as_ref()
    else {
        return false;
    };
    if called_name != let_name {
        return false;
    }

    for clause in clauses {
        if var_is_referenced_id_aware(&clause.body, subject_var_id, subject_var_name) {
            return false;
        }
        if let Some(guard) = &clause.guard
            && var_is_referenced_id_aware(guard, subject_var_id, subject_var_name)
        {
            return false;
        }
    }
    true
}

/// Rewrites `if a <= b { if a == b { some } else { none } } else { rest }`
/// into `if a == b { some } else { if a < b { none } else { rest } }`, or
/// hands the three branches back untouched.
pub(crate) fn try_normalize_sorted_assoc_lookup_if(
    condition: PseudoExpr,
    then_branch: PseudoExpr,
    else_branch: PseudoExpr,
) -> Result<PseudoExpr, (PseudoExpr, PseudoExpr, PseudoExpr)> {
    let Some((lt_op, left, right, inner_then, inner_else)) =
        sorted_assoc_lookup_parts(&condition, &then_branch).map(
            |(lt_op, left, right, inner_then, inner_else)| {
                (
                    lt_op,
                    left.clone(),
                    right.clone(),
                    inner_then.clone(),
                    inner_else.clone(),
                )
            },
        )
    else {
        return Err((condition, then_branch, else_branch));
    };

    Ok(PseudoExpr::If {
        condition: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(left.clone()),
            right: PBox::new(right.clone()),
        }),
        then_branch: PBox::new(inner_then),
        else_branch: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::BinOp {
                op: lt_op,
                left: PBox::new(left),
                right: PBox::new(right),
            }),
            then_branch: PBox::new(inner_else),
            else_branch: PBox::new(else_branch),
        }),
    })
}

/// The pieces of a sorted-assoc lookup `if`: the strict operator, both
/// compared operands, and the inner `if`'s two branches.
fn sorted_assoc_lookup_parts<'e>(
    condition: &'e PseudoExpr,
    then_branch: &'e PseudoExpr,
) -> Option<(
    BinaryOp,
    &'e PseudoExpr,
    &'e PseudoExpr,
    &'e PseudoExpr,
    &'e PseudoExpr,
)> {
    let (lt_op, left, right) = match condition {
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
    } = then_branch
    else {
        return None;
    };

    if !is_standard_option_none_candidate(inner_else.as_ref()) {
        return None;
    }
    if !matches_same_equality_operands(inner_condition, left, right) {
        return None;
    }
    Some((lt_op, left, right, inner_then, inner_else))
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
