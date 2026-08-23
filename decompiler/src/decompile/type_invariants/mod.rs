use crate::decompile::final_type_table::FinalTypeTable;
use crate::decompile::mid::type_env::{TypeEnvironment, resolve_type_with_env};
use crate::error::{DecompileError, Result};
use crate::pseudo::ast::{
    BinaryOp, PseudoExpr, PseudoType, TypeResolution, UnaryOp, WhenClause, WhenPattern,
};
use crate::pseudo::constructor::KnownConstructor;
use crate::pseudo::field_selector::FieldSelector;

fn invariant_error(message: impl Into<String>) -> DecompileError {
    DecompileError::internal(format!("type invariant violated: {}", message.into()))
}

fn effective_expr_type(
    expr: &PseudoExpr,
    final_types: Option<&FinalTypeTable>,
    env: &TypeEnvironment,
) -> TypeResolution {
    let mut current = expr;
    loop {
        match current {
            PseudoExpr::Let { body, .. } => current = body,
            PseudoExpr::Trace { value, .. } => current = value,
            PseudoExpr::Var { id, .. } => {
                // `FinalTypeTable` is authoritative for typed output on the
                // final AST. The frozen MIR env is the fallback, so callers
                // that pass only a MIR env still resolve.
                if let Some(final_types) = final_types
                    && let Some(ty) = id.and_then(|vid| final_types.type_of_var(vid))
                {
                    return TypeResolution::known(ty);
                }
                return resolve_type_with_env(current, Some(env));
            }
            _ => return resolve_type_with_env(current, Some(env)),
        }
    }
}

fn validate_when_pattern(
    pattern: &WhenPattern,
    subject_ty: &PseudoType,
    subject_expr: &PseudoExpr,
) -> Result<()> {
    // `Data` subjects are accepted for every collection-style pattern
    // (Pair / Tuple / List / Pair Constructor): the simplifier
    // matches raw `Data` values whose runtime shape fits the pattern
    // before the type tracker narrows them.
    //
    // `Function { ... }` is accepted universally: the solver hints
    // every Lambda/RecFn as Function, and inlining can collapse a
    // let-bound Lambda into a body that is legitimately pair- or
    // list-shaped.
    let violation = match pattern {
        WhenPattern::Pair(_, _) => (!matches!(
            subject_ty,
            PseudoType::Pair(_, _)
                | PseudoType::Unknown
                | PseudoType::Data
                | PseudoType::Function { .. }
        ))
        .then_some("pair"),
        WhenPattern::Tuple(fields) => match subject_ty {
            PseudoType::Tuple(items) if items.len() == fields.len() => None,
            PseudoType::Unknown | PseudoType::Data | PseudoType::Function { .. } => None,
            _ => Some("tuple"),
        },
        WhenPattern::List { .. } => (!matches!(
            subject_ty,
            PseudoType::List(_)
                | PseudoType::Unknown
                | PseudoType::Data
                | PseudoType::Function { .. }
        ))
        .then_some("list"),
        WhenPattern::Constructor { shape, .. }
            if shape.as_known() == Some(KnownConstructor::Pair) =>
        {
            (!matches!(
                subject_ty,
                PseudoType::Pair(_, _)
                    | PseudoType::Unknown
                    | PseudoType::Data
                    | PseudoType::Function { .. }
            ))
            .then_some("pair")
        }
        _ => None,
    };

    if let Some(kind) = violation {
        Err(invariant_error(format!(
            "{kind} pattern cannot match `{:?}` for subject `{:?}`",
            subject_ty, subject_expr
        )))
    } else {
        Ok(())
    }
}

fn validate_field_access(record_ty: &PseudoType, field: &str) -> Result<()> {
    // `fields` / `tag` are universal Constr-projection selectors: any value
    // shaped as a Constr can carry them — `Data` (the catch-all UPLC type),
    // `Result(_, _)` and `Option(_)` (both lower to Constr<0|1>(payload)),
    // `Pair(_, _)` (the simplifier types `Pair.first(unpack(X))` results as
    // Pair before projection normalisation), and `Unknown`.
    let valid = match field {
        // Permissive: Constr-projection is allowed on any type. The
        // simplifier can intermediate-type a value as `Int` /
        // `ByteArray` / `String` while the AST still carries a
        // `.fields` chain, and erroring here would abort the whole
        // decompilation.
        "fields" | "tag" => true,
        // `Constr.unpack(X)` produces a `Pair<Int, List<Data>>` that
        // pseudo-types still spell `Data` until naming/simplify strips the
        // unpack wrapping, so `fst`/`snd` on `Data` is a legitimate
        // intermediate — as are the `1st`/`2nd` aliases.
        "fst" | "snd" | "first" | "second" | "1st" | "2nd" => {
            matches!(
                record_ty,
                PseudoType::Pair(_, _) | PseudoType::Unknown | PseudoType::Data
            )
        }
        // Same for List selectors on `Data`: `un_list` returns a
        // `List<Data>` that surrounding code may still see as `Data`.
        "head" | "tail" => matches!(
            record_ty,
            PseudoType::List(_) | PseudoType::Unknown | PseudoType::Data
        ),
        _ => true,
    };

    if valid {
        Ok(())
    } else {
        Err(invariant_error(format!(
            "field `{field}` cannot be read from `{:?}`",
            record_ty
        )))
    }
}

fn validate_index_access(collection_ty: &PseudoType) -> Result<()> {
    // `Data` wraps List/Pair/Constr forms, so index access on it is
    // the standard way to navigate raw Data before the type tracker
    // promotes the wrapper to a specific collection type.
    if matches!(
        collection_ty,
        PseudoType::List(_)
            | PseudoType::Tuple(_)
            | PseudoType::Pair(_, _)
            | PseudoType::Unknown
            | PseudoType::Data
    ) {
        Ok(())
    } else {
        Err(invariant_error(format!(
            "index access requires a collection, got `{:?}`",
            collection_ty
        )))
    }
}

fn validate_binary_op(op: BinaryOp, left_ty: &PseudoType, right_ty: &PseudoType) -> Result<()> {
    // `Data` plays the role of `Unknown` here — the simplifier may
    // compare a typed value (Int, ByteArray) against a raw `Data`
    // value whose underlying shape is compatible.
    let flexible = |ty: &PseudoType| matches!(ty, PseudoType::Unknown | PseudoType::Data);
    let valid = match op {
        BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
            { matches!(left_ty, PseudoType::Int) || flexible(left_ty) }
                .then_some(())
                .and_then(|_| {
                    (matches!(right_ty, PseudoType::Int) || flexible(right_ty)).then_some(())
                })
                .is_some()
        }
        BinaryOp::And | BinaryOp::Or => {
            is_valid_if_condition_type(left_ty) && is_valid_if_condition_type(right_ty)
        }
        BinaryOp::Lt | BinaryOp::Lte | BinaryOp::Gt | BinaryOp::Gte => {
            (matches!(left_ty, PseudoType::Int | PseudoType::ByteArray) || flexible(left_ty))
                && (matches!(right_ty, PseudoType::Int | PseudoType::ByteArray)
                    || flexible(right_ty))
                && (flexible(left_ty) || flexible(right_ty) || left_ty == right_ty)
        }
        BinaryOp::Eq | BinaryOp::Neq => {
            flexible(left_ty) || flexible(right_ty) || left_ty == right_ty
        }
        BinaryOp::Cons => match right_ty {
            PseudoType::List(inner) => {
                matches!(left_ty, PseudoType::Unknown) || **inner == *left_ty
            }
            PseudoType::Unknown => true,
            _ => false,
        },
        BinaryOp::Concat => {
            let side_ok = |ty: &PseudoType| {
                matches!(
                    ty,
                    PseudoType::ByteArray | PseudoType::String | PseudoType::Unknown
                )
            };
            side_ok(left_ty)
                && side_ok(right_ty)
                && (matches!(left_ty, PseudoType::Unknown)
                    || matches!(right_ty, PseudoType::Unknown)
                    || left_ty == right_ty)
        }
    };

    if valid {
        Ok(())
    } else {
        Err(invariant_error(format!(
            "binary op `{:?}` cannot be applied to `{:?}` and `{:?}`",
            op, left_ty, right_ty
        )))
    }
}

fn validate_unary_op(op: UnaryOp, operand_ty: &PseudoType) -> Result<()> {
    let valid = match op {
        UnaryOp::Not => is_valid_if_condition_type(operand_ty),
        UnaryOp::Negate => matches!(operand_ty, PseudoType::Int | PseudoType::Unknown),
        UnaryOp::Length => {
            matches!(
                operand_ty,
                PseudoType::ByteArray | PseudoType::List(_) | PseudoType::Unknown
            )
        }
    };

    if valid {
        Ok(())
    } else {
        Err(invariant_error(format!(
            "unary op `{:?}` cannot be applied to `{:?}`",
            op, operand_ty
        )))
    }
}

fn is_valid_if_condition_type(condition_ty: &PseudoType) -> bool {
    matches!(
        condition_ty,
        PseudoType::Bool
            | PseudoType::Data
            | PseudoType::Unknown
            | PseudoType::Option(_)
            | PseudoType::Result(_, _)
            | PseudoType::Named(_)
    )
}

pub(crate) fn validate_type_invariants(
    expr: &PseudoExpr,
    final_types: Option<&FinalTypeTable>,
    env: &TypeEnvironment,
) -> Result<()> {
    fn validate(
        expr: &PseudoExpr,
        final_types: Option<&FinalTypeTable>,
        env: &TypeEnvironment,
    ) -> Result<()> {
        enum Step<'e> {
            Visit(&'e PseudoExpr),
            CheckIf(&'e PseudoExpr),
            AfterWhenSubject {
                subject: &'e PseudoExpr,
                clauses: &'e [WhenClause],
            },
            EnterClause {
                subject: &'e PseudoExpr,
                subject_ty: TypeResolution,
                clause: &'e WhenClause,
            },
            CheckFieldAccess {
                record: &'e PseudoExpr,
                selector: &'e FieldSelector,
            },
            CheckIndexAccess(&'e PseudoExpr),
            CheckBinOp {
                op: BinaryOp,
                left: &'e PseudoExpr,
                right: &'e PseudoExpr,
            },
            CheckUnOp {
                op: UnaryOp,
                operand: &'e PseudoExpr,
            },
        }

        let mut steps: Vec<Step<'_>> = vec![Step::Visit(expr)];
        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(expr) => match expr {
                    PseudoExpr::Let { value, body, .. } => {
                        steps.push(Step::Visit(body));
                        steps.push(Step::Visit(value));
                    }
                    PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
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
                        steps.push(Step::CheckIf(condition));
                        steps.push(Step::Visit(else_branch));
                        steps.push(Step::Visit(then_branch));
                        steps.push(Step::Visit(condition));
                    }
                    PseudoExpr::When {
                        subject, clauses, ..
                    } => {
                        steps.push(Step::AfterWhenSubject { subject, clauses });
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
                    PseudoExpr::Pair(left, right) => {
                        steps.push(Step::Visit(right));
                        steps.push(Step::Visit(left));
                    }
                    PseudoExpr::Constr { fields, .. } => {
                        for field in fields.iter().rev() {
                            steps.push(Step::Visit(field));
                        }
                    }
                    PseudoExpr::FieldAccess {
                        record, selector, ..
                    } => {
                        steps.push(Step::CheckFieldAccess { record, selector });
                        steps.push(Step::Visit(record));
                    }
                    PseudoExpr::IndexAccess { collection, .. } => {
                        steps.push(Step::CheckIndexAccess(collection));
                        steps.push(Step::Visit(collection));
                    }
                    PseudoExpr::BinOp { op, left, right } => {
                        steps.push(Step::CheckBinOp {
                            op: *op,
                            left,
                            right,
                        });
                        steps.push(Step::Visit(right));
                        steps.push(Step::Visit(left));
                    }
                    PseudoExpr::UnOp { op, operand } => {
                        steps.push(Step::CheckUnOp { op: *op, operand });
                        steps.push(Step::Visit(operand));
                    }
                    PseudoExpr::BuiltinCall { args, .. } => {
                        for arg in args.iter().rev() {
                            steps.push(Step::Visit(arg));
                        }
                    }
                    PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                        steps.push(Step::Visit(inner));
                    }
                    PseudoExpr::Trace { message, value } => {
                        steps.push(Step::Visit(value));
                        steps.push(Step::Visit(message));
                    }
                    PseudoExpr::Var { .. }
                    | PseudoExpr::Int(_)
                    | PseudoExpr::ByteArray(_)
                    | PseudoExpr::String(_)
                    | PseudoExpr::Bool(_)
                    | PseudoExpr::Unit
                    | PseudoExpr::Error { .. }
                    | PseudoExpr::Raw { .. }
                    | PseudoExpr::Data(_)
                    | PseudoExpr::HelperSymbol(_) => {}
                },
                Step::CheckIf(condition) => {
                    if let Some(condition_ty) =
                        effective_expr_type(condition, final_types, env).as_deref()
                        && !is_valid_if_condition_type(condition_ty)
                    {
                        return Err(invariant_error(format!(
                            "`if` condition requires Bool/Data, got `{:?}` for condition `{:?}`",
                            condition_ty, condition
                        )));
                    }
                }
                Step::AfterWhenSubject { subject, clauses } => {
                    let subject_ty = effective_expr_type(subject, final_types, env);
                    for clause in clauses.iter().rev() {
                        steps.push(Step::EnterClause {
                            subject,
                            subject_ty: subject_ty.clone(),
                            clause,
                        });
                    }
                }
                Step::EnterClause {
                    subject,
                    subject_ty,
                    clause,
                } => {
                    if let Some(subject_ty) = subject_ty.as_deref() {
                        validate_when_pattern(&clause.pattern, subject_ty, subject)?;
                    }
                    steps.push(Step::Visit(&clause.body));
                    if let Some(guard) = &clause.guard {
                        steps.push(Step::Visit(guard));
                    }
                    if let WhenPattern::Literal(lit) = &clause.pattern {
                        steps.push(Step::Visit(lit));
                    }
                }
                Step::CheckFieldAccess { record, selector } => {
                    if let Some(record_ty) =
                        effective_expr_type(record, final_types, env).as_deref()
                    {
                        validate_field_access(record_ty, selector.as_pretty_name())?;
                    }
                }
                Step::CheckIndexAccess(collection) => {
                    if let Some(collection_ty) =
                        effective_expr_type(collection, final_types, env).as_deref()
                    {
                        validate_index_access(collection_ty)?;
                    }
                }
                Step::CheckBinOp { op, left, right } => {
                    if let (Some(left_ty), Some(right_ty)) = (
                        effective_expr_type(left, final_types, env).as_deref(),
                        effective_expr_type(right, final_types, env).as_deref(),
                    ) {
                        validate_binary_op(op, left_ty, right_ty)?;
                    }
                }
                Step::CheckUnOp { op, operand } => {
                    if let Some(operand_ty) =
                        effective_expr_type(operand, final_types, env).as_deref()
                    {
                        validate_unary_op(op, operand_ty)?;
                    }
                }
            }
        }
        Ok(())
    }

    validate(expr, final_types, env)
}

#[cfg(test)]
mod tests;
