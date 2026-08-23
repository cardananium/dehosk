use crate::pseudo::ast::{BinaryOp, PseudoExpr};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::nameless::convert::{nameless_to_pseudo, pseudo_to_nameless};
use crate::pseudo::nameless::fold::NamelessFolder;
use crate::pseudo::nameless::{NamelessClause, NamelessExpr, NamelessPattern, VarTable};
use crate::pseudo::var_id::VarId;

/// Convert constructor-tag assertions — `expect!(x.tag == N, value)`
/// or `expect!(Constr.unpack(x).fst == N, value)` — to
/// `when x is { Constr<N> -> value; _ -> fail }`.
///
/// Catches `expect!` forms created during simplification that bypass
/// the tag-to-constructor conversion in simplify_if/simplify_when.
///
/// The nameless roundtrip is lossy for duplicate-id bindings: only
/// the first binder's name hint per VarId is kept, so a `Let { id: K }`
/// inside another `Let { id: K }` gets renamed. Skip the roundtrip
/// when there is no `expect!` marker, so the no-op case stays
/// structurally identical to the input.
pub(crate) fn convert_expect_tag_to_constr_when(expr: PseudoExpr) -> PseudoExpr {
    if !contains_expect_marker(&expr) {
        return expr;
    }
    let (nameless, table) = pseudo_to_nameless(&expr);
    let converted = convert_expect_tag_to_constr_when_nameless(nameless, &table);
    nameless_to_pseudo(&converted, &table)
}

/// True iff `expr` contains a `Var { name: "expect!" }` — the
/// structural marker the pass rewrites.
fn contains_expect_marker(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Var { name, .. } => {
                if name == "expect!" {
                    return true;
                }
            }
            PseudoExpr::Lambda { body, .. } => pending.push(body),
            PseudoExpr::RecFn { body, .. } => pending.push(body),
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(value);
                pending.push(body);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(condition);
                pending.push(then_branch);
                pending.push(else_branch);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                pending.push(subject);
                for c in clauses {
                    if let Some(g) = c.guard.as_ref() {
                        pending.push(g);
                    }
                    pending.push(&c.body);
                }
            }
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements);
                if let Some(t) = tail.as_ref() {
                    pending.push(t);
                }
            }
            PseudoExpr::Tuple(items) => pending.extend(items),
            PseudoExpr::Pair(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields),
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args),
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            PseudoExpr::Trace { message, value } => {
                pending.push(message);
                pending.push(value);
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
    false
}

/// Pure nameless implementation. The "expect!" / "fn_call" sentinel
/// names live in the [`VarTable`]: a `Var(id)` is the marker iff
/// `table.render_name_hint(id)` matches the sentinel string.
pub(crate) fn convert_expect_tag_to_constr_when_nameless(
    expr: NamelessExpr,
    table: &VarTable,
) -> NamelessExpr {
    struct ConvertExpectTag<'t> {
        table: &'t VarTable,
    }

    impl<'t> ConvertExpectTag<'t> {
        fn name_of(&self, id: VarId) -> Option<&'t str> {
            self.table.get(id).and_then(|m| m.render_name_hint())
        }

        fn is_named(&self, expr: &NamelessExpr, target: &str) -> bool {
            matches!(
                expr,
                NamelessExpr::Var(id) if self.name_of(*id) == Some(target)
            )
        }

        fn build_constr_when(
            &self,
            subject: NamelessExpr,
            tag: usize,
            value: NamelessExpr,
        ) -> NamelessExpr {
            NamelessExpr::When {
                subject: Box::new(subject),
                subject_name: None,
                clauses: vec![
                    NamelessClause {
                        pattern: NamelessPattern::Constructor {
                            type_hint: None,
                            tag,
                            fields: vec![],
                            shape: ConstructorShape::unknown_data(tag, 0),
                        },
                        guard: None,
                        body: value,
                    },
                    NamelessClause {
                        pattern: NamelessPattern::Wildcard,
                        guard: None,
                        body: NamelessExpr::Error { message: None },
                    },
                ],
            }
        }
    }

    impl<'t> NamelessFolder for ConvertExpectTag<'t> {
        fn post_apply(&mut self, function: NamelessExpr, args: Vec<NamelessExpr>) -> NamelessExpr {
            if !self.is_named(&function, "expect!") || args.is_empty() {
                return NamelessExpr::Apply {
                    function: Box::new(function),
                    args,
                };
            }

            // Form 1: `expect!(BinOp(Eq, lhs, rhs), value)`
            if let NamelessExpr::BinOp {
                op: BinaryOp::Eq,
                left,
                right,
            } = &args[0]
                && let Some((subject, tag)) = extract_tag_comparison_nameless(left, right)
            {
                let value = expect_value_arg_nameless(args);
                return self.build_constr_when(subject, tag, value);
            }

            // Form 2: `expect!(x(x.tag), body)` — Scott encoding,
            // assertion ⇒ tag must be 0.
            if let NamelessExpr::Apply {
                function: inner_fn,
                args: inner_args,
            } = &args[0]
                && inner_args.len() == 1
                && let NamelessExpr::FieldAccess { record, selector } = &inner_args[0]
                && selector.as_pretty_name() == "tag"
                && nameless_var_eq_with_table(inner_fn.as_ref(), record.as_ref(), self.table)
            {
                let subject = (**record).clone();
                let value = expect_value_arg_nameless(args);
                return self.build_constr_when(subject, 0, value);
            }

            // Form 3: `expect!(fn_call(x, x.tag), body)` — wrapped form.
            if let NamelessExpr::Apply {
                function: outer_fn,
                args: outer_args,
            } = &args[0]
                && self.is_named(outer_fn.as_ref(), "fn_call")
                && outer_args.len() == 2
                && let NamelessExpr::FieldAccess { record, selector } = &outer_args[1]
                && selector.as_pretty_name() == "tag"
                && nameless_var_eq_with_table(&outer_args[0], record.as_ref(), self.table)
            {
                let subject = outer_args[0].clone();
                let value = expect_value_arg_nameless(args);
                return self.build_constr_when(subject, 0, value);
            }

            NamelessExpr::Apply {
                function: Box::new(function),
                args,
            }
        }
    }

    ConvertExpectTag { table }.fold(expr)
}

fn nameless_var_eq(lhs: &NamelessExpr, rhs: &NamelessExpr) -> bool {
    matches!(
        (lhs, rhs),
        (NamelessExpr::Var(a), NamelessExpr::Var(b)) if a == b
    )
}

/// Variant of [`nameless_var_eq`] that consults `VarTable` for a
/// name-based fallback when both Var ids are compat placeholders:
/// id-less refs with the same rendered name are the same variable.
fn nameless_var_eq_with_table(lhs: &NamelessExpr, rhs: &NamelessExpr, table: &VarTable) -> bool {
    if nameless_var_eq(lhs, rhs) {
        return true;
    }
    let (NamelessExpr::Var(a), NamelessExpr::Var(b)) = (lhs, rhs) else {
        return false;
    };
    // Paired-unresolved: both refs must carry placeholder ids. Any
    // authoritative id here is a genuine mismatch — `nameless_var_eq`
    // above would have accepted equal ids.
    if a.get().is_some() || b.get().is_some() {
        return false;
    }
    let name_a = table.get(*a).and_then(|m| m.render_name_hint());
    let name_b = table.get(*b).and_then(|m| m.render_name_hint());
    matches!((name_a, name_b), (Some(x), Some(y)) if x == y)
}

fn expect_value_arg_nameless(args: Vec<NamelessExpr>) -> NamelessExpr {
    args.into_iter().nth(1).unwrap_or(NamelessExpr::Unit)
}

fn extract_tag_comparison_nameless(
    left: &NamelessExpr,
    right: &NamelessExpr,
) -> Option<(NamelessExpr, usize)> {
    fn try_unpack_subject(expr: &NamelessExpr) -> Option<NamelessExpr> {
        if let NamelessExpr::BuiltinCall { name, args } = expr
            && (*name == crate::BuiltinId::ConstrUnpack || *name == crate::BuiltinId::DataUnConstr)
            && args.len() == 1
        {
            return Some(args[0].clone());
        }
        None
    }

    fn try_tag_and_int(
        tag_expr: &NamelessExpr,
        int_expr: &NamelessExpr,
    ) -> Option<(NamelessExpr, usize)> {
        use num_traits::ToPrimitive;
        let int_val = if let NamelessExpr::Int(n) = int_expr {
            n.to_usize()?
        } else {
            return None;
        };
        if let NamelessExpr::FieldAccess { record, selector } = tag_expr {
            if selector.as_pretty_name() == "tag" {
                return Some(((**record).clone(), int_val));
            }
            if selector.is_pair_fst() {
                return try_unpack_subject(record).map(|subject| (subject, int_val));
            }
        }
        if let NamelessExpr::IndexAccess {
            collection,
            index: 0,
        } = tag_expr
        {
            return try_unpack_subject(collection).map(|subject| (subject, int_val));
        }
        None
    }

    try_tag_and_int(left, right).or_else(|| try_tag_and_int(right, left))
}

#[cfg(test)]
mod tests;
