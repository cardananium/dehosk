use crate::builtins::BuiltinId;
use crate::decompile::list_traversal::list_literal_parts;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, PseudoData, PseudoExpr};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use num_traits::ToPrimitive;

#[cfg(test)]
use crate::decompile::list_traversal::list_subject_and_tail_depth;
#[cfg(test)]
use crate::pseudo::ast::Binder;
#[cfg(test)]
use std::collections::BTreeSet;

pub(crate) fn normalize_constructor_data_expr(
    tag_expr: PseudoExpr,
    fields_expr: PseudoExpr,
) -> PseudoExpr {
    if let PseudoExpr::Int(ref tag_int) = tag_expr
        && let Some(tag) = tag_int.to_usize()
    {
        if let Some((elements, tail)) = list_literal_parts(&fields_expr) {
            if tail.is_none() {
                let arity = elements.len();
                return PseudoExpr::constr(ConstructorShape::unknown_data(tag, arity), elements);
            }

            return PseudoExpr::builtin_id(
                BuiltinId::DataConstr,
                vec![
                    tag_expr,
                    PseudoExpr::List {
                        elements: elements.into(),
                        tail: tail.map(PBox::new),
                    },
                ],
            );
        }

        if matches!(fields_expr, PseudoExpr::Var { .. }) {
            return PseudoExpr::constr(ConstructorShape::unknown_data(tag, 1), vec![fields_expr]);
        }
    }

    PseudoExpr::builtin_id(BuiltinId::DataConstr, vec![tag_expr, fields_expr])
}

pub(crate) fn normalize_convertible_data_expr(expr: PseudoExpr) -> PseudoExpr {
    match expr {
        PseudoExpr::Data(data) => {
            let data = *data;
            if pseudo_data_is_convertible(&data) {
                pseudo_data_to_expr(data.clone()).unwrap_or(PseudoExpr::Data(Box::new(data)))
            } else {
                PseudoExpr::Data(Box::new(data))
            }
        }
        other => other,
    }
}

pub(crate) fn rewrite_constr_exposer_wrapper(
    function_name: &str,
    args: Vec<PseudoExpr>,
) -> Option<PseudoExpr> {
    if args.len() != 1 {
        return None;
    }

    match function_name {
        "__constr_index_exposer" => Some(PseudoExpr::builtin_id(BuiltinId::DataConstrIndex, args)),
        "__constr_fields_exposer" => {
            Some(PseudoExpr::builtin_id(BuiltinId::DataConstrFields, args))
        }
        _ => None,
    }
}

#[derive(Clone, Copy)]
pub(crate) enum ConstrPairProjection {
    Tag,
    Fields,
}

impl ConstrPairProjection {
    fn field_name(self) -> &'static str {
        match self {
            Self::Tag => "tag",
            Self::Fields => "fields",
        }
    }
}

pub(crate) fn rewrite_constr_unpack_pair_projection(
    pair_arg: &PseudoExpr,
    tracked_subject: Option<PseudoExpr>,
    projection: ConstrPairProjection,
) -> Option<PseudoExpr> {
    let subject = match pair_arg {
        PseudoExpr::BuiltinCall { name, args }
            if (*name == BuiltinId::ConstrUnpack || *name == BuiltinId::DataUnConstr)
                && args.len() == 1 =>
        {
            Some(args[0].clone())
        }
        _ => tracked_subject,
    }?;

    Some(PseudoExpr::field_access(
        subject,
        projection.field_name().to_string(),
    ))
}

pub(crate) fn extract_constr_unpack_subject(expr: &PseudoExpr) -> Option<&PseudoExpr> {
    match expr {
        PseudoExpr::BuiltinCall { name, args }
            if (*name == BuiltinId::ConstrUnpack || *name == BuiltinId::DataUnConstr)
                && args.len() == 1 =>
        {
            Some(&args[0])
        }
        _ => None,
    }
}

#[cfg(test)]
pub(crate) fn extract_constr_unpack_subject_var_name(expr: &PseudoExpr) -> Option<&str> {
    match extract_constr_unpack_subject(expr) {
        Some(PseudoExpr::Var { name, .. }) => Some(name.as_str()),
        _ => None,
    }
}

pub(crate) fn extract_constr_unpack_fst_subject(expr: &PseudoExpr) -> Option<&PseudoExpr> {
    match expr {
        PseudoExpr::FieldAccess {
            record, selector, ..
        } if selector.is_pair_fst() => extract_constr_unpack_subject(record),
        PseudoExpr::IndexAccess {
            collection,
            index: 0,
        } => extract_constr_unpack_subject(collection),
        _ => None,
    }
}

#[cfg(test)]
pub(crate) fn is_constr_unpack_of_var(expr: &PseudoExpr, subject_name: &str) -> bool {
    matches!(
        extract_constr_unpack_subject_var_name(expr),
        Some(name) if name == subject_name
    )
}

#[cfg(test)]
pub(crate) fn is_constr_unpack_snd_of_var(expr: &PseudoExpr, subject_name: &str) -> bool {
    matches!(
        expr,
        PseudoExpr::FieldAccess { record, selector, .. }
            if selector.is_pair_snd() && is_constr_unpack_of_var(record, subject_name)
    )
}

pub(crate) fn extract_constr_unpack_tag_eq(expr: &PseudoExpr) -> Option<(&PseudoExpr, usize)> {
    let PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left,
        right,
    } = expr
    else {
        return None;
    };

    if let Some(subject) = extract_constr_unpack_fst_subject(left)
        && let PseudoExpr::Int(n) = right.as_ref()
        && let Some(tag) = n.to_usize()
    {
        return Some((subject, tag));
    }

    if let Some(subject) = extract_constr_unpack_fst_subject(right)
        && let PseudoExpr::Int(n) = left.as_ref()
        && let Some(tag) = n.to_usize()
    {
        return Some((subject, tag));
    }

    None
}

#[cfg(test)]
pub(crate) fn extract_constr_unpack_tag_eq_var_name(expr: &PseudoExpr) -> Option<(&str, usize)> {
    let (subject, tag) = extract_constr_unpack_tag_eq(expr)?;
    match subject {
        PseudoExpr::Var { name, .. } => Some((name.as_str(), tag)),
        _ => None,
    }
}

#[cfg(test)]
pub(crate) fn is_constr_unpack_tag_eq_for_var(expr: &PseudoExpr, subject_name: &str) -> bool {
    matches!(
        extract_constr_unpack_tag_eq_var_name(expr),
        Some((name, _)) if name == subject_name
    )
}

#[cfg(test)]
pub(crate) fn extract_expect_constr_unpack_tag(
    expr: &PseudoExpr,
) -> Option<(usize, &str, &PseudoExpr)> {
    let PseudoExpr::Apply { function, args } = expr else {
        return None;
    };
    if !matches!(
        function.as_ref(),
        PseudoExpr::Var { name, .. } if name == "expect!"
    ) || args.len() != 2
    {
        return None;
    }

    let (subject_name, tag) = extract_constr_unpack_tag_eq_var_name(&args[0])?;
    Some((tag, subject_name, &args[1]))
}

#[cfg(test)]
pub(crate) fn extract_constr_unpack_field_index(
    expr: &PseudoExpr,
    subject_name: &str,
) -> Option<usize> {
    if let PseudoExpr::FieldAccess {
        record, selector, ..
    } = expr
    {
        if selector.is_list_head() {
            let (inner, depth) = list_subject_and_tail_depth(record);
            if is_constr_unpack_snd_of_var(&inner, subject_name) {
                return Some(depth);
            }
        }
    }

    if let PseudoExpr::IndexAccess { collection, index } = expr {
        let (inner, depth) = list_subject_and_tail_depth(collection);
        if is_constr_unpack_snd_of_var(&inner, subject_name) {
            return Some(depth + index);
        }
    }

    None
}

#[cfg(test)]
pub(crate) fn collect_constr_unpack_field_indices(
    expr: &PseudoExpr,
    subject_name: &str,
    indices: &mut BTreeSet<usize>,
) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        if let Some(idx) = extract_constr_unpack_field_index(cur, subject_name) {
            indices.insert(idx);
            continue;
        }

        let mut kids: Vec<&PseudoExpr> = Vec::new();
        match cur {
            PseudoExpr::Let { value, body, .. } => {
                kids.push(value);
                kids.push(body);
            }
            PseudoExpr::Apply { function, args } => {
                kids.push(function);
                for arg in args {
                    kids.push(arg);
                }
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                kids.push(body);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                kids.push(condition);
                kids.push(then_branch);
                kids.push(else_branch);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                kids.push(subject);
                for clause in clauses {
                    if let Some(guard) = &clause.guard {
                        kids.push(guard);
                    }
                    kids.push(&clause.body);
                }
            }
            PseudoExpr::List { elements, tail } => {
                for element in elements {
                    kids.push(element);
                }
                if let Some(tail) = tail {
                    kids.push(tail);
                }
            }
            PseudoExpr::Tuple(elements) => {
                for element in elements {
                    kids.push(element);
                }
            }
            PseudoExpr::Pair(left, right) | PseudoExpr::BinOp { left, right, .. } => {
                kids.push(left);
                kids.push(right);
            }
            PseudoExpr::UnOp { operand, .. }
            | PseudoExpr::FieldAccess {
                record: operand, ..
            }
            | PseudoExpr::IndexAccess {
                collection: operand,
                ..
            }
            | PseudoExpr::Delay(operand)
            | PseudoExpr::Force(operand) => {
                kids.push(operand);
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args {
                    kids.push(arg);
                }
            }
            PseudoExpr::Constr { fields, .. } => {
                for field in fields {
                    kids.push(field);
                }
            }
            PseudoExpr::Trace { message, value } => {
                kids.push(message);
                kids.push(value);
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
        }
        pending.extend(kids.into_iter().rev());
    }
}

/// Every node rewrites its children uniformly — no binder opens a scope here
/// — so a node is either replaced outright or split into a shell plus its
/// children, which the matching `Rebuild` step puts back.
#[cfg(test)]
pub(crate) fn rewrite_constr_unpack_field_accesses(
    expr: PseudoExpr,
    subject_name: &str,
    max_field: usize,
    field_binders: Option<&[Binder]>,
) -> PseudoExpr {
    /// Split a node into a SHELL — every immediate child replaced by a `Unit`
    /// placeholder — plus those children in `map_children` order.
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

    enum Job {
        Visit(PseudoExpr),
        /// The node's rewritten children sit on `done`; put them back into the
        /// shell they were taken out of.
        Rebuild {
            shell: PseudoExpr,
            count: usize,
        },
    }

    let mut jobs: Vec<Job> = vec![Job::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(job) = jobs.pop() {
        let expr = match job {
            Job::Visit(expr) => expr,
            Job::Rebuild { shell, count } => {
                let at = done.len() - count;
                let kids = done.split_off(at);
                done.push(join_children(shell, kids));
                continue;
            }
        };

        if let Some(idx) = extract_constr_unpack_field_index(&expr, subject_name) {
            if idx <= max_field {
                if let Some(binder) = field_binders.and_then(|binders| binders.get(idx)) {
                    done.push(PseudoExpr::var_with_id(binder.as_str(), binder.id));
                    continue;
                }

                done.push(PseudoExpr::var(format!("field_{}", idx)));
                continue;
            }
        }

        match expr {
            PseudoExpr::Apply { function, args } => {
                if matches!(
                    function.as_ref(),
                    PseudoExpr::Var { name, .. } if name == "expect!"
                ) && args.len() == 2
                    && is_constr_unpack_tag_eq_for_var(&args[0], subject_name)
                {
                    if let Some(rewritten) = args.get(1).cloned() {
                        jobs.push(Job::Visit(rewritten));
                        continue;
                    }
                }

                let (shell, kids) = split_children(PseudoExpr::Apply { function, args });
                jobs.push(Job::Rebuild {
                    shell,
                    count: kids.len(),
                });
                // Reversed so they pop — and so land on `done` — in order.
                for kid in kids.into_iter().rev() {
                    jobs.push(Job::Visit(kid));
                }
            }
            // Every other node rewrites its children uniformly, in
            // `map_children`'s order; leaves (Var, Int, ByteArray, String,
            // Bool, Unit, Error, Raw, Data, HelperSymbol) split into zero
            // children and rejoin unchanged.
            other => {
                let (shell, kids) = split_children(other);
                jobs.push(Job::Rebuild {
                    shell,
                    count: kids.len(),
                });
                for kid in kids.into_iter().rev() {
                    jobs.push(Job::Visit(kid));
                }
            }
        }
    }

    done.pop()
        .expect("rewrite_constr_unpack_field_accesses leaves exactly one result")
}

pub(crate) fn is_empty_constr_tag(expr: &PseudoExpr, tag: usize) -> bool {
    matches!(
        expr,
        PseudoExpr::Constr {
            tag: expr_tag,
            fields,
            ..
        } if *expr_tag == tag && fields.is_empty()
    )
}

pub(crate) fn is_known_empty_constr_tag(expr: &PseudoExpr, kc: KnownConstructor) -> bool {
    matches!(
        expr,
        PseudoExpr::Constr {
            shape,
            tag: expr_tag,
            fields,
            ..
        } if *shape == ConstructorShape::Known(kc)
            && *expr_tag == kc.expected_tag()
            && fields.is_empty()
    )
}

pub(crate) fn is_bool_true_like(expr: &PseudoExpr) -> bool {
    match expr {
        PseudoExpr::Bool(true) => true,
        _ if is_known_empty_constr_tag(expr, KnownConstructor::True) => true,
        _ if is_empty_constr_tag(expr, 1) => true,
        _ => false,
    }
}

pub(crate) fn is_bool_false_like(expr: &PseudoExpr) -> bool {
    match expr {
        PseudoExpr::Bool(false) => true,
        _ if is_known_empty_constr_tag(expr, KnownConstructor::False) => true,
        _ if is_empty_constr_tag(expr, 0) => true,
        _ => false,
    }
}

pub(crate) fn is_standard_option_none_candidate(expr: &PseudoExpr) -> bool {
    matches!(expr, PseudoExpr::Bool(true))
        || is_known_empty_constr_tag(expr, KnownConstructor::None)
        || is_empty_constr_tag(expr, 1)
}

pub(crate) fn is_standard_option_some_candidate(expr: &PseudoExpr) -> bool {
    matches!(
        expr,
        PseudoExpr::Constr {
            shape: ConstructorShape::Known(KnownConstructor::Some),
            fields,
            ..
        } if fields.len() == 1
    ) || is_option_some_arity1(expr)
}

/// `Some(x)` is `Constr<0>([x])` — it wraps EXACTLY one value. A
/// tag-0 `Constr`/`DataConstr` of any other arity is a distinct ADT
/// constructor that merely shares the zero tag (e.g. a 2-field record
/// `Constr<0>([a, b])`), and rendering one as `Some` yields the
/// unparseable `Some(x, 0)` — hence the arity-1 gate. An opaque
/// `DataConstr(0, var)` fields list of unknown length still counts as
/// a single wrapped field, matching
/// `extract_standard_option_some_fields`.
fn is_option_some_arity1(expr: &PseudoExpr) -> bool {
    match expr {
        PseudoExpr::Constr { tag: 0, fields, .. } => fields.len() == 1,
        PseudoExpr::BuiltinCall { name, args }
            if *name == BuiltinId::DataConstr && args.len() == 2 =>
        {
            if !matches!(&args[0], PseudoExpr::Int(n) if n.to_usize() == Some(0)) {
                return false;
            }
            match list_literal_parts(&args[1]) {
                Some((elements, tail)) => tail.is_none() && elements.len() == 1,
                None => matches!(&args[1], PseudoExpr::Var { .. }),
            }
        }
        _ => false,
    }
}

pub(crate) fn extract_standard_option_some_fields(expr: &PseudoExpr) -> Option<Vec<PseudoExpr>> {
    match expr {
        // A multi-field tag-0 `Constr` is a different ADT, not `Some`
        // (see `is_option_some_arity1`).
        PseudoExpr::Constr { tag: 0, fields, .. } if fields.len() == 1 => {
            Some((fields.clone()).into_vec())
        }
        PseudoExpr::BuiltinCall { name, args }
            if *name == BuiltinId::DataConstr && args.len() == 2 =>
        {
            let PseudoExpr::Int(tag) = &args[0] else {
                return None;
            };
            if tag.to_usize() != Some(0) {
                return None;
            }

            let fields_expr = &args[1];
            if let Some((elements, tail)) = list_literal_parts(fields_expr)
                && tail.is_none()
                && elements.len() == 1
            {
                return Some(elements);
            }

            if matches!(fields_expr, PseudoExpr::Var { .. }) {
                return Some(vec![fields_expr.clone()]);
            }

            None
        }
        _ => None,
    }
}

pub(crate) fn make_standard_option_none() -> PseudoExpr {
    PseudoExpr::constr_known(KnownConstructor::None, vec![])
}

pub(crate) fn make_standard_option_some(fields: Vec<PseudoExpr>) -> PseudoExpr {
    PseudoExpr::constr_known(KnownConstructor::Some, fields)
}

fn pseudo_data_is_convertible(data: &PseudoData) -> bool {
    match data {
        PseudoData::Constr(_, fields) => fields.iter().all(pseudo_data_is_convertible),
        PseudoData::List(items) => items.iter().all(pseudo_data_is_convertible),
        PseudoData::Integer(_) | PseudoData::ByteString(_) => true,
        PseudoData::Map(_) => false,
    }
}

fn pseudo_data_to_expr(data: PseudoData) -> Option<PseudoExpr> {
    match data {
        PseudoData::Constr(tag, fields) => {
            let lowered_fields: Option<Vec<PseudoExpr>> =
                fields.into_iter().map(pseudo_data_to_expr).collect();
            let fields = lowered_fields?;
            let arity = fields.len();
            Some(PseudoExpr::constr(
                ConstructorShape::unknown_data(tag, arity),
                fields,
            ))
        }
        PseudoData::Integer(n) => Some(PseudoExpr::Int(n)),
        PseudoData::ByteString(bs) => Some(PseudoExpr::ByteArray(bs)),
        PseudoData::List(items) => {
            let lowered: Option<Vec<PseudoExpr>> =
                items.into_iter().map(pseudo_data_to_expr).collect();
            Some(PseudoExpr::List {
                elements: (lowered?).into(),
                tail: None,
            })
        }
        PseudoData::Map(_) => None,
    }
}

#[cfg(test)]
mod tests;
