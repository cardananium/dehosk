//! Recover `expect <Ctor>(..) = X` from the raw `un_constr_data` spine.
//!
//! The compiled form of a constructor destructure is an
//! `un_constr_data` unpack, a tag comparison and a chain of list
//! projections. This rebuilds the surface `expect` out of it, gated on
//! the tag check actually being present so a bare unpack is never given
//! an assertion it does not make.

use super::*;
use crate::pseudo::ast::PBox;

/// Convert a standalone `expect! Constr.unpack(x).fst == 0` to
/// `expect Constr<0>(field_0, field_1, ...) = x`.
///
/// Handles the cases NOT inside when-branches (those go through
/// `destructure_when_fields`); they appear at the start of function bodies
/// as `Apply(Var("expect!"), [BinOp(Eq, unpack.fst, Int(N)), body])`.
///
/// When the unpack subject's name resolves to a [`ContextType`]
/// (`script_context`, `tx_info`, `tx_out`, …) and `script_version` is
/// `Some`, each minted field binder takes the schema's field name
/// (`tx_info`, `redeemer`, `script_info`, …) instead of `field_N` and is
/// tagged `VarKind::CardanoContext`, so `assign_names::candidate_name`
/// preserves the semantic name at render time.
pub(super) fn resolve_expect_constr_unpack(
    expr: PseudoExpr,
    version: Option<ScriptVersion>,
) -> PseudoExpr {
    use crate::pseudo::ast::{BinaryOp, UnaryOp, WhenClause, WhenPattern};
    use crate::pseudo::fold::ExprFolder;
    use crate::pseudo::var_id::VarId;
    use num_traits::ToPrimitive;

    struct ExpectResolver {
        version: Option<ScriptVersion>,
    }

    // Copies of the `destructure_when_fields` helpers as free fns,
    // reachable outside the When-clause context.

    /// Check if `expr` is `BuiltinCall("Constr.unpack"|"Data.un_constr", [Var(name)])`
    fn is_unpack_of_name(expr: &PseudoExpr, subject_name: &str) -> bool {
        if let PseudoExpr::BuiltinCall { name, args } = expr
            && (*name == crate::BuiltinId::ConstrUnpack || *name == crate::BuiltinId::DataUnConstr)
            && args.len() == 1
            && let PseudoExpr::Var { name: ref vn, .. } = args[0]
        {
            return vn == subject_name;
        }
        false
    }

    /// Check if `expr` is `FieldAccess(unpack(subject), "fst")`.
    fn is_unpack_fst(expr: &PseudoExpr, subject_name: &str) -> bool {
        if let PseudoExpr::FieldAccess {
            record, selector, ..
        } = expr
            && selector.is_pair_fst()
        {
            return is_unpack_of_name(record, subject_name);
        }
        if let PseudoExpr::IndexAccess {
            collection,
            index: 0,
        } = expr
        {
            return is_unpack_of_name(collection, subject_name);
        }
        false
    }

    /// Check if `expr` is `FieldAccess(unpack(subject), "snd")`.
    fn is_unpack_snd(expr: &PseudoExpr, subject_name: &str) -> bool {
        if let PseudoExpr::FieldAccess {
            record, selector, ..
        } = expr
            && selector.is_pair_snd()
        {
            return is_unpack_of_name(record, subject_name);
        }
        false
    }

    /// Count nested `List.tail` calls.
    fn count_tail_depth(expr: &PseudoExpr) -> (&PseudoExpr, usize) {
        let mut current = expr;
        let mut depth = 0usize;
        loop {
            if let PseudoExpr::BuiltinCall { name, args } = current
                && *name == crate::BuiltinId::ListTail
                && args.len() == 1
            {
                depth += 1;
                current = &args[0];
                continue;
            }
            if let PseudoExpr::Apply { function, args } = current
                && let PseudoExpr::BuiltinCall { name, args: ba } = function.as_ref()
                && *name == crate::BuiltinId::ListTail
                && ba.is_empty()
                && args.len() == 1
            {
                depth += 1;
                current = &args[0];
                continue;
            }
            return (current, depth);
        }
    }

    /// Extract field index from `Constr.unpack(subject).snd[N..].head`.
    fn get_field_index(expr: &PseudoExpr, subject_name: &str) -> Option<usize> {
        if let PseudoExpr::FieldAccess {
            record, selector, ..
        } = expr
            && selector.is_list_head()
        {
            let (inner, depth) = count_tail_depth(record);
            if let PseudoExpr::FieldAccess {
                record: direct_record,
                selector: direct_selector,
                ..
            } = inner
                && direct_selector.as_pretty_name() == "fields"
                && let PseudoExpr::Var { name, .. } = direct_record.as_ref()
                && name == subject_name
            {
                return Some(depth);
            }
        }

        if let PseudoExpr::FieldAccess {
            record, selector, ..
        } = expr
            && selector.is_list_head()
        {
            let (inner, depth) = count_tail_depth(record);
            if is_unpack_snd(inner, subject_name) {
                return Some(depth);
            }
        }
        if let PseudoExpr::IndexAccess { collection, index } = expr {
            if let PseudoExpr::FieldAccess {
                record, selector, ..
            } = collection.as_ref()
                && selector.as_pretty_name() == "fields"
                && let PseudoExpr::Var { name, .. } = record.as_ref()
                && name == subject_name
            {
                return Some(*index);
            }
            let (inner, depth) = count_tail_depth(collection);
            if is_unpack_snd(inner, subject_name) {
                return Some(depth + index);
            }
        }
        None
    }

    /// Collect all field indices accessed in an expression.
    fn scan_field_indices(
        expr: &PseudoExpr,
        subject_name: &str,
        indices: &mut std::collections::BTreeSet<usize>,
    ) {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            if let Some(idx) = get_field_index(current, subject_name) {
                indices.insert(idx);
                continue;
            }
            match current {
                PseudoExpr::Let { value, body, .. } => {
                    pending.push(value);
                    pending.push(body);
                }
                PseudoExpr::Apply { function, args } => {
                    pending.push(function);
                    pending.extend(args.iter());
                }
                PseudoExpr::Lambda { body, .. } => {
                    pending.push(body);
                }
                PseudoExpr::RecFn { body, .. } => {
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
                    pending.extend(clauses.iter().map(|c| &c.body));
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(left);
                    pending.push(right);
                }
                PseudoExpr::UnOp { operand, .. } => {
                    pending.push(operand);
                }
                PseudoExpr::BuiltinCall { args, .. } => {
                    pending.extend(args.iter());
                }
                PseudoExpr::FieldAccess { record, .. } => {
                    pending.push(record);
                }
                PseudoExpr::IndexAccess { collection, .. } => {
                    pending.push(collection);
                }
                PseudoExpr::Constr { fields, .. } => {
                    pending.extend(fields.iter());
                }
                PseudoExpr::List { elements, tail } => {
                    pending.extend(elements.iter());
                    if let Some(t) = tail {
                        pending.push(t);
                    }
                }
                PseudoExpr::Tuple(elems) => {
                    pending.extend(elems.iter());
                }
                PseudoExpr::Pair(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                PseudoExpr::Trace { message, value } => {
                    pending.push(message);
                    pending.push(value);
                }
                PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                    pending.push(inner);
                }
                PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::Unit
                | PseudoExpr::Var { .. }
                | PseudoExpr::Error { .. }
                | PseudoExpr::Raw { .. }
                | PseudoExpr::Data(_)
                | PseudoExpr::HelperSymbol(_) => {}
            }
        }
    }

    /// Replace field access patterns with Var("field_N") references.
    // It's hand-rolled rather than expressed as an `ExprFolder` because the
    // `Apply` arm below makes a TOP-DOWN decision — on the raw, unprocessed
    // `function` and `args[0]` — to discard them and descend into only
    // `args[1]`. `ExprFolder::pre_expr` can substitute a node before
    // recursion, but can't then ask the driver to recurse into just one part
    // of what it discarded, so that case is spelled out by hand here,
    // preserving the exact literal order (and the exact discard) instead of
    // arguing it's equivalent to folding everything bottom-up.
    fn rewrite_field_accesses(
        expr: PseudoExpr,
        subject_name: &str,
        field_binders: &[Binder],
    ) -> PseudoExpr {
        enum Step {
            Enter(PseudoExpr),
            Post(Post),
        }
        enum Post {
            Let {
                name: String,
                id: Option<VarId>,
            },
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
            If,
            When {
                subject_name: Option<Binder>,
                clause_meta: Vec<(WhenPattern, bool)>,
            },
            BinOp {
                op: BinaryOp,
            },
            UnOp {
                op: UnaryOp,
            },
            BuiltinCall {
                name: crate::BuiltinId,
                argc: usize,
            },
            FieldAccess {
                selector: crate::pseudo::field_selector::FieldSelector,
            },
            IndexAccess {
                index: usize,
            },
            Constr {
                type_hint: Option<crate::pseudo::type_hint::TypeHintId>,
                tag: usize,
                count: usize,
                shape: ConstructorShape,
            },
            List {
                count: usize,
                has_tail: bool,
            },
            Tuple {
                count: usize,
            },
            Pair,
            Trace,
            Delay,
            Force,
        }

        fn take(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
            let at = done.len() - n;
            done.split_off(at)
        }

        let mut steps: Vec<Step> = vec![Step::Enter(expr)];
        let mut done: Vec<PseudoExpr> = Vec::new();

        while let Some(step) = steps.pop() {
            match step {
                Step::Enter(expr) => {
                    if let Some(idx) = get_field_index(&expr, subject_name)
                        && let Some(field_binder) = field_binders.get(idx)
                    {
                        done.push(PseudoExpr::var_with_id(
                            field_binder.as_str(),
                            field_binder.id,
                        ));
                        continue;
                    }
                    match expr {
                        PseudoExpr::Let {
                            name,
                            id,
                            value,
                            body,
                        } => {
                            steps.push(Step::Post(Post::Let { name, id }));
                            steps.push(Step::Enter(body.into_inner()));
                            steps.push(Step::Enter(value.into_inner()));
                        }
                        PseudoExpr::Apply { function, mut args } => {
                            // Special case: expect!(Constr.unpack(subject).fst == N, body) — remove
                            if let PseudoExpr::Var { ref name, .. } = *function
                                && name == "expect!"
                                && args.len() == 2
                                && is_tag_check(&args[0], subject_name)
                            {
                                let body = args.pop().expect("checked len == 2");
                                steps.push(Step::Enter(body));
                                continue;
                            }
                            let argc = args.len();
                            steps.push(Step::Post(Post::Apply { argc }));
                            for a in args.into_iter().rev() {
                                steps.push(Step::Enter(a));
                            }
                            steps.push(Step::Enter(function.into_inner()));
                        }
                        PseudoExpr::Lambda { params, body } => {
                            steps.push(Step::Post(Post::Lambda { params }));
                            steps.push(Step::Enter(body.into_inner()));
                        }
                        PseudoExpr::RecFn { name, params, body } => {
                            steps.push(Step::Post(Post::RecFn { name, params }));
                            steps.push(Step::Enter(body.into_inner()));
                        }
                        PseudoExpr::If {
                            condition,
                            then_branch,
                            else_branch,
                        } => {
                            steps.push(Step::Post(Post::If));
                            steps.push(Step::Enter(else_branch.into_inner()));
                            steps.push(Step::Enter(then_branch.into_inner()));
                            steps.push(Step::Enter(condition.into_inner()));
                        }
                        PseudoExpr::When {
                            subject,
                            subject_name: sn,
                            clauses,
                        } => {
                            let mut clause_meta = Vec::with_capacity(clauses.len());
                            let mut clause_parts = Vec::with_capacity(clauses.len());
                            for c in clauses {
                                clause_meta.push((c.pattern, c.guard.is_some()));
                                clause_parts.push((c.guard, c.body));
                            }
                            steps.push(Step::Post(Post::When {
                                subject_name: sn,
                                clause_meta,
                            }));
                            for (guard, body) in clause_parts.into_iter().rev() {
                                steps.push(Step::Enter(body));
                                if let Some(g) = guard {
                                    steps.push(Step::Enter(g));
                                }
                            }
                            steps.push(Step::Enter(subject.into_inner()));
                        }
                        PseudoExpr::BinOp { op, left, right } => {
                            steps.push(Step::Post(Post::BinOp { op }));
                            steps.push(Step::Enter(right.into_inner()));
                            steps.push(Step::Enter(left.into_inner()));
                        }
                        PseudoExpr::UnOp { op, operand } => {
                            steps.push(Step::Post(Post::UnOp { op }));
                            steps.push(Step::Enter(operand.into_inner()));
                        }
                        PseudoExpr::BuiltinCall { name, args } => {
                            let argc = args.len();
                            steps.push(Step::Post(Post::BuiltinCall { name, argc }));
                            for a in args.into_iter().rev() {
                                steps.push(Step::Enter(a));
                            }
                        }
                        PseudoExpr::FieldAccess {
                            record, selector, ..
                        } => {
                            steps.push(Step::Post(Post::FieldAccess { selector }));
                            steps.push(Step::Enter(record.into_inner()));
                        }
                        PseudoExpr::IndexAccess { collection, index } => {
                            steps.push(Step::Post(Post::IndexAccess { index }));
                            steps.push(Step::Enter(collection.into_inner()));
                        }
                        PseudoExpr::Constr {
                            type_hint,
                            tag,
                            fields,
                            shape,
                        } => {
                            let count = fields.len();
                            steps.push(Step::Post(Post::Constr {
                                type_hint,
                                tag,
                                count,
                                shape,
                            }));
                            for f in fields.into_iter().rev() {
                                steps.push(Step::Enter(f));
                            }
                        }
                        PseudoExpr::List { elements, tail } => {
                            let count = elements.len();
                            let has_tail = tail.is_some();
                            steps.push(Step::Post(Post::List { count, has_tail }));
                            if let Some(t) = tail {
                                steps.push(Step::Enter(t.into_inner()));
                            }
                            for e in elements.into_iter().rev() {
                                steps.push(Step::Enter(e));
                            }
                        }
                        PseudoExpr::Tuple(elems) => {
                            let count = elems.len();
                            steps.push(Step::Post(Post::Tuple { count }));
                            for e in elems.into_iter().rev() {
                                steps.push(Step::Enter(e));
                            }
                        }
                        PseudoExpr::Pair(a, b) => {
                            steps.push(Step::Post(Post::Pair));
                            steps.push(Step::Enter(b.into_inner()));
                            steps.push(Step::Enter(a.into_inner()));
                        }
                        PseudoExpr::Trace { message, value } => {
                            steps.push(Step::Post(Post::Trace));
                            steps.push(Step::Enter(value.into_inner()));
                            steps.push(Step::Enter(message.into_inner()));
                        }
                        PseudoExpr::Delay(inner) => {
                            steps.push(Step::Post(Post::Delay));
                            steps.push(Step::Enter(inner.into_inner()));
                        }
                        PseudoExpr::Force(inner) => {
                            steps.push(Step::Post(Post::Force));
                            steps.push(Step::Enter(inner.into_inner()));
                        }
                        other @ (PseudoExpr::Int(_)
                        | PseudoExpr::ByteArray(_)
                        | PseudoExpr::String(_)
                        | PseudoExpr::Bool(_)
                        | PseudoExpr::Unit
                        | PseudoExpr::Var { .. }
                        | PseudoExpr::Error { .. }
                        | PseudoExpr::Raw { .. }
                        | PseudoExpr::Data(_)
                        | PseudoExpr::HelperSymbol(_)) => done.push(other),
                    }
                }
                Step::Post(post) => {
                    let rebuilt = match post {
                        Post::Let { name, id } => {
                            let body = done.pop().expect("let body");
                            let value = done.pop().expect("let value");
                            PseudoExpr::Let {
                                name,
                                id,
                                value: PBox::new(value),
                                body: PBox::new(body),
                            }
                        }
                        Post::Apply { argc } => {
                            let args = take(&mut done, argc);
                            let function = done.pop().expect("apply function");
                            PseudoExpr::Apply {
                                function: PBox::new(function),
                                args: args.into(),
                            }
                        }
                        Post::Lambda { params } => {
                            let body = done.pop().expect("lambda body");
                            PseudoExpr::Lambda {
                                params,
                                body: PBox::new(body),
                            }
                        }
                        Post::RecFn { name, params } => {
                            let body = done.pop().expect("recfn body");
                            PseudoExpr::RecFn {
                                name,
                                params,
                                body: PBox::new(body),
                            }
                        }
                        Post::If => {
                            let mut parts = take(&mut done, 3).into_iter();
                            let condition = parts.next().expect("if condition");
                            let then_branch = parts.next().expect("if then");
                            let else_branch = parts.next().expect("if else");
                            PseudoExpr::If {
                                condition: PBox::new(condition),
                                then_branch: PBox::new(then_branch),
                                else_branch: PBox::new(else_branch),
                            }
                        }
                        Post::When {
                            subject_name,
                            clause_meta,
                        } => {
                            let total: usize = 1 + clause_meta
                                .iter()
                                .map(|(_, has_guard)| if *has_guard { 2 } else { 1 })
                                .sum::<usize>();
                            let mut parts = take(&mut done, total).into_iter();
                            let subject = parts.next().expect("when subject");
                            let clauses = clause_meta
                                .into_iter()
                                .map(|(pattern, has_guard)| {
                                    let guard = if has_guard {
                                        Some(parts.next().expect("clause guard"))
                                    } else {
                                        None
                                    };
                                    let body = parts.next().expect("clause body");
                                    WhenClause {
                                        pattern,
                                        guard,
                                        body,
                                    }
                                })
                                .collect();
                            PseudoExpr::When {
                                subject: PBox::new(subject),
                                subject_name,
                                clauses,
                            }
                        }
                        Post::BinOp { op } => {
                            let right = done.pop().expect("binop right");
                            let left = done.pop().expect("binop left");
                            PseudoExpr::BinOp {
                                op,
                                left: PBox::new(left),
                                right: PBox::new(right),
                            }
                        }
                        Post::UnOp { op } => {
                            let operand = done.pop().expect("unop operand");
                            PseudoExpr::UnOp {
                                op,
                                operand: PBox::new(operand),
                            }
                        }
                        Post::BuiltinCall { name, argc } => {
                            let args = take(&mut done, argc);
                            PseudoExpr::BuiltinCall {
                                name,
                                args: args.into(),
                            }
                        }
                        Post::FieldAccess { selector } => {
                            let record = done.pop().expect("field access record");
                            PseudoExpr::field_access_typed(record, selector)
                        }
                        Post::IndexAccess { index } => {
                            let collection = done.pop().expect("index access collection");
                            PseudoExpr::IndexAccess {
                                collection: PBox::new(collection),
                                index,
                            }
                        }
                        Post::Constr {
                            type_hint,
                            tag,
                            count,
                            shape,
                        } => {
                            let fields = take(&mut done, count);
                            PseudoExpr::Constr {
                                type_hint,
                                tag,
                                fields: fields.into(),
                                shape,
                            }
                        }
                        Post::List { count, has_tail } => {
                            let tail = if has_tail { done.pop() } else { None };
                            let elements = take(&mut done, count);
                            PseudoExpr::List {
                                elements: elements.into(),
                                tail: tail.map(PBox::new),
                            }
                        }
                        Post::Tuple { count } => {
                            let elements = take(&mut done, count);
                            PseudoExpr::Tuple(elements.into())
                        }
                        Post::Pair => {
                            let b = done.pop().expect("pair second");
                            let a = done.pop().expect("pair first");
                            PseudoExpr::Pair(PBox::new(a), PBox::new(b))
                        }
                        Post::Trace => {
                            let value = done.pop().expect("trace value");
                            let message = done.pop().expect("trace message");
                            PseudoExpr::Trace {
                                message: PBox::new(message),
                                value: PBox::new(value),
                            }
                        }
                        Post::Delay => {
                            let inner = done.pop().expect("delay inner");
                            PseudoExpr::Delay(PBox::new(inner))
                        }
                        Post::Force => {
                            let inner = done.pop().expect("force inner");
                            PseudoExpr::Force(PBox::new(inner))
                        }
                    };
                    done.push(rebuilt);
                }
            }
        }

        done.pop().expect("rewrite_field_accesses result")
    }

    /// Check if `expr` is a tag-equality check: `unpack(subject).fst == N`.
    fn is_tag_check(expr: &PseudoExpr, subject_name: &str) -> bool {
        if let PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left,
            right,
        } = expr
        {
            return (is_unpack_fst(left, subject_name)
                && matches!(right.as_ref(), PseudoExpr::Int(_)))
                || (is_unpack_fst(right, subject_name)
                    && matches!(left.as_ref(), PseudoExpr::Int(_)));
        }
        false
    }

    /// Try to extract `(tag, subject_binder, stripped_body)` from
    /// `Apply(Var("expect!"), [BinOp(Eq, unpack(x).fst, Int(N)), body])`.
    fn try_extract_expect_unpack(expr: &PseudoExpr) -> Option<(usize, Binder, &PseudoExpr)> {
        if let PseudoExpr::Apply { function, args } = expr
            && let PseudoExpr::Var { name, .. } = function.as_ref()
            && name == "expect!"
            && args.len() == 2
            && let PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left,
                right,
            } = &args[0]
        {
            // left = unpack(x).fst, right = Int(N)
            if let Some(subj) = extract_unpack_fst_subject(left)
                && let PseudoExpr::Int(n) = right.as_ref()
                && let Some(tag) = n.to_usize()
            {
                return Some((tag, subj, &args[1]));
            }
            // right = unpack(x).fst, left = Int(N)
            if let Some(subj) = extract_unpack_fst_subject(right)
                && let PseudoExpr::Int(n) = left.as_ref()
                && let Some(tag) = n.to_usize()
            {
                return Some((tag, subj, &args[1]));
            }
        }
        None
    }

    /// Extract the subject binder from
    /// `FieldAccess(BuiltinCall("Constr.unpack", [Var(x)]), "fst")`.
    fn extract_unpack_fst_subject(expr: &PseudoExpr) -> Option<Binder> {
        if let PseudoExpr::FieldAccess {
            record, selector, ..
        } = expr
            && selector.is_pair_fst()
        {
            return extract_unpack_subject(record);
        }
        if let PseudoExpr::IndexAccess {
            collection,
            index: 0,
        } = expr
        {
            return extract_unpack_subject(collection);
        }
        None
    }

    /// Extract subject binder from
    /// `BuiltinCall("Constr.unpack"|"Data.un_constr", [Var(x)])`.
    fn extract_unpack_subject(expr: &PseudoExpr) -> Option<Binder> {
        if let PseudoExpr::BuiltinCall { name, args } = expr
            && (*name == crate::BuiltinId::ConstrUnpack || *name == crate::BuiltinId::DataUnConstr)
            && args.len() == 1
            && let PseudoExpr::Var { name: ref vn, id } = args[0]
        {
            return Some(Binder::new(
                vn.clone(),
                id.unwrap_or_else(VarId::fresh_compat_placeholder),
            ));
        }
        None
    }

    impl ExprFolder for ExpectResolver {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
            // Reconstruct the Apply node first, then inspect it
            let node = PseudoExpr::Apply {
                function: PBox::new(function),
                args: args.into(),
            };

            // Check if this is `expect!(Constr.unpack(x).fst == N, body)`
            if let Some((tag, subject_name, body)) = try_extract_expect_unpack(&node) {
                // Scan the body for field accesses on the same subject
                let mut indices = std::collections::BTreeSet::new();
                scan_field_indices(body, subject_name.as_str(), &mut indices);

                // Name field binders from the schema when the subject is a
                // known ContextType and the version is known, tagging them
                // `VarKind::CardanoContext` so `assign_names` keeps it.
                let ctx_type = self.version.and_then(|_| {
                    crate::decompile::simplify::postprocess::ContextType::from_display_name(
                        subject_name.as_str(),
                    )
                });
                let field_binders: Vec<Binder> = indices
                    .iter()
                    .next_back()
                    .map(|max_field| {
                        (0..=*max_field)
                            .map(|i| {
                                let semantic = ctx_type.zip(self.version).and_then(|(t, v)| {
                                    crate::decompile::simplify::postprocess::context_field_at(
                                        t, i, v,
                                    )
                                });
                                let name = match semantic {
                                    Some(field) => field.display_name().to_string(),
                                    None => format!("field_{}", i),
                                };
                                Binder::new(name, VarId::fresh_binding())
                            })
                            .collect()
                    })
                    .unwrap_or_default();

                // Rewrite the body: replace field accesses with field_N vars
                let new_body = if !indices.is_empty() {
                    rewrite_field_accesses(body.clone(), subject_name.as_str(), &field_binders)
                } else {
                    body.clone()
                };

                // The wildcard `-> fail` arm makes the pretty printer's expect sugar
                // render this as `expect Constr<tag>(field_0, ...) = subject_name`.
                let arity = field_binders.len();
                return PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var_with_id(
                        subject_name.as_str(),
                        subject_name.id,
                    )),
                    subject_name: Some(subject_name.clone()),
                    clauses: vec![
                        WhenClause {
                            pattern: WhenPattern::constructor(
                                ConstructorShape::unknown_data(tag, arity),
                                field_binders,
                            ),
                            guard: None,
                            body: new_body,
                        },
                        WhenClause {
                            pattern: WhenPattern::Wildcard,
                            guard: None,
                            body: PseudoExpr::Error {
                                message: Some("expect".to_string()),
                            },
                        },
                    ],
                };
            }

            node
        }
    }

    ExpectResolver { version }.fold(expr)
}
