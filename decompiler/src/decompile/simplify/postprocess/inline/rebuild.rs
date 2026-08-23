use crate::builtins::BuiltinId;
use crate::decompile::TypeHintId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;

fn pop_n_results(results: &mut Vec<PseudoExpr>, len: usize) -> Vec<PseudoExpr> {
    let mut items = Vec::with_capacity(len);
    for _ in 0..len {
        items.push(pop_result(results));
    }
    items.reverse();
    items
}

pub(super) fn pop_result(results: &mut Vec<PseudoExpr>) -> PseudoExpr {
    results
        .pop()
        .expect("resolve_inline_field_accesses: result stack underflow")
}

pub(super) fn rebuild_apply_from_results(
    results: &mut Vec<PseudoExpr>,
    args_len: usize,
) -> PseudoExpr {
    let args = pop_n_results(results, args_len);
    let function = pop_result(results);
    PseudoExpr::Apply {
        function: PBox::new(function),
        args: args.into(),
    }
}

pub(super) fn rebuild_if_from_results(results: &mut Vec<PseudoExpr>) -> PseudoExpr {
    let else_branch = pop_result(results);
    let then_branch = pop_result(results);
    let condition = pop_result(results);
    PseudoExpr::If {
        condition: PBox::new(condition),
        then_branch: PBox::new(then_branch),
        else_branch: PBox::new(else_branch),
    }
}

pub(super) fn rebuild_builtin_call_from_results(
    results: &mut Vec<PseudoExpr>,
    name: BuiltinId,
    args_len: usize,
) -> PseudoExpr {
    let args = pop_n_results(results, args_len);
    PseudoExpr::BuiltinCall {
        name,
        args: args.into(),
    }
}

pub(super) fn rebuild_list_from_results(
    results: &mut Vec<PseudoExpr>,
    elements_len: usize,
    has_tail: bool,
) -> PseudoExpr {
    let tail = if has_tail {
        Some(PBox::new(pop_result(results)))
    } else {
        None
    };
    let elements = pop_n_results(results, elements_len);

    PseudoExpr::List {
        elements: elements.into(),
        tail,
    }
}

pub(super) fn rebuild_constr_from_results(
    results: &mut Vec<PseudoExpr>,
    type_hint: Option<TypeHintId>,
    tag: usize,
    fields_len: usize,
    shape: ConstructorShape,
) -> PseudoExpr {
    let fields = pop_n_results(results, fields_len);
    PseudoExpr::Constr {
        type_hint,
        tag,
        fields: fields.into(),
        shape,
    }
}

pub(super) fn rebuild_tuple_from_results(results: &mut Vec<PseudoExpr>, len: usize) -> PseudoExpr {
    PseudoExpr::Tuple((pop_n_results(results, len)).into())
}

pub(super) fn rebuild_field_access_from_results(
    results: &mut Vec<PseudoExpr>,
    selector: FieldSelector,
) -> PseudoExpr {
    let record = pop_result(results);
    PseudoExpr::field_access_typed(record, selector)
}

pub(super) fn rebuild_force_from_results(results: &mut Vec<PseudoExpr>) -> PseudoExpr {
    let inner = pop_result(results);
    PseudoExpr::Force(PBox::new(inner))
}

pub(super) fn rebuild_delay_from_results(results: &mut Vec<PseudoExpr>) -> PseudoExpr {
    let inner = pop_result(results);
    PseudoExpr::Delay(PBox::new(inner))
}

pub(super) fn rebuild_lambda_from_results(
    results: &mut Vec<PseudoExpr>,
    params: Vec<Binder>,
) -> PseudoExpr {
    let body = pop_result(results);
    PseudoExpr::Lambda {
        params,
        body: PBox::new(body),
    }
}

pub(super) fn rebuild_recfn_from_results(
    results: &mut Vec<PseudoExpr>,
    name: Binder,
    params: Vec<Binder>,
) -> PseudoExpr {
    let body = pop_result(results);
    PseudoExpr::RecFn {
        name,
        params,
        body: PBox::new(body),
    }
}

pub(super) fn rebuild_trace_from_results(results: &mut Vec<PseudoExpr>) -> PseudoExpr {
    let value = pop_result(results);
    let message = pop_result(results);
    PseudoExpr::Trace {
        message: PBox::new(message),
        value: PBox::new(value),
    }
}

pub(super) fn rebuild_pair_from_results(results: &mut Vec<PseudoExpr>) -> PseudoExpr {
    let second = pop_result(results);
    let first = pop_result(results);
    PseudoExpr::Pair(PBox::new(first), PBox::new(second))
}

pub(super) fn rebuild_when_from_results(
    results: &mut Vec<PseudoExpr>,
    subject: PseudoExpr,
    subject_name: Option<Binder>,
    clauses: Vec<(WhenPattern, bool)>,
) -> PseudoExpr {
    let mut rebuilt_clauses = Vec::with_capacity(clauses.len());
    for (pattern, has_guard) in clauses.into_iter().rev() {
        let body = pop_result(results);
        let guard = if has_guard {
            Some(pop_result(results))
        } else {
            None
        };
        rebuilt_clauses.push(WhenClause {
            pattern,
            guard,
            body,
        });
    }
    rebuilt_clauses.reverse();

    PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name,
        clauses: rebuilt_clauses,
    }
}
