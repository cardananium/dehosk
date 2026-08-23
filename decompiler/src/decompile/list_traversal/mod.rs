use crate::BuiltinId;
use crate::pseudo::ast::PseudoExpr;

// Builtin name aliases collapse to a small variant set:
//
//   "List.head" | "head_list" → ListHead
//   "List.tail" | "tail_list" → ListTail
//   "List.cons" → ListCons
//   "cons_list" | "mk_cons" | "List.prepend" → ListPrepend
//
// The `Var { name, .. }` arms below cover a builtin looked up by name in a
// place not yet canonicalised into `BuiltinCall`, so they compare the strings
// rather than a `BuiltinId`.

#[cfg(test)]
pub(crate) fn list_head_argument(expr: &PseudoExpr) -> Option<&PseudoExpr> {
    match expr {
        PseudoExpr::BuiltinCall { name, args }
            if *name == BuiltinId::ListHead && args.len() == 1 =>
        {
            Some(&args[0])
        }
        PseudoExpr::Apply { function, args } if args.len() == 1 => match function.as_ref() {
            PseudoExpr::Var { name, .. } if *name == "List.head" || *name == "head_list" => {
                Some(&args[0])
            }
            PseudoExpr::BuiltinCall {
                name,
                args: builtin_args,
            } if *name == BuiltinId::ListHead && builtin_args.is_empty() => Some(&args[0]),
            _ => None,
        },
        _ => None,
    }
}

pub(crate) fn list_tail_argument(expr: &PseudoExpr) -> Option<&PseudoExpr> {
    match expr {
        PseudoExpr::BuiltinCall { name, args }
            if *name == BuiltinId::ListTail && args.len() == 1 =>
        {
            Some(&args[0])
        }
        PseudoExpr::Apply { function, args } if args.len() == 1 => match function.as_ref() {
            PseudoExpr::Var { name, .. } if *name == "List.tail" || *name == "tail_list" => {
                Some(&args[0])
            }
            PseudoExpr::BuiltinCall {
                name,
                args: builtin_args,
            } if *name == BuiltinId::ListTail && builtin_args.is_empty() => Some(&args[0]),
            _ => None,
        },
        _ => None,
    }
}

fn into_list_tail_argument(expr: PseudoExpr) -> Result<PseudoExpr, PseudoExpr> {
    match expr {
        PseudoExpr::BuiltinCall { name, mut args }
            if name == BuiltinId::ListTail && args.len() == 1 =>
        {
            Ok(args.pop().expect("List.tail checked single arg"))
        }
        PseudoExpr::BuiltinCall { name, args } => Err(PseudoExpr::BuiltinCall { name, args }),
        PseudoExpr::Apply { function, mut args } if args.len() == 1 => {
            let is_tail = match function.as_ref() {
                PseudoExpr::Var { name, .. } => name == "List.tail" || name == "tail_list",
                PseudoExpr::BuiltinCall {
                    name,
                    args: builtin_args,
                } => *name == BuiltinId::ListTail && builtin_args.is_empty(),
                _ => false,
            };
            if is_tail {
                Ok(args.pop().expect("List.tail Apply checked single arg"))
            } else {
                Err(PseudoExpr::Apply { function, args })
            }
        }
        PseudoExpr::Apply { function, args } => Err(PseudoExpr::Apply { function, args }),
        other => Err(other),
    }
}

fn is_list_cons_builtin(id: BuiltinId) -> bool {
    matches!(id, BuiltinId::ListCons | BuiltinId::ListPrepend)
}

pub(crate) fn list_cons_parts(expr: &PseudoExpr) -> Option<(&PseudoExpr, &PseudoExpr)> {
    match expr {
        PseudoExpr::BuiltinCall { name, args }
            if is_list_cons_builtin(*name) && args.len() == 2 =>
        {
            Some((&args[0], &args[1]))
        }
        PseudoExpr::Apply { function, args } if args.len() == 2 => match function.as_ref() {
            PseudoExpr::Var { name, .. }
                if *name == "List.cons" || *name == "cons_list" || *name == "mk_cons" =>
            {
                Some((&args[0], &args[1]))
            }
            PseudoExpr::BuiltinCall {
                name,
                args: builtin_args,
            } if is_list_cons_builtin(*name) && builtin_args.is_empty() => {
                Some((&args[0], &args[1]))
            }
            _ => None,
        },
        PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Cons,
            left,
            right,
        } => Some((left.as_ref(), right.as_ref())),
        PseudoExpr::List {
            elements,
            tail: Some(tail),
        } if elements.len() == 1 => Some((&elements[0], tail.as_ref())),
        _ => None,
    }
}

pub(crate) fn list_literal_parts(
    expr: &PseudoExpr,
) -> Option<(Vec<PseudoExpr>, Option<PseudoExpr>)> {
    enum Frame<'a> {
        // `List { elements, tail: Some(tail_expr) }`: only merges if the
        // recursive parse of `tail_expr` resolves to a *clean* (tail =
        // None) list; otherwise `tail_expr` itself becomes the opaque
        // tail, discarding whatever the recursive parse produced.
        ListTail(Vec<PseudoExpr>, &'a PseudoExpr),
        // A single cons cell (`Constr` tag 1, or a cons-shaped builtin
        // call): the head is prepended unconditionally, and a failed
        // recursive parse propagates as failure.
        Cons(PseudoExpr),
        Terminal(Vec<PseudoExpr>),
        Fail,
    }

    let mut frames = Vec::new();
    let mut current = expr;
    loop {
        match current {
            PseudoExpr::List { elements, tail } => match tail.as_deref() {
                None => {
                    frames.push(Frame::Terminal((elements.clone()).into_vec()));
                    break;
                }
                Some(tail_expr) => {
                    frames.push(Frame::ListTail((elements.clone()).into_vec(), tail_expr));
                    current = tail_expr;
                }
            },
            PseudoExpr::Constr { tag: 0, fields, .. } if fields.is_empty() => {
                frames.push(Frame::Terminal(vec![]));
                break;
            }
            PseudoExpr::Bool(true) => {
                frames.push(Frame::Terminal(vec![]));
                break;
            }
            PseudoExpr::Constr { tag: 1, fields, .. } if fields.len() == 2 => {
                frames.push(Frame::Cons(fields[0].clone()));
                current = &fields[1];
            }
            other => match list_cons_parts(other) {
                Some((head, tail)) => {
                    frames.push(Frame::Cons(head.clone()));
                    current = tail;
                }
                None => {
                    frames.push(Frame::Fail);
                    break;
                }
            },
        }
    }

    let mut result: Option<(Vec<PseudoExpr>, Option<PseudoExpr>)> = match frames
        .pop()
        .expect("descent always pushes at least one frame")
    {
        Frame::Terminal(elements) => Some((elements, None)),
        Frame::Fail => None,
        Frame::ListTail(..) | Frame::Cons(..) => {
            unreachable!("descent only stops after pushing Terminal or Fail")
        }
    };

    while let Some(frame) = frames.pop() {
        result = match frame {
            Frame::Cons(head) => result.map(|(mut elements, tail)| {
                elements.insert(0, head);
                (elements, tail)
            }),
            Frame::ListTail(pre_elements, tail_expr) => match result {
                Some((mut tail_elements, None)) => {
                    let mut elements = pre_elements;
                    elements.append(&mut tail_elements);
                    Some((elements, None))
                }
                _ => Some((pre_elements, Some(tail_expr.clone()))),
            },
            Frame::Terminal(_) | Frame::Fail => {
                unreachable!("Terminal/Fail is only ever the deepest frame")
            }
        };
    }

    result
}

pub(crate) fn is_list_tail_call(expr: &PseudoExpr) -> bool {
    list_tail_argument(expr).is_some()
}

pub(crate) fn is_list_tail_of_var(expr: &PseudoExpr, var_name: &str) -> bool {
    match list_tail_argument(expr) {
        Some(PseudoExpr::Var { name, .. }) => name == var_name,
        _ => false,
    }
}

pub(crate) fn list_subject_and_tail_depth(expr: &PseudoExpr) -> (PseudoExpr, usize) {
    let mut depth = 0usize;
    let mut current = expr;

    while let Some(inner) = list_tail_argument(current) {
        depth += 1;
        current = inner;
    }

    (current.clone(), depth)
}

pub(crate) fn list_subject_and_tail_depth_owned(expr: PseudoExpr) -> (PseudoExpr, usize) {
    let mut depth = 0usize;
    let mut current = expr;

    loop {
        match into_list_tail_argument(current) {
            Ok(inner) => {
                depth += 1;
                current = inner;
            }
            Err(current) => return (current, depth),
        }
    }
}

#[cfg(test)]
mod tests;
