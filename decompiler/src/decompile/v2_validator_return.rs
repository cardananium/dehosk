//! V1/V2 validators return `Bool`, not `Unit`.
//!
//! A Plutus V1 or V2 validator passes if and only if it returns `True`.
//! A V3 validator returns `Unit` (rendered as `Void`) and signals
//! failure with `fail`, not `False`.
//!
//! The decompiler can leave a tail-position `PseudoExpr::Unit` in a
//! V1/V2 validator body — `if cond { Void } else { expect … }` — where
//! the UPLC used `()` as the "this branch succeeded" sentinel and the
//! simplifier never derived a Bool shape.
//!
//! This pass walks the validator-entry body in *tail position only* and
//! rewrites tail `Unit` to `Bool(true)`. Argument positions, nested
//! closure bodies, and other non-tail positions keep their `Void`, which
//! is still a legitimate value to pass to a callback or bind to a name.
//!
//! The pass is a no-op when `script_version` is `None` (the required
//! return type is unknown) or `Some(PlutusV3)`. Otherwise it rewrites
//! the lambda bound by the `VarKind::ValidatorEntry` binder — or, if no
//! wrap ran and the AST is a bare Lambda, that Lambda's body.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::decompile::ScriptVersion;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;

/// Entry point: for V1/V2, find the Let whose binder is annotated
/// `VarKind::ValidatorEntry` and rewrite tail-position `Unit` in its
/// lambda body. The marker is the annotation, never the binder's name.
pub(crate) fn lower_v2_tail_unit_to_true(
    expr: PseudoExpr,
    script_version: Option<ScriptVersion>,
    kind_annotations: &HashMap<VarId, VarKind>,
) -> PseudoExpr {
    let should_lower = matches!(
        script_version,
        Some(ScriptVersion::PlutusV1) | Some(ScriptVersion::PlutusV2)
    );
    if !should_lower {
        return expr;
    }
    rewrite_validator_entry(expr, kind_annotations)
}

/// Walk the outer `Let` chain and apply the tail-rewrite to the
/// lambda bound by the `VarKind::ValidatorEntry` binder. Helper
/// bodies are not descended into: their tail position belongs to
/// that helper's return type, not the validator's.
fn rewrite_validator_entry(
    expr: PseudoExpr,
    kind_annotations: &HashMap<VarId, VarKind>,
) -> PseudoExpr {
    let mut lets = Vec::new();
    let mut current = expr;
    let terminal = loop {
        match current {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                lets.push((name, id, value));
                current = body.into_inner();
            }
            other => break other,
        }
    };
    // Defensive: with no wrap step, the top of the AST is the lambda.
    let mut result = match terminal {
        PseudoExpr::Lambda { params, body } => PseudoExpr::Lambda {
            params,
            body: PBox::new(walk_tail(body.into_inner())),
        },
        other => other,
    };
    for (name, id, value) in lets.into_iter().rev() {
        let is_validator_entry = id
            .get()
            .and_then(|vid| kind_annotations.get(&vid))
            .is_some_and(|kind| matches!(kind, VarKind::ValidatorEntry));
        let value = if is_validator_entry {
            rewrite_lambda_body_in_tail(value.into_inner())
        } else {
            value.into_inner()
        };
        result = PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(result),
        };
    }
    result
}

/// Rewrite a `Lambda` body in tail position; pass others through.
fn rewrite_lambda_body_in_tail(expr: PseudoExpr) -> PseudoExpr {
    if let PseudoExpr::Lambda { params, body } = expr {
        PseudoExpr::Lambda {
            params,
            body: PBox::new(walk_tail(body.into_inner())),
        }
    } else {
        expr
    }
}

enum TailFrame {
    Let {
        name: String,
        id: Option<VarId>,
        value: PBox,
    },
    IfThen {
        condition: PBox,
        else_branch: PseudoExpr,
    },
    IfElse {
        condition: PBox,
        then_branch: PseudoExpr,
    },
    WhenClause {
        subject: PBox,
        subject_name: Option<Binder>,
        pattern: WhenPattern,
        guard: Option<PseudoExpr>,
        done: Vec<WhenClause>,
        remaining: std::vec::IntoIter<WhenClause>,
    },
    Trace {
        message: PBox,
    },
    SeqTail {
        function: PBox,
        stmt: PseudoExpr,
    },
    ExpectTail {
        function: PBox,
        cond: PseudoExpr,
        msg: Option<PseudoExpr>,
    },
}

/// Walk `expr` in tail position: `Unit` — and a trailing identity
/// `fn(x) { x }` — becomes `Bool(true)`. Recurses through constructs
/// that preserve tail position (`Let` body, `If` branches, `When`
/// clause bodies, `Trace` value, `Seq` and `expect!` continuations)
/// and leaves every other shape unchanged.
fn walk_tail(expr: PseudoExpr) -> PseudoExpr {
    let mut frames: Vec<TailFrame> = Vec::new();
    let mut current = expr;

    'descend: loop {
        // Follow the tail chain down, pushing a frame per level, until
        // hitting a shape that doesn't preserve tail position further.
        let mut value = loop {
            current = match current {
                PseudoExpr::Unit => break PseudoExpr::Bool(true),
                PseudoExpr::Lambda {
                    ref params,
                    ref body,
                } if params.len() == 1
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Var { id: Some(body_id), .. }
                            if *body_id == params[0].var_id()
                    ) =>
                {
                    break PseudoExpr::Bool(true);
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    frames.push(TailFrame::Let { name, id, value });
                    body.into_inner()
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    frames.push(TailFrame::IfThen {
                        condition,
                        else_branch: else_branch.into_inner(),
                    });
                    then_branch.into_inner()
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let mut remaining = clauses.into_iter();
                    match remaining.next() {
                        Some(first) => {
                            frames.push(TailFrame::WhenClause {
                                subject,
                                subject_name,
                                pattern: first.pattern,
                                guard: first.guard,
                                done: Vec::new(),
                                remaining,
                            });
                            first.body
                        }
                        // No clauses: nothing to descend into.
                        None => {
                            break PseudoExpr::When {
                                subject,
                                subject_name,
                                clauses: vec![],
                            };
                        }
                    }
                }
                // `trace msg val` returns `val`: `value` is in tail
                // position, `message` is only evaluated for its log
                // side-effect.
                PseudoExpr::Trace { message, value } => {
                    frames.push(TailFrame::Trace { message });
                    value.into_inner()
                }
                // `BuiltinCall::Seq` lowers `stmt1; stmt2`: args[0] is
                // the statement (not tail), args[1] the tail expression.
                PseudoExpr::Apply {
                    ref function,
                    ref args,
                } if args.len() == 2
                    && matches!(
                        function.as_ref(),
                        PseudoExpr::BuiltinCall { name, args: builtin_args }
                            if *name == crate::BuiltinId::Seq && builtin_args.is_empty()
                    ) =>
                {
                    let PseudoExpr::Apply { function, args } = current else {
                        unreachable!()
                    };
                    let mut args = args;
                    let tail = args.pop().expect("seq apply has 2 args");
                    let stmt = args.pop().expect("seq apply has 2 args");
                    frames.push(TailFrame::SeqTail { function, stmt });
                    tail
                }
                // `expect!` chain: `Apply { function: Var("expect!"),
                // args: [cond, continuation, ?msg] }`. Only the
                // continuation is tail. The sentinel is matched by
                // name; its `id` may be `None` or a compat placeholder.
                PseudoExpr::Apply {
                    ref function,
                    ref args,
                } if (args.len() == 2 || args.len() == 3)
                    && matches!(
                        function.as_ref(),
                        PseudoExpr::Var { name, .. } if name.as_str() == "expect!"
                    ) =>
                {
                    let PseudoExpr::Apply { function, args } = current else {
                        unreachable!()
                    };
                    let mut args = args.into_iter();
                    let cond = args.next().expect("expect! has cond");
                    let continuation = args.next().expect("expect! has continuation");
                    let msg = args.next();
                    frames.push(TailFrame::ExpectTail {
                        function,
                        cond,
                        msg,
                    });
                    continuation
                }
                // No other shape preserves tail position — Apply,
                // Lambda, BuiltinCall, Delay/Force, Var, primitives:
                // unchanged.
                other => break other,
            };
        };

        // Ascend: pop frames, filling each hole with `value`. `IfThen`
        // and `WhenClause` still owe another tail-position descent, so
        // they push a continuation frame and jump back to `'descend`.
        loop {
            match frames.pop() {
                None => return value,
                Some(TailFrame::Let {
                    name,
                    id,
                    value: bound,
                }) => {
                    value = PseudoExpr::Let {
                        name,
                        id,
                        value: bound,
                        body: PBox::new(value),
                    };
                }
                Some(TailFrame::IfThen {
                    condition,
                    else_branch,
                }) => {
                    frames.push(TailFrame::IfElse {
                        condition,
                        then_branch: value,
                    });
                    current = else_branch;
                    continue 'descend;
                }
                Some(TailFrame::IfElse {
                    condition,
                    then_branch,
                }) => {
                    value = PseudoExpr::If {
                        condition,
                        then_branch: PBox::new(then_branch),
                        else_branch: PBox::new(value),
                    };
                }
                Some(TailFrame::WhenClause {
                    subject,
                    subject_name,
                    pattern,
                    guard,
                    mut done,
                    mut remaining,
                }) => {
                    done.push(WhenClause {
                        pattern,
                        guard, // guards are bool predicates already
                        body: value,
                    });
                    match remaining.next() {
                        Some(next) => {
                            frames.push(TailFrame::WhenClause {
                                subject,
                                subject_name,
                                pattern: next.pattern,
                                guard: next.guard,
                                done,
                                remaining,
                            });
                            current = next.body;
                            continue 'descend;
                        }
                        None => {
                            value = PseudoExpr::When {
                                subject,
                                subject_name,
                                clauses: done,
                            };
                        }
                    }
                }
                Some(TailFrame::Trace { message }) => {
                    value = PseudoExpr::Trace {
                        message,
                        value: PBox::new(value),
                    };
                }
                Some(TailFrame::SeqTail { function, stmt }) => {
                    value = PseudoExpr::Apply {
                        function,
                        args: vec![stmt, value].into(),
                    };
                }
                Some(TailFrame::ExpectTail {
                    function,
                    cond,
                    msg,
                }) => {
                    let mut new_args = vec![cond, value];
                    if let Some(msg) = msg {
                        new_args.push(msg);
                    }
                    value = PseudoExpr::Apply {
                        function,
                        args: new_args.into(),
                    };
                }
            }
        }
    }
}

#[cfg(test)]
mod tests;
