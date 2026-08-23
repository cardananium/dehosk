use crate::decompile::constructor_data::{
    extract_standard_option_some_fields, is_bool_false_like, is_standard_option_none_candidate,
    is_standard_option_some_candidate, make_standard_option_none, make_standard_option_some,
};
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

/// Fix Bool/Option confusion: `Option.None` and `Bool.True` share the same
/// empty constructor shape, while `Option.Some` carries payload fields.
///
/// An if/else with one branch `Bool(true)` (0-field, tag 1) and the other
/// `Constr<0>(value)` (1+ fields, tag 0) is really `None` / `Some(value)`,
/// as is the recursive `[] -> True; [h,..t] -> if ... { Constr<0>(...) } else { recurse }`.
pub(crate) fn fix_bool_option_confusion(expr: PseudoExpr) -> PseudoExpr {
    struct BoolOptionFixer;

    fn is_none_candidate(expr: &PseudoExpr) -> bool {
        is_standard_option_none_candidate(expr)
    }

    fn is_false_none_candidate(expr: &PseudoExpr) -> bool {
        is_bool_false_like(expr)
    }

    fn is_some_candidate(expr: &PseudoExpr) -> bool {
        is_standard_option_some_candidate(expr)
    }

    fn has_option_confusion(clauses: &[WhenClause]) -> bool {
        // Disproof veto: if any clause body leaves a BARE constructor in a
        // result/tail position that `fix_clause_body` cannot rewrite into
        // `Some`/`None`, this `when` is a genuine 3+-constructor sum, not an
        // Option — relabeling two coincidentally Option-shaped arms while a raw
        // ctor arm stays produces a non-typecheckable Option value.
        if clauses
            .iter()
            .any(|c| body_has_option_disproof_witness(&c.body))
        {
            return false;
        }

        let has_none = clauses.iter().any(|c| is_none_candidate(&c.body));
        let has_false_none = clauses.iter().any(|c| is_false_none_candidate(&c.body));
        let has_some = clauses.iter().any(|c| is_some_candidate(&c.body));
        if (has_none || has_false_none) && has_some {
            return true;
        }
        if has_none || has_false_none {
            let has_nested_some = clauses.iter().any(|c| {
                body_contains_some_candidate(&c.body) || body_contains_named_option(&c.body)
            });
            if has_nested_some {
                return true;
            }
        }
        false
    }

    /// A genuine Option-returning `when` can never have an arm whose tail is a
    /// bare constructor that is neither a `Some`-candidate (tag 0 / arity 1)
    /// nor a `None`-candidate (tag 1 / nullary, or `Bool(true)`) nor a `fail` /
    /// `Error` / `Ok`. Such a constructor is a disproof witness: the subject is
    /// a distinct ADT that merely shares Option's shape on two of its arms.
    ///
    /// Descends ONLY where `fix_clause_body` rewrites — `If` then/else, `Let`
    /// body, `When` arms — never into conditions, `Apply` args, or `Let`
    /// values, which are not result positions.
    fn body_has_option_disproof_witness(expr: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            // Anything `fix_clause_body` recognizes as None/Some (including
            // `Bool(true)`/`Bool(false)`-none) is not a witness, and is not
            // descended into further.
            if is_none_candidate(current)
                || is_false_none_candidate(current)
                || is_some_candidate(current)
            {
                continue;
            }

            match current {
                PseudoExpr::Constr {
                    tag, fields, shape, ..
                } => {
                    // `Error(_)` / `Ok(_)` (Result) are legitimate non-Option
                    // tails that a Some/None recovery tolerates; never
                    // witnesses.
                    if matches!(
                        shape,
                        ConstructorShape::Known(KnownConstructor::Error | KnownConstructor::Ok)
                    ) {
                        continue;
                    }
                    // Shapes Option cannot produce:
                    //   tag >= 2                    -> impossible for Option
                    //   tag == 0 && arity != 1      -> not `Some(x)`
                    //   tag == 1 && non-nullary     -> not `None`
                    if *tag >= 2
                        || (*tag == 0 && fields.len() != 1)
                        || (*tag == 1 && !fields.is_empty())
                    {
                        return true;
                    }
                }
                // Descends ONLY where `fix_clause_body` rewrites — `If`
                // then/else, `Let` body, `When` arms — never into
                // conditions, `Apply` args, or `Let` values, which are not
                // result positions.
                PseudoExpr::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    pending.push(then_branch);
                    pending.push(else_branch);
                }
                PseudoExpr::Let { body, .. } => pending.push(body),
                PseudoExpr::When { clauses, .. } => {
                    pending.extend(clauses.iter().map(|c| &c.body));
                }
                _ => {}
            }
        }
        false
    }

    fn body_contains_some_candidate(expr: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            if is_some_candidate(current) {
                return true;
            }
            match current {
                PseudoExpr::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    pending.push(then_branch);
                    pending.push(else_branch);
                }
                PseudoExpr::Let { value, body, .. } => {
                    pending.push(value);
                    pending.push(body);
                }
                _ => {}
            }
        }
        false
    }

    fn body_contains_named_option(expr: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Constr {
                    shape:
                        ConstructorShape::Known(KnownConstructor::Some)
                        | ConstructorShape::Known(KnownConstructor::None),
                    ..
                } => return true,
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
                    pending.extend(clauses.iter().map(|c| &c.body));
                }
                PseudoExpr::Apply { function, args } => {
                    pending.push(function);
                    pending.extend(args.iter());
                }
                PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                    pending.push(body);
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(left);
                    pending.push(right);
                }
                _ => {}
            }
        }
        false
    }

    fn fix_clause_body(root: PseudoExpr) -> PseudoExpr {
        /// One `when` in progress: its untouched subject/pattern context,
        /// the clauses still to fix, and the clauses already rebuilt.
        struct WhenBuild {
            subject: PBox,
            subject_name: Option<Binder>,
            remaining: std::vec::IntoIter<WhenClause>,
            finished: Vec<WhenClause>,
        }

        enum Step {
            Enter(PseudoExpr),
            LetPost {
                name: String,
                id: Option<VarId>,
            },
            IfPost {
                condition: PBox,
            },
            WhenNext(WhenBuild),
            WhenClauseDone {
                build: WhenBuild,
                pattern: WhenPattern,
                has_guard: bool,
            },
        }

        let mut stack = vec![Step::Enter(root)];
        let mut done: Vec<PseudoExpr> = Vec::new();

        while let Some(step) = stack.pop() {
            match step {
                Step::Enter(expr) => {
                    if is_none_candidate(&expr) || is_false_none_candidate(&expr) {
                        done.push(make_standard_option_none());
                        continue;
                    }
                    if is_some_candidate(&expr) {
                        done.push(
                            extract_standard_option_some_fields(&expr)
                                .map(make_standard_option_some)
                                .unwrap_or(expr),
                        );
                        continue;
                    }
                    match expr {
                        PseudoExpr::Let {
                            name,
                            id,
                            value,
                            body,
                        } => {
                            stack.push(Step::LetPost { name, id });
                            stack.push(Step::Enter(body.into_inner()));
                            stack.push(Step::Enter(value.into_inner()));
                        }
                        PseudoExpr::If {
                            condition,
                            then_branch,
                            else_branch,
                        } => {
                            stack.push(Step::IfPost { condition });
                            stack.push(Step::Enter(else_branch.into_inner()));
                            stack.push(Step::Enter(then_branch.into_inner()));
                        }
                        PseudoExpr::When {
                            subject,
                            subject_name,
                            clauses,
                        } => {
                            stack.push(Step::WhenNext(WhenBuild {
                                subject,
                                subject_name,
                                remaining: clauses.into_iter(),
                                finished: Vec::new(),
                            }));
                        }
                        // Any other node kind is left untouched.
                        other => done.push(other),
                    }
                }
                Step::LetPost { name, id } => {
                    let body = done.pop().expect("let body");
                    let value = done.pop().expect("let value");
                    done.push(PseudoExpr::Let {
                        name,
                        id,
                        value: PBox::new(value),
                        body: PBox::new(body),
                    });
                }
                Step::IfPost { condition } => {
                    let else_branch = done.pop().expect("if else");
                    let then_branch = done.pop().expect("if then");
                    done.push(PseudoExpr::If {
                        condition,
                        then_branch: PBox::new(then_branch),
                        else_branch: PBox::new(else_branch),
                    });
                }
                Step::WhenNext(mut build) => match build.remaining.next() {
                    None => done.push(PseudoExpr::When {
                        subject: build.subject,
                        subject_name: build.subject_name,
                        clauses: build.finished,
                    }),
                    Some(WhenClause {
                        pattern,
                        guard,
                        body,
                    }) => {
                        let has_guard = guard.is_some();
                        stack.push(Step::WhenClauseDone {
                            build,
                            pattern,
                            has_guard,
                        });
                        stack.push(Step::Enter(body));
                        if let Some(g) = guard {
                            stack.push(Step::Enter(g));
                        }
                    }
                },
                Step::WhenClauseDone {
                    mut build,
                    pattern,
                    has_guard,
                } => {
                    let body = done.pop().expect("clause body");
                    let guard = if has_guard {
                        Some(done.pop().expect("clause guard"))
                    } else {
                        None
                    };
                    build.finished.push(WhenClause {
                        pattern,
                        guard,
                        body,
                    });
                    stack.push(Step::WhenNext(build));
                }
            }
        }

        done.pop().expect("fix_clause_body result")
    }

    impl ExprFolder for BoolOptionFixer {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_if(
            &mut self,
            condition: PseudoExpr,
            then_branch: PseudoExpr,
            else_branch: PseudoExpr,
        ) -> PseudoExpr {
            if (is_none_candidate(&then_branch) || is_false_none_candidate(&then_branch))
                && is_some_candidate(&else_branch)
            {
                let new_else = extract_standard_option_some_fields(&else_branch)
                    .map(make_standard_option_some)
                    .unwrap_or(else_branch);
                return PseudoExpr::If {
                    condition: PBox::new(condition),
                    then_branch: PBox::new(make_standard_option_none()),
                    else_branch: PBox::new(new_else),
                };
            }

            if is_some_candidate(&then_branch)
                && (is_none_candidate(&else_branch) || is_false_none_candidate(&else_branch))
            {
                let new_then = extract_standard_option_some_fields(&then_branch)
                    .map(make_standard_option_some)
                    .unwrap_or(then_branch);
                return PseudoExpr::If {
                    condition: PBox::new(condition),
                    then_branch: PBox::new(new_then),
                    else_branch: PBox::new(make_standard_option_none()),
                };
            }

            PseudoExpr::If {
                condition: PBox::new(condition),
                then_branch: PBox::new(then_branch),
                else_branch: PBox::new(else_branch),
            }
        }

        fn post_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            if has_option_confusion(&clauses) {
                let fixed_clauses = clauses
                    .into_iter()
                    .map(|c| WhenClause {
                        pattern: c.pattern,
                        guard: c.guard,
                        body: fix_clause_body(c.body),
                    })
                    .collect();
                return PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses: fixed_clauses,
                };
            }

            PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses,
            }
        }
    }

    BoolOptionFixer.fold(expr)
}

#[cfg(test)]
mod tests;
