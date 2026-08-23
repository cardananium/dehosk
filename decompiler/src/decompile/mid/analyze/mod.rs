//! Abstract interpretation pass for MidExpr.
//!
//! Forward analysis propagating AbstractValue through the expression tree:
//! constant propagation, Thunk classification (cosmetic vs. lazy), builtin
//! constant folding, and let-value abstract evaluation into the binding
//! env.

use std::collections::HashMap;

use uplc::ast::{Constant, NamedDeBruijn, Program};
use uplc::builtins::DefaultFunction;
use uplc::machine::cost_model::ExBudget;

use crate::pseudo::abstract_value::{AbstractLiteral, AbstractType, AbstractValue};
use crate::pseudo::mid::expr::{MidExpr, MidLiteral};
use crate::pseudo::var_id::VarId;

/// Abstract interpreter state.
pub(crate) struct Analyzer {
    env: HashMap<VarId, AbstractValue>,
}

impl Analyzer {
    pub(crate) fn new() -> Self {
        Self {
            env: HashMap::new(),
        }
    }

    /// Run analysis on a MidExpr tree, filling annotations in-place.
    ///
    /// `env` scoping is why this is bespoke rather than one of the shared
    /// `rewrite_bottom_up` helpers: the snapshots do not bracket a whole node.
    /// A `Closure` restores after its body, an `If` re-snapshots BETWEEN its two
    /// branches, and a `Trace` snapshots before the message and drops it before
    /// the body — so each save and restore is a step in its own right.
    pub(crate) fn analyze(&mut self, expr: &mut MidExpr) {
        let taken = std::mem::replace(expr, MidExpr::Error { id: expr.id() });
        *expr = self.analyze_owned(taken);
    }

    fn analyze_owned(&mut self, root: MidExpr) -> MidExpr {
        enum Task {
            /// Take the node apart; queue its children and its scope steps.
            Enter(MidExpr),
            /// The `let` value is on the value stack: evaluate it abstractly and
            /// bind it. Deliberately never undone — dropping it would hide the
            /// value from later refs to the same `VarId`.
            BindLet(VarId),
            /// Remember the env, then apply these bindings on top of it.
            Save(Vec<(VarId, AbstractValue)>),
            /// Restore the remembered env but KEEP it, for a sibling that still
            /// needs the same starting point (an `If`'s `else`).
            RestoreKeep,
            /// Restore the remembered env and forget it.
            RestorePop,
            /// Reassemble the node from its children, then annotate it.
            Exit { shell: MidExpr, arity: usize },
        }

        let mut tasks = vec![Task::Enter(root)];
        let mut done: Vec<MidExpr> = Vec::new();
        let mut saved: Vec<HashMap<VarId, AbstractValue>> = Vec::new();

        while let Some(task) = tasks.pop() {
            match task {
                Task::Save(bindings) => {
                    saved.push(self.env.clone());
                    for (var, value) in bindings {
                        self.env.insert(var, value);
                    }
                }
                Task::RestoreKeep => {
                    self.env = saved.last().expect("unbalanced env snapshot").clone();
                }
                Task::RestorePop => {
                    self.env = saved.pop().expect("unbalanced env snapshot");
                }
                Task::BindLet(var) => {
                    let av = self.abstract_eval(done.last().expect("let value"));
                    self.env.insert(var, av);
                }
                Task::Exit { mut shell, arity } => {
                    let at = done.len() - arity;
                    shell.put_children(done.split_off(at));
                    match &mut shell {
                        MidExpr::Thunk { body, cosmetic, .. } => {
                            *cosmetic = is_value_form(body);
                        }
                        MidExpr::Builtin {
                            fun, args, folded, ..
                        } if !args.is_empty() => {
                            *folded = try_fold_builtin(*fun, args);
                        }
                        _ => {}
                    }
                    done.push(shell);
                }
                Task::Enter(mut node) => {
                    // Per-arm binders have to be read before the children are
                    // moved out, since they live on the branch, not the body.
                    let arm_binders: Vec<Vec<(VarId, AbstractValue)>> = match &node {
                        MidExpr::Case { branches, .. } => branches
                            .iter()
                            .map(|b| {
                                b.binders
                                    .iter()
                                    .enumerate()
                                    .map(|(i, binder)| {
                                        (
                                            *binder,
                                            AbstractValue::ConstructorField {
                                                tag: b.tag,
                                                field_index: i,
                                            },
                                        )
                                    })
                                    .collect()
                            })
                            .collect(),
                        _ => Vec::new(),
                    };
                    let let_var = match &node {
                        MidExpr::Let { var, .. } => Some(*var),
                        _ => None,
                    };
                    // Scope work that must happen before ANY child: a lambda's
                    // parameters are unknown at the definition site, so they are
                    // dropped from the env; the snapshot keeps inner `let`
                    // bindings from leaking out past the body.
                    let is_closure = matches!(node, MidExpr::Closure { .. });
                    if let MidExpr::Closure { params, .. } = &node {
                        saved.push(self.env.clone());
                        for p in params {
                            self.env.remove(p);
                        }
                    }
                    let is_case = matches!(node, MidExpr::Case { .. });
                    let is_if = matches!(node, MidExpr::If { .. });
                    let is_trace = matches!(node, MidExpr::Trace { .. });

                    let kids = node.take_children();
                    let arity = kids.len();
                    let mut kids = kids.into_iter();

                    // Built in EXECUTION order, then reversed onto the LIFO stack.
                    let mut plan: Vec<Task> = Vec::new();
                    if is_case {
                        plan.push(Task::Enter(kids.next().expect("case scrutinee")));
                        for binders in arm_binders {
                            plan.push(Task::Save(binders));
                            plan.push(Task::Enter(kids.next().expect("case arm")));
                            plan.push(Task::RestorePop);
                        }
                    } else if is_if {
                        plan.push(Task::Enter(kids.next().expect("if condition")));
                        // Snapshot AFTER the condition: it runs in the enclosing env.
                        plan.push(Task::Save(Vec::new()));
                        plan.push(Task::Enter(kids.next().expect("if then")));
                        plan.push(Task::RestoreKeep);
                        plan.push(Task::Enter(kids.next().expect("if else")));
                        plan.push(Task::RestorePop);
                    } else if is_trace {
                        // Snapshot BEFORE the message so its bindings do not leak
                        // into the body.
                        plan.push(Task::Save(Vec::new()));
                        plan.push(Task::Enter(kids.next().expect("trace message")));
                        plan.push(Task::RestorePop);
                        plan.push(Task::Enter(kids.next().expect("trace body")));
                    } else if let Some(var) = let_var {
                        plan.push(Task::Enter(kids.next().expect("let value")));
                        plan.push(Task::BindLet(var));
                        plan.push(Task::Enter(kids.next().expect("let body")));
                    } else {
                        for kid in kids {
                            plan.push(Task::Enter(kid));
                        }
                        if is_closure {
                            plan.push(Task::RestorePop);
                        }
                    }
                    plan.push(Task::Exit { shell: node, arity });

                    for task in plan.into_iter().rev() {
                        tasks.push(task);
                    }
                }
            }
        }

        debug_assert!(saved.is_empty(), "env snapshots must all be restored");
        debug_assert_eq!(done.len(), 1, "the analyzer must leave one result");
        done.pop().expect("analysis result")
    }

    fn abstract_eval(&self, expr: &MidExpr) -> AbstractValue {
        let mut current = expr;
        loop {
            match current {
                MidExpr::Lit { value, .. } => return literal_to_abstract(value),
                MidExpr::Var { var, .. } => {
                    return self.env.get(var).cloned().unwrap_or(AbstractValue::Unknown);
                }
                MidExpr::Thunk { .. } => return AbstractValue::Thunk,
                MidExpr::Closure { params, .. } => {
                    return AbstractValue::Closure {
                        params: params.clone(),
                    };
                }
                MidExpr::Constr { tag, fields, .. } => {
                    return AbstractValue::Constructor {
                        tag: *tag,
                        arity: fields.len(),
                    };
                }
                MidExpr::Builtin {
                    fun,
                    forces,
                    args,
                    folded,
                    ..
                } => {
                    if let Some(lit) = folded {
                        return literal_to_abstract(lit);
                    }
                    let expected = builtin_arity(*fun);
                    return if args.len() < expected {
                        AbstractValue::BuiltinPartial {
                            fun: *fun,
                            forces: *forces,
                            args_given: args.len(),
                        }
                    } else {
                        builtin_return_type(*fun)
                    };
                }
                MidExpr::If { .. } => return AbstractValue::Unknown,
                MidExpr::Error { .. } => return AbstractValue::Unknown,
                MidExpr::Let { body, .. } => current = body,
                _ => return AbstractValue::Unknown,
            }
        }
    }
}

impl Default for Analyzer {
    fn default() -> Self {
        Self::new()
    }
}

/// Check if an expression is a value-form: already fully evaluated, so
/// Thunk/Force can wrap or unwrap it without changing semantics.
fn is_value_form(expr: &MidExpr) -> bool {
    match expr {
        MidExpr::Lit { .. }
        | MidExpr::Closure { .. }
        | MidExpr::Constr { .. }
        | MidExpr::Var { .. }
        | MidExpr::Error { .. } => true,
        // A builtin with no arguments is a function reference, not a
        // computation, so Thunk(Builtin{args:[]}) is cosmetic.
        MidExpr::Builtin { args, .. } if args.is_empty() => true,
        _ => false,
    }
}

fn literal_to_abstract(lit: &MidLiteral) -> AbstractValue {
    match lit {
        MidLiteral::Integer(n) => AbstractValue::Constant(AbstractLiteral::Integer(n.clone())),
        MidLiteral::ByteString(b) => {
            AbstractValue::Constant(AbstractLiteral::ByteString(b.clone()))
        }
        MidLiteral::String(s) => AbstractValue::Constant(AbstractLiteral::String(s.clone())),
        MidLiteral::Bool(b) => AbstractValue::Constant(AbstractLiteral::Bool(*b)),
        MidLiteral::Unit => AbstractValue::Constant(AbstractLiteral::Unit),
        MidLiteral::Data(_) => AbstractValue::Typed(AbstractType::Data),
        MidLiteral::List(_) => {
            AbstractValue::Typed(AbstractType::List(Box::new(AbstractType::Unknown)))
        }
        MidLiteral::Pair(_, _) => AbstractValue::Typed(AbstractType::Pair(
            Box::new(AbstractType::Unknown),
            Box::new(AbstractType::Unknown),
        )),
        MidLiteral::Bls12_381G1(_) => AbstractValue::Typed(AbstractType::G1Element),
        MidLiteral::Bls12_381G2(_) => AbstractValue::Typed(AbstractType::G2Element),
    }
}

/// If all arguments are known constants, evaluate using the actual UPLC machine.
fn try_fold_builtin(fun: DefaultFunction, args: &[MidExpr]) -> Option<MidLiteral> {
    if !is_safe_to_fold(fun) {
        return None;
    }

    // Check all args are literals
    let lits: Vec<&MidLiteral> = args
        .iter()
        .filter_map(|a| match a {
            MidExpr::Lit { value, .. } => Some(value),
            _ => None,
        })
        .collect();

    if lits.len() != args.len() {
        return None;
    }

    let term = build_builtin_term(fun, &lits)?;
    let program = Program {
        version: (1, 1, 0),
        term,
    };

    let result = program.eval(ExBudget {
        mem: 1_000_000,
        cpu: 1_000_000_000,
    });

    let result_term = result.result().ok()?;
    term_to_literal(&result_term)
}

/// Check if a builtin is safe to fold (pure, no errors on valid inputs).
fn is_safe_to_fold(fun: DefaultFunction) -> bool {
    matches!(
        fun,
        DefaultFunction::AddInteger
            | DefaultFunction::SubtractInteger
            | DefaultFunction::MultiplyInteger
            | DefaultFunction::EqualsInteger
            | DefaultFunction::LessThanInteger
            | DefaultFunction::LessThanEqualsInteger
            | DefaultFunction::AppendByteString
            | DefaultFunction::EqualsByteString
            | DefaultFunction::LessThanByteString
            | DefaultFunction::LessThanEqualsByteString
            | DefaultFunction::LengthOfByteString
            | DefaultFunction::AppendString
            | DefaultFunction::EqualsString
            | DefaultFunction::EncodeUtf8
            | DefaultFunction::ConsByteString
            | DefaultFunction::EqualsData
            | DefaultFunction::NullList
            | DefaultFunction::Sha2_256
            | DefaultFunction::Sha3_256
            | DefaultFunction::Blake2b_256
            | DefaultFunction::Blake2b_224
            | DefaultFunction::MkCons
            | DefaultFunction::MkNilData
            | DefaultFunction::MkNilPairData
            | DefaultFunction::IntegerToByteString
            | DefaultFunction::ByteStringToInteger
    )
}

fn build_builtin_term(
    fun: DefaultFunction,
    args: &[&MidLiteral],
) -> Option<uplc::ast::Term<NamedDeBruijn>> {
    use uplc::ast::Term;

    let mut term = Term::Builtin { fun, uniq_id: 0 };

    // Apply forces for polymorphic builtins
    let force_count = fun.force_count();
    for _ in 0..force_count {
        term = Term::Force {
            body: term.into(),
            uniq_id: 0,
        };
    }

    for lit in args {
        let constant = literal_to_constant(lit)?;
        term = Term::Apply {
            function: term.into(),
            argument: Term::Constant {
                value: constant.into(),
                uniq_id: 0,
            }
            .into(),
            uniq_id: 0,
        };
    }

    Some(term)
}

fn literal_to_constant(lit: &MidLiteral) -> Option<Constant> {
    match lit {
        MidLiteral::Integer(n) => Some(Constant::Integer(n.clone())),
        MidLiteral::ByteString(b) => Some(Constant::ByteString(b.clone())),
        MidLiteral::String(s) => Some(Constant::String(s.clone())),
        MidLiteral::Bool(b) => Some(Constant::Bool(*b)),
        MidLiteral::Unit => Some(Constant::Unit),
        _ => None, // Complex types not worth folding
    }
}

fn term_to_literal(term: &uplc::ast::Term<NamedDeBruijn>) -> Option<MidLiteral> {
    match term {
        uplc::ast::Term::Constant { value, .. } => match value.as_ref() {
            Constant::Integer(n) => Some(MidLiteral::Integer(n.clone())),
            Constant::ByteString(b) => Some(MidLiteral::ByteString(b.clone())),
            Constant::String(s) => Some(MidLiteral::String(s.clone())),
            Constant::Bool(b) => Some(MidLiteral::Bool(*b)),
            Constant::Unit => Some(MidLiteral::Unit),
            _ => None,
        },
        _ => None,
    }
}

/// Expected argument count for a DefaultFunction. Delegating to the canonical
/// `DefaultFunction::arity()` in uplc keeps partial-vs-full application
/// classification consistent with the runtime machine.
fn builtin_arity(fun: DefaultFunction) -> usize {
    fun.arity()
}

/// Infer the return type of a fully-applied builtin.
fn builtin_return_type(fun: DefaultFunction) -> AbstractValue {
    let ty = match fun {
        DefaultFunction::AddInteger
        | DefaultFunction::SubtractInteger
        | DefaultFunction::MultiplyInteger
        | DefaultFunction::DivideInteger
        | DefaultFunction::QuotientInteger
        | DefaultFunction::RemainderInteger
        | DefaultFunction::ModInteger => AbstractType::Int,

        DefaultFunction::EqualsInteger
        | DefaultFunction::LessThanInteger
        | DefaultFunction::LessThanEqualsInteger
        | DefaultFunction::EqualsByteString
        | DefaultFunction::LessThanByteString
        | DefaultFunction::LessThanEqualsByteString
        | DefaultFunction::EqualsString
        | DefaultFunction::EqualsData
        | DefaultFunction::NullList => AbstractType::Bool,

        DefaultFunction::AppendByteString
        | DefaultFunction::ConsByteString
        | DefaultFunction::SliceByteString
        | DefaultFunction::Sha2_256
        | DefaultFunction::Sha3_256
        | DefaultFunction::Blake2b_256
        | DefaultFunction::Blake2b_224
        | DefaultFunction::Keccak_256
        | DefaultFunction::EncodeUtf8 => AbstractType::ByteArray,

        DefaultFunction::AppendString | DefaultFunction::DecodeUtf8 => AbstractType::String,

        DefaultFunction::LengthOfByteString | DefaultFunction::IndexByteString => AbstractType::Int,

        _ => AbstractType::Unknown,
    };
    AbstractValue::Typed(ty)
}

pub(crate) fn run_analysis(expr: &mut MidExpr) {
    // 1. Use counting
    super::use_count::apply_use_counts(expr);

    // 2. Abstract interpretation
    let mut analyzer = Analyzer::new();
    analyzer.analyze(expr);
}

#[cfg(test)]
mod tests;
