//! UPLC → MidExpr translation.
//!
//! Assigns a VarId to every variable, rebuilds Let from
//! Apply(Lambda, value), counts builtin forces, links UPLC
//! uniq_id ↔ MidExprId provenance, and records DeBruijn
//! bindings for runtime env inspection.

use uplc::ast::{Constant, NamedDeBruijn, Term};

use crate::pseudo::mid::expr::{CaseEncoding, MidBranch, MidExpr, MidLiteral};
use crate::pseudo::mid::expr_id::{MidExprId, ProvenanceBuilder};
use crate::pseudo::var_id::{VarId, VarInterner};

use super::var_registry::{VarOrigin, VarRegistry};

/// One pending unit of work for [`MidTranslator::translate`]'s step machine.
///
/// `Visit` descends; every other variant is a CONTINUATION — the part of a
/// term's translation that has to run after its children are translated, with
/// the header data (its `MidExprId`, its binders) carried across the gap that
/// a recursive call would have kept in a stack frame.
enum Step<'t> {
    /// Translate this term: push its node, or its continuation plus children.
    Visit(&'t Term<NamedDeBruijn>),
    /// Bring a `let` binder into scope, then translate the body under it. A
    /// separate step because the VALUE must be translated outside that scope.
    EnterLetBody {
        var: VarId,
        body: &'t Term<NamedDeBruijn>,
    },
    /// Pop the lambda's params off the scope and build the `Closure`.
    FinishClosure {
        mid_id: MidExprId,
        params: Vec<VarId>,
    },
    /// Pop the binder off the scope and build the `Let` from value + body.
    FinishLet {
        mid_id: MidExprId,
        var: VarId,
    },
    /// Rebuild the (flattened) application from its function and `arg_count` args.
    FinishApply {
        mid_id: MidExprId,
        arg_count: usize,
    },
    FinishForce {
        mid_id: MidExprId,
    },
    FinishDelay {
        mid_id: MidExprId,
    },
    FinishConstr {
        mid_id: MidExprId,
        tag: usize,
        arity: usize,
    },
    /// A `Case` over a literal `Constr`, folded to the selected branch applied
    /// to the constr's fields. Both collapsed UPLC nodes are re-attributed.
    FinishFoldedCase {
        mid_id: MidExprId,
        case_uniq: isize,
        constr_uniq: isize,
        field_count: usize,
    },
    FinishCase {
        mid_id: MidExprId,
        branch_count: usize,
    },
}

/// Take the last `n` results, oldest first — i.e. in the order they were pushed.
fn pop_n(done: &mut Vec<MidExpr>, n: usize) -> Vec<MidExpr> {
    let at = done.len() - n;
    done.split_off(at)
}

/// Translates UPLC Term<NamedDeBruijn> to MidExpr with full provenance.
pub(crate) struct MidTranslator {
    pub interner: VarInterner,
    pub var_registry: VarRegistry,
    pub provenance: ProvenanceBuilder,
    /// DeBruijn scope stack: innermost binding is last.
    scope: Vec<VarId>,
}

impl MidTranslator {
    pub(crate) fn new() -> Self {
        Self {
            interner: VarInterner::new(),
            var_registry: VarRegistry::new(),
            provenance: ProvenanceBuilder::new(),
            scope: Vec::new(),
        }
    }

    /// Translate a UPLC term, iteratively.
    pub(crate) fn translate(&mut self, term: &Term<NamedDeBruijn>) -> MidExpr {
        let mut steps: Vec<Step<'_>> = vec![Step::Visit(term)];
        let mut done: Vec<MidExpr> = Vec::new();

        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(term) => self.visit(term, &mut steps, &mut done),
                Step::EnterLetBody { var, body } => {
                    // The value was translated OUTSIDE the binding's scope;
                    // the body is translated inside it.
                    self.scope.push(var);
                    steps.push(Step::Visit(body));
                }
                Step::FinishClosure { mid_id, params } => {
                    let body = done.pop().expect("closure body");
                    for _ in &params {
                        self.scope.pop();
                    }
                    done.push(MidExpr::Closure {
                        id: mid_id,
                        params,
                        body: Box::new(body),
                        recursive: None, // filled in later
                    });
                }
                Step::FinishLet { mid_id, var } => {
                    let body = done.pop().expect("let body");
                    let value = done.pop().expect("let value");
                    self.scope.pop();
                    done.push(MidExpr::Let {
                        id: mid_id,
                        var,
                        value: Box::new(value),
                        body: Box::new(body),
                        use_count: 0, // filled in later
                    });
                }
                Step::FinishApply { mid_id, arg_count } => {
                    let function = done.pop().expect("apply function");
                    let mut args = pop_n(&mut done, arg_count);
                    args.reverse();
                    done.push(self.merge_apply(mid_id, function, args));
                }
                Step::FinishForce { mid_id } => {
                    let inner = done.pop().expect("force body");
                    done.push(self.merge_force(mid_id, inner));
                }
                Step::FinishDelay { mid_id } => {
                    let inner = done.pop().expect("delay body");
                    done.push(MidExpr::Thunk {
                        id: mid_id,
                        body: Box::new(inner),
                        cosmetic: false, // determined later
                    });
                }
                Step::FinishConstr { mid_id, tag, arity } => {
                    let fields = pop_n(&mut done, arity);
                    done.push(MidExpr::Constr {
                        id: mid_id,
                        tag,
                        fields,
                    });
                }
                Step::FinishFoldedCase {
                    mid_id,
                    case_uniq,
                    constr_uniq,
                    field_count,
                } => {
                    let fields = pop_n(&mut done, field_count);
                    let branch = done.pop().expect("folded case branch");
                    let folded = if fields.is_empty() {
                        branch
                    } else {
                        self.create_let_chain_or_apply(mid_id, branch, fields)
                    };
                    let folded_id = folded.id();
                    self.provenance.absorb_uplc(folded_id, case_uniq);
                    self.provenance.absorb_uplc(folded_id, constr_uniq);
                    done.push(folded);
                }
                Step::FinishCase {
                    mid_id,
                    branch_count,
                } => {
                    let bodies = pop_n(&mut done, branch_count);
                    let scrutinee = done.pop().expect("case scrutinee");
                    done.push(self.build_case(mid_id, scrutinee, bodies));
                }
            }
        }

        debug_assert_eq!(done.len(), 1, "the step machine must leave one result");
        done.pop().expect("translation result")
    }

    /// One term: emit its own node, or its header plus the [`Step`]s that will
    /// translate its children and reassemble it.
    ///
    /// Children are pushed in REVERSE so the stack pops them in source order.
    fn visit<'t>(
        &mut self,
        term: &'t Term<NamedDeBruijn>,
        steps: &mut Vec<Step<'t>>,
        done: &mut Vec<MidExpr>,
    ) {
        let mid_id = self.provenance.fresh_id();

        let uplc_id = term_uniq_id(term);
        self.provenance.link(mid_id, uplc_id);

        match term {
            Term::Var { name, .. } => {
                let debruijn_idx: usize = name.index.into();
                let var_id = self.lookup_var(debruijn_idx);

                done.push(MidExpr::Var {
                    id: mid_id,
                    var: var_id.unwrap_or_else(|| {
                        // Free variable — create a synthetic binding
                        let name = format!("free_{}", debruijn_idx);
                        let vid = self.interner.intern_fresh(&name);
                        self.var_registry.register(vid, name, VarOrigin::Synthetic);
                        vid
                    }),
                });
            }

            Term::Constant { value, .. } => done.push(MidExpr::Lit {
                id: mid_id,
                value: constant_to_literal(value),
            }),

            Term::Lambda {
                parameter_name,
                body,
                uniq_id,
            } => {
                // Collect chained lambdas: \x -> \y -> body → Closure([x, y], body)
                let mut params = Vec::new();
                let mut current_body = body.as_ref();
                let current_uniq = *uniq_id;

                // First param
                let param_name = sanitize_name(&parameter_name.text);
                let param_id = self.interner.intern_fresh(&param_name);
                self.var_registry.register(
                    param_id,
                    param_name,
                    VarOrigin::LambdaParam {
                        lambda_term_id: current_uniq,
                        position: 0,
                    },
                );
                self.var_registry.record_debruijn(param_id, current_uniq, 0);
                params.push(param_id);

                // Collect additional chained lambdas
                while let Term::Lambda {
                    parameter_name: inner_name,
                    body: inner_body,
                    uniq_id: inner_uniq,
                } = current_body
                {
                    let name = sanitize_name(&inner_name.text);
                    let pid = self.interner.intern_fresh(&name);
                    self.var_registry.register(
                        pid,
                        name,
                        VarOrigin::LambdaParam {
                            lambda_term_id: *inner_uniq,
                            position: params.len(),
                        },
                    );
                    self.var_registry.record_debruijn(pid, *inner_uniq, 0);
                    params.push(pid);

                    // Preserve exact ownership of collapsed lambda-chain nodes
                    // on the surviving outer Closure MidExpr.
                    self.provenance.absorb_uplc(mid_id, *inner_uniq);

                    current_body = inner_body.as_ref();
                }

                // Push all params onto scope (in order: first param has highest DeBruijn)
                for p in &params {
                    self.scope.push(*p);
                }

                steps.push(Step::FinishClosure { mid_id, params });
                steps.push(Step::Visit(current_body));
            }

            Term::Apply {
                function,
                argument,
                uniq_id,
            } => {
                // Detect let pattern: Apply(Lambda, value) → Let
                if let Term::Lambda {
                    parameter_name,
                    body,
                    uniq_id: lambda_uniq,
                } = function.as_ref()
                {
                    let var_name = sanitize_name(&parameter_name.text);
                    let var_id = self.interner.intern_fresh(&var_name);
                    self.var_registry.register(
                        var_id,
                        var_name,
                        VarOrigin::LetBinding {
                            apply_term_id: *uniq_id,
                        },
                    );
                    self.var_registry.record_debruijn(var_id, *lambda_uniq, 0);

                    // The inner lambda is collapsed into the surviving Let owner.
                    self.provenance.absorb_uplc(mid_id, *lambda_uniq);

                    steps.push(Step::FinishLet {
                        mid_id,
                        var: var_id,
                    });
                    steps.push(Step::EnterLetBody {
                        var: var_id,
                        body: body.as_ref(),
                    });
                    steps.push(Step::Visit(argument.as_ref()));
                    return;
                }

                // Collect chained applications: f(a)(b)(c) → Apply(f, [a, b, c])
                let mut arg_terms: Vec<&'t Term<NamedDeBruijn>> = vec![argument.as_ref()];
                let mut func_term = function.as_ref();

                while let Term::Apply {
                    function: inner_f,
                    argument: inner_a,
                    uniq_id: inner_uniq,
                } = func_term
                {
                    // Don't flatten if inner apply is also a let pattern
                    if matches!(inner_f.as_ref(), Term::Lambda { .. }) {
                        break;
                    }
                    // Preserve exact ownership of collapsed apply-spine nodes on
                    // the surviving outer Apply owner.
                    self.provenance.absorb_uplc(mid_id, *inner_uniq);
                    arg_terms.push(inner_a.as_ref());
                    func_term = inner_f.as_ref();
                }

                steps.push(Step::FinishApply {
                    mid_id,
                    arg_count: arg_terms.len(),
                });
                steps.push(Step::Visit(func_term));
                for arg in arg_terms.into_iter().rev() {
                    steps.push(Step::Visit(arg));
                }
            }

            Term::Force { body, .. } => {
                steps.push(Step::FinishForce { mid_id });
                steps.push(Step::Visit(body.as_ref()));
            }

            Term::Delay { body, .. } => {
                steps.push(Step::FinishDelay { mid_id });
                steps.push(Step::Visit(body.as_ref()));
            }

            Term::Builtin { fun, .. } => done.push(MidExpr::Builtin {
                id: mid_id,
                fun: *fun,
                forces: 0,
                args: Vec::new(),
                folded: None,
            }),

            Term::Error { .. } => done.push(MidExpr::Error { id: mid_id }),

            Term::Constr { tag, fields, .. } => {
                steps.push(Step::FinishConstr {
                    mid_id,
                    tag: *tag,
                    arity: fields.len(),
                });
                for field in fields.iter().rev() {
                    steps.push(Step::Visit(field));
                }
            }

            Term::Case {
                constr,
                branches,
                uniq_id,
            } => {
                // Constant-fold: Case(Constr<tag>(fields), branches) → Apply(branches[tag], fields)
                // This is the V3 pattern where Constr packs builtins and Case selects a branch.
                if let Term::Constr {
                    tag: constr_tag,
                    fields: constr_fields,
                    uniq_id: constr_uniq,
                    ..
                } = constr.as_ref()
                    && let Some(branch) = branches.get(*constr_tag)
                {
                    steps.push(Step::FinishFoldedCase {
                        mid_id,
                        case_uniq: *uniq_id,
                        constr_uniq: *constr_uniq,
                        field_count: constr_fields.len(),
                    });
                    for field in constr_fields.iter().rev() {
                        steps.push(Step::Visit(field));
                    }
                    steps.push(Step::Visit(branch));
                    return;
                }

                // Non-constant scrutinee: create Case node with binder extraction
                steps.push(Step::FinishCase {
                    mid_id,
                    branch_count: branches.len(),
                });
                for branch in branches.iter().rev() {
                    steps.push(Step::Visit(branch));
                }
                steps.push(Step::Visit(constr.as_ref()));
            }
        }
    }

    /// `Apply` reassembly: a `Builtin` head swallows the args instead of being
    /// wrapped, so `builtin(a)(b)` stays one node.
    fn merge_apply(&mut self, mid_id: MidExprId, function: MidExpr, args: Vec<MidExpr>) -> MidExpr {
        match function {
            MidExpr::Builtin {
                id: b_id,
                fun,
                forces,
                args: mut builtin_args,
                folded,
            } => {
                self.provenance.absorb_mid(b_id, mid_id);
                builtin_args.extend(args);
                MidExpr::Builtin {
                    id: b_id,
                    fun,
                    forces,
                    args: builtin_args,
                    folded,
                }
            }
            _ => MidExpr::Apply {
                id: mid_id,
                function: Box::new(function),
                args,
            },
        }
    }

    /// `Force` reassembly: a force over a builtin (bare, or already applied)
    /// becomes that builtin's force count rather than a wrapper node.
    fn merge_force(&mut self, mid_id: MidExprId, inner: MidExpr) -> MidExpr {
        // If inner is a Builtin, increment its force count instead
        if let MidExpr::Builtin {
            id: b_id,
            fun,
            forces,
            args,
            folded,
        } = inner
        {
            self.provenance.absorb_mid(b_id, mid_id);
            return MidExpr::Builtin {
                id: b_id,
                fun,
                forces: forces + 1,
                args,
                folded,
            };
        }

        // Force(Apply(Builtin{...}, args)) → Builtin{forces++, args}
        // Handles patterns like Force(Apply(Apply(Force(Builtin), arg1), arg2))
        if let MidExpr::Apply {
            id: apply_id,
            function,
            args: apply_args,
            ..
        } = inner
        {
            if let MidExpr::Builtin {
                id: b_id,
                fun,
                forces,
                mut args,
                folded,
            } = *function
            {
                self.provenance.absorb_mid(b_id, mid_id);
                args.extend(apply_args);
                return MidExpr::Builtin {
                    id: b_id,
                    fun,
                    forces: forces + 1,
                    args,
                    folded,
                };
            }
            // Not a builtin — wrap back in Force(Apply(...))
            return MidExpr::Force {
                id: mid_id,
                body: Box::new(MidExpr::Apply {
                    id: apply_id,
                    function,
                    args: apply_args,
                }),
                resolved: None,
            };
        }

        MidExpr::Force {
            id: mid_id,
            body: Box::new(inner),
            resolved: None,
        }
    }

    /// `Case` reassembly: lift each `Closure` branch's params into the branch's
    /// binders and unwrap the Scott-encoding thunk around its body.
    fn build_case(
        &mut self,
        mid_id: MidExprId,
        scrutinee: MidExpr,
        bodies: Vec<MidExpr>,
    ) -> MidExpr {
        let mut mid_branches: Vec<MidBranch> = bodies
            .into_iter()
            .enumerate()
            .map(|(i, body)| MidBranch {
                tag: i,
                binders: Vec::new(),
                body,
            })
            .collect();

        // Extract binders from Lambda branches
        for branch in &mut mid_branches {
            if let MidExpr::Closure {
                id: closure_id,
                params,
                body,
                ..
            } = branch.body.clone()
            {
                branch.binders = params;
                let mut extracted_body = *body;
                let mut collapsed_uplc_ids = self.provenance.uplc_ids(closure_id).to_vec();
                // Unwrap cosmetic Thunk from Scott encoding
                if let MidExpr::Thunk {
                    id: thunk_id,
                    body: inner,
                    ..
                } = extracted_body
                {
                    collapsed_uplc_ids.extend(self.provenance.uplc_ids(thunk_id).iter().copied());
                    extracted_body = *inner;
                }
                let extracted_body_id = extracted_body.id();
                for uplc_id in collapsed_uplc_ids {
                    self.provenance.absorb_uplc(extracted_body_id, uplc_id);
                }
                branch.body = extracted_body;
            }
        }

        MidExpr::Case {
            id: mid_id,
            scrutinee: Box::new(scrutinee),
            branches: mid_branches,
            encoding: CaseEncoding::Native,
        }
    }

    /// Used when constant-folding Case(Constr<tag>(fields), [Lambda(params, body)]).
    fn create_let_chain_or_apply(
        &mut self,
        mid_id: MidExprId,
        function: MidExpr,
        args: Vec<MidExpr>,
    ) -> MidExpr {
        // If function is a Closure with enough params, unzip into a Let chain;
        // args past the param count are applied to the resulting body.
        match function {
            MidExpr::Closure {
                id: closure_id,
                params,
                body,
                ..
            } if params.len() <= args.len() => {
                let mut result = *body;
                // Unwrap cosmetic Thunk from Scott/Case encoding
                let mut unwrapped_thunk_id = None;
                if let MidExpr::Thunk {
                    id: thunk_id, body, ..
                } = result
                {
                    unwrapped_thunk_id = Some(thunk_id);
                    result = *body;
                }

                // Split args into bound (matching params) and excess
                let param_count = params.len();
                let bound_args: Vec<MidExpr> = args.iter().take(param_count).cloned().collect();
                let excess_args: Vec<MidExpr> = args.into_iter().skip(param_count).collect();
                let closure_uplc_ids = self.provenance.uplc_ids(closure_id).to_vec();
                let mut outermost_let_id = None;

                // Bind params to their matching args
                for (param, arg) in params.into_iter().zip(bound_args).rev() {
                    let let_id = self.provenance.fresh_derived_from(mid_id);
                    result = MidExpr::Let {
                        id: let_id,
                        var: param,
                        value: Box::new(arg),
                        body: Box::new(result),
                        use_count: 0,
                    };
                    outermost_let_id = Some(let_id);
                }

                if let Some(outermost_let_id) = outermost_let_id {
                    for uplc_id in closure_uplc_ids {
                        self.provenance.absorb_uplc(outermost_let_id, uplc_id);
                    }
                    if let Some(thunk_id) = unwrapped_thunk_id {
                        self.provenance.absorb_mid(outermost_let_id, thunk_id);
                    }
                }

                // Apply excess args to the result (they're data arguments for bound functions)
                if !excess_args.is_empty() {
                    result = MidExpr::Apply {
                        id: mid_id,
                        function: Box::new(result),
                        args: excess_args,
                    };
                }

                result
            }
            other => {
                // Fallback: regular Apply
                MidExpr::Apply {
                    id: mid_id,
                    function: Box::new(other),
                    args,
                }
            }
        }
    }

    fn lookup_var(&self, debruijn_index: usize) -> Option<VarId> {
        if debruijn_index == 0 || self.scope.is_empty() {
            return None;
        }
        // DeBruijn index 1 = most recently bound variable (last in scope)
        let idx = debruijn_index.checked_sub(1)?;
        if idx < self.scope.len() {
            Some(self.scope[self.scope.len() - 1 - idx])
        } else {
            None // free variable
        }
    }
}

impl Default for MidTranslator {
    fn default() -> Self {
        Self::new()
    }
}

fn term_uniq_id(term: &Term<NamedDeBruijn>) -> isize {
    match term {
        Term::Var { uniq_id, .. }
        | Term::Delay { uniq_id, .. }
        | Term::Lambda { uniq_id, .. }
        | Term::Apply { uniq_id, .. }
        | Term::Constant { uniq_id, .. }
        | Term::Force { uniq_id, .. }
        | Term::Error { uniq_id }
        | Term::Builtin { uniq_id, .. }
        | Term::Constr { uniq_id, .. }
        | Term::Case { uniq_id, .. } => *uniq_id,
    }
}

fn constant_to_literal(constant: &Constant) -> MidLiteral {
    match constant {
        Constant::Integer(n) => MidLiteral::Integer(n.clone()),
        Constant::ByteString(b) => MidLiteral::ByteString(b.clone()),
        Constant::String(s) => MidLiteral::String(s.clone()),
        Constant::Bool(b) => MidLiteral::Bool(*b),
        Constant::Unit => MidLiteral::Unit,
        Constant::Data(d) => MidLiteral::Data(Box::new(d.clone())),
        Constant::ProtoList(_, items) => {
            MidLiteral::List(items.iter().map(constant_to_literal).collect())
        }
        Constant::ProtoPair(_, _, a, b) => MidLiteral::Pair(
            Box::new(constant_to_literal(a)),
            Box::new(constant_to_literal(b)),
        ),
        // BLS elements: store as opaque markers (no blst dependency in decompiler)
        Constant::Bls12_381G1Element(_) => MidLiteral::Bls12_381G1(vec![]),
        Constant::Bls12_381G2Element(_) => MidLiteral::Bls12_381G2(vec![]),
        Constant::Bls12_381MlResult(_) => MidLiteral::ByteString(b"<ml_result>".to_vec()),
    }
}

/// Clean up DeBruijn variable name hints.
fn sanitize_name(name: &str) -> String {
    let s = name.trim();
    if s.is_empty() || s == "i" {
        // Default names for anonymous parameters
        "v".to_string()
    } else {
        s.to_string()
    }
}

#[cfg(test)]
mod tests;
