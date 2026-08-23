//! MidExpr → PseudoExpr lowering, building the SourceMap alongside.
//!
//! Most Delay/Force pairs are already resolved at the MIR level; an
//! unresolved Force lowers to `PseudoExpr::Force` for the simplifier.

use crate::builtins::BuiltinId;
use crate::decompile::constructor_data::{
    normalize_constructor_data_expr, normalize_convertible_data_expr,
};
use crate::decompile::pseudo_lineage::{project_final_pseudo_to_mid, snapshot_expr_at_path};
use crate::error::Result;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, PseudoNodeId, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::mid::expr::{CaseEncoding, MidBranch, MidExpr, MidLiteral};
use crate::pseudo::mid::expr_id::{MidExprId, ProvenanceBuilder};
use crate::pseudo::var_id::VarInterner;

use super::source_map::SourceMap;
use super::type_env::TypeEnvironment;

pub(crate) struct MirDecompileOutput {
    pub pseudo: PseudoExpr,
    pub source_map: SourceMap,
    pub var_registry: super::var_registry::VarRegistry,
    pub simplify_state: crate::decompile::simplify::SimplifyState,
    /// Inferred type environment populated during MIR lowering:
    /// literals, Lit-valued Let binders, Var echoes, folded and
    /// saturated builtins, If/Case branch types, Closure-in-Let
    /// signatures, saturated Apply results, Constr/Data, Trace.
    ///
    /// Only `type_invariants` reads it; `naming`, `render_prep`,
    /// `helper_hoist`, `late_normalize`, `late_option_cps`, `lambda`,
    /// and `pretty` still read the inline `PseudoExpr::Var.tipo` field.
    pub type_env: std::rc::Rc<TypeEnvironment>,
}

/// Lowers MidExpr to PseudoExpr while building the source map.
pub(crate) struct Lowerer<'a> {
    interner: &'a VarInterner,
    provenance: &'a ProvenanceBuilder,
    pub source_map: SourceMap,
    pub simplify_state: crate::decompile::simplify::SimplifyState,
    /// Type environment populated during lowering (dual-write).
    pub type_env: TypeEnvironment,
    /// Producer-witnessed church-bool orientations for Scott
    /// 2x0-binder cases (key = the `Case`'s `MidExprId`). Scott branch
    /// tags are POSITIONS, so without a witness those cases keep honest
    /// `Constr<0>/Constr<1>` patterns instead of guessed True/False.
    pub bool_orientations:
        std::collections::HashMap<MidExprId, super::bool_orientation::Orientation>,
    /// Per-bool data-tag church-bool conventions: Native 2x0 case id ->
    /// `church_true` tag (which `Constr<t>` is true for that bool). Seeds
    /// convention-oriented arm patterns so the collapse is per-bool, not
    /// program-flag. Absent = unwitnessed (program-flag fallback).
    pub datatag_conventions: std::collections::HashMap<MidExprId, usize>,
    /// Paths of the nodes being lowered. See [`PathArena`].
    paths: PathArena,
    /// Whether to maintain `source_map.initial_pseudo_to_mid`.
    ///
    /// That map has exactly one consumer — the final-pseudo lineage projection
    /// — and that projection returns an empty map unless the pipeline is
    /// collecting per-pass snapshots, which a plain decompile does not. Keeping
    /// it up to date is not free: every rewrite that moves a subtree has to
    /// re-key the whole subtree, because a `PseudoNodeId` is a hash of the
    /// node's path. Nested `Force(Delay(x))` cancellations re-key the same
    /// subtree once per level, which is quadratic and, with the flattening
    /// constant, measured cubic.
    track_lineage: bool,
}

impl<'a> Lowerer<'a> {
    pub(crate) fn new(interner: &'a VarInterner, provenance: &'a ProvenanceBuilder) -> Self {
        Self {
            interner,
            provenance,
            source_map: SourceMap::new(),
            simplify_state: crate::decompile::simplify::SimplifyState::default(),
            type_env: TypeEnvironment::new(),
            bool_orientations: std::collections::HashMap::new(),
            datatag_conventions: std::collections::HashMap::new(),
            paths: PathArena::new(),
            // On by default: a caller that constructs a Lowerer directly gets
            // the full source map. The pipeline turns it off when the map will
            // not be read.
            track_lineage: true,
        }
    }

    /// Opt out of maintaining `initial_pseudo_to_mid`. See the field.
    pub(crate) fn with_lineage_tracking(mut self, track: bool) -> Self {
        self.track_lineage = track;
        self
    }

    /// Lower a MidExpr to PseudoExpr.
    pub(crate) fn lower(&mut self, mid: &MidExpr) -> Result<PseudoExpr> {
        let root = self.paths.root();
        self.lower_at(mid, root)
    }

    /// Lower `root` on a heap step stack.
    ///
    /// The tree depth is script-controlled — a spine tens of thousands of nodes
    /// deep fits inside the Plutus size limit — and on `wasm32` the engine's
    /// call stack cannot be grown to match, so the descent must not sit on it.
    fn lower_at(&mut self, root: &MidExpr, root_path: PathId) -> Result<PseudoExpr> {
        let mut frames: Vec<Frame<'_>> = vec![Frame::Enter {
            mid: root,
            path: root_path,
        }];
        let mut done: Vec<PseudoExpr> = Vec::new();

        while let Some(frame) = frames.pop() {
            match frame {
                Frame::Enter { mid, path } => {
                    let mid_id = mid.id();
                    match mid {
                        MidExpr::Thunk { body, cosmetic, .. } => {
                            let uplc_ids = self.provenance.uplc_ids(mid_id);
                            self.source_map.register_mid(mid_id, &uplc_ids);
                            // A cosmetic thunk is stripped, so its body takes
                            // this node's own path rather than one below it.
                            let body_path = if *cosmetic {
                                path
                            } else {
                                self.paths.child(path, 0)
                            };
                            frames.push(Frame::Thunk {
                                mid_id,
                                path,
                                cosmetic: *cosmetic,
                            });
                            frames.push(Frame::Enter {
                                mid: body,
                                path: body_path,
                            });
                        }
                        MidExpr::Closure {
                            params,
                            body,
                            recursive,
                            ..
                        } => {
                            let uplc_ids = self.provenance.uplc_ids(mid_id);
                            self.source_map.register_mid(mid_id, &uplc_ids);
                            // Build binders with MIR-authoritative VarIds so
                            // they match the body's `var_with_id(name, *var)`
                            // references; `Binder::synthetic` mints fresh
                            // ones and orphans them.
                            let param_binders: Vec<crate::pseudo::ast::Binder> = params
                                .iter()
                                .map(|p| {
                                    let name = self.interner.resolve(*p).to_string();
                                    self.source_map.register_var(*p, name.clone());
                                    crate::pseudo::ast::Binder::new(name, *p)
                                })
                                .collect();
                            let body_path = self.paths.child(path, 0);
                            frames.push(Frame::Closure {
                                mid_id,
                                path,
                                param_binders,
                                recursive: *recursive,
                            });
                            frames.push(Frame::Enter {
                                mid: body,
                                path: body_path,
                            });
                        }
                        MidExpr::Apply { function, args, .. } => {
                            let uplc_ids = self.provenance.uplc_ids(mid_id);
                            self.source_map.register_mid(mid_id, &uplc_ids);

                            // A fully applied call to a Var with a recorded
                            // FnSignature has the signature's return type.
                            // Peek BEFORE lowering the function, which
                            // consumes its MidExpr shape.
                            //
                            // Other arities get no type: a partial application
                            // returns a curried Function(remaining_params -> ret)
                            // that nothing synthesizes yet, and over-saturation
                            // means the callee returned a further callable whose
                            // signature is not tracked here.
                            let result_type = if let MidExpr::Var { var, .. } = function.as_ref() {
                                self.type_env.signature_of(*var).and_then(|sig| {
                                    if sig.arity() == args.len() {
                                        Some(sig.return_type.clone())
                                    } else {
                                        None
                                    }
                                })
                            } else {
                                None
                            };

                            let function_path = self.paths.child(path, 0);
                            let arg_paths: Vec<PathId> = (0..args.len())
                                .map(|index| self.paths.child(path, index as u32 + 1))
                                .collect();

                            frames.push(Frame::Apply {
                                mid_id,
                                path,
                                result_type,
                                argc: args.len(),
                            });
                            // Pushed in reverse so they pop — and so land on
                            // `done` — in source order: callee, then args.
                            for (arg, arg_path) in args.iter().zip(arg_paths).rev() {
                                frames.push(Frame::Enter {
                                    mid: arg,
                                    path: arg_path,
                                });
                            }
                            frames.push(Frame::Enter {
                                mid: function,
                                path: function_path,
                            });
                        }

                        MidExpr::Constr { tag, fields, .. } => {
                            let uplc_ids = self.provenance.uplc_ids(mid_id);
                            self.source_map.register_mid(mid_id, &uplc_ids);

                            let field_paths: Vec<PathId> = (0..fields.len())
                                .map(|index| self.paths.child(path, index as u32))
                                .collect();
                            frames.push(Frame::Constr {
                                mid_id,
                                path,
                                tag: *tag,
                                count: fields.len(),
                            });
                            for (field, field_path) in fields.iter().zip(field_paths).rev() {
                                frames.push(Frame::Enter {
                                    mid: field,
                                    path: field_path,
                                });
                            }
                        }

                        MidExpr::Builtin {
                            fun, args, folded, ..
                        } => {
                            let uplc_ids = self.provenance.uplc_ids(mid_id);
                            self.source_map.register_mid(mid_id, &uplc_ids);

                            if let Some(lit) = folded {
                                // A folded builtin's result is a literal with a
                                // known type; register it so consumers of the
                                // result see a real type. No children to lower.
                                let folded_ty = Self::literal_type(lit);
                                self.type_env.bind_expr(mid_id, folded_ty);
                                let lowered = self.lower_literal(lit);
                                self.register_mid_subtree_on_expr_path(&lowered, path, mid);
                                self.register_lowered(&lowered, path, mid_id);
                                done.push(lowered);
                            } else {
                                // Children first, so the args carry expr_type
                                // entries before the polymorphic result type is
                                // derived from them.
                                let arg_paths: Vec<PathId> = (0..args.len())
                                    .map(|index| self.paths.child(path, index as u32))
                                    .collect();
                                frames.push(Frame::Builtin {
                                    mid_id,
                                    path,
                                    fun: *fun,
                                    mid_args: args,
                                });
                                for (arg, arg_path) in args.iter().zip(arg_paths).rev() {
                                    frames.push(Frame::Enter {
                                        mid: arg,
                                        path: arg_path,
                                    });
                                }
                            }
                        }

                        MidExpr::Force { body, resolved, .. } => {
                            let uplc_ids = self.provenance.uplc_ids(mid_id);
                            self.source_map.register_mid(mid_id, &uplc_ids);

                            if let Some(resolved_expr) = resolved {
                                // The resolved expression stands in for this
                                // node, so it takes this node's own path.
                                frames.push(Frame::Force {
                                    mid_id,
                                    path,
                                    kind: ForceKind::Resolved { body },
                                });
                                frames.push(Frame::Enter {
                                    mid: resolved_expr,
                                    path,
                                });
                            } else if let MidExpr::Thunk {
                                id: thunk_id,
                                body: thunk_body,
                                ..
                            } = body.as_ref()
                            {
                                // Force(Thunk(x)) -> x, at this node's path.
                                frames.push(Frame::Force {
                                    mid_id,
                                    path,
                                    kind: ForceKind::ThunkCancel {
                                        thunk_id: *thunk_id,
                                    },
                                });
                                frames.push(Frame::Enter {
                                    mid: thunk_body,
                                    path,
                                });
                            } else if let MidExpr::Let {
                                id: let_id,
                                var,
                                value,
                                body: let_body,
                                ..
                            } = body.as_ref()
                                && let MidExpr::Thunk {
                                    id: thunk_id,
                                    body: thunk_body,
                                    ..
                                } = let_body.as_ref()
                            {
                                // Force(Let(v, val, Thunk(x))) -> Let(v, val, x)
                                let name = self.interner.resolve(*var).to_string();
                                self.source_map.register_var(*var, name.clone());
                                let value_path = self.paths.child(path, 0);
                                let body_path = self.paths.child(path, 1);
                                frames.push(Frame::Force {
                                    mid_id,
                                    path,
                                    kind: ForceKind::LetThunk {
                                        let_id: *let_id,
                                        thunk_id: *thunk_id,
                                        var: *var,
                                        name,
                                    },
                                });
                                frames.push(Frame::Enter {
                                    mid: thunk_body,
                                    path: body_path,
                                });
                                frames.push(Frame::Enter {
                                    mid: value,
                                    path: value_path,
                                });
                            } else {
                                let body_path = self.paths.child(path, 0);
                                frames.push(Frame::Force {
                                    mid_id,
                                    path,
                                    kind: ForceKind::Plain,
                                });
                                frames.push(Frame::Enter {
                                    mid: body,
                                    path: body_path,
                                });
                            }
                        }

                        MidExpr::Let {
                            var, value, body, ..
                        } => {
                            let uplc_ids = self.provenance.uplc_ids(mid_id);
                            self.source_map.register_mid(mid_id, &uplc_ids);

                            let name = self.interner.resolve(*var).to_string();
                            self.source_map.register_var(*var, name.clone());
                            // Capture the value's MidExprId before lowering, to
                            // bind any type the Lit writer registered onto the
                            // let binder's VarId.
                            let value_mid_id = value.id();
                            // Peek at the Closure shape for signature emission
                            // before lowering turns `value` into a PseudoExpr.
                            let closure_signature_info: Option<(
                                Vec<crate::pseudo::var_id::VarId>,
                                MidExprId,
                                bool,
                            )> = if let MidExpr::Closure {
                                params,
                                body: closure_body,
                                recursive,
                                ..
                            } = value.as_ref()
                            {
                                Some((params.clone(), closure_body.id(), recursive.is_some()))
                            } else {
                                None
                            };

                            let value_path = self.paths.child(path, 0);
                            let body_path = self.paths.child(path, 1);
                            frames.push(Frame::LetPost {
                                mid_id,
                                path,
                                var: *var,
                                name: name.clone(),
                            });
                            frames.push(Frame::Enter {
                                mid: body,
                                path: body_path,
                            });
                            frames.push(Frame::LetBetween {
                                var: *var,
                                name,
                                value_mid_id,
                                closure_signature_info,
                            });
                            frames.push(Frame::Enter {
                                mid: value,
                                path: value_path,
                            });
                        }

                        MidExpr::Case {
                            scrutinee,
                            branches,
                            encoding,
                            ..
                        } => {
                            let uplc_ids = self.provenance.uplc_ids(mid_id);
                            self.source_map.register_mid(mid_id, &uplc_ids);

                            // Collect branch-body ids up front; their types
                            // unify into the Case's own expr_type after
                            // lowering.
                            let branch_body_ids: Vec<MidExprId> =
                                branches.iter().map(|b| b.body.id()).collect();
                            let subject_path = self.paths.child(path, 0);
                            frames.push(Frame::CaseBranches {
                                mid_id,
                                path,
                                branches,
                                encoding: *encoding,
                                branch_body_ids,
                            });
                            frames.push(Frame::Enter {
                                mid: scrutinee,
                                path: subject_path,
                            });
                        }

                        MidExpr::If {
                            condition,
                            then_branch,
                            else_branch,
                            ..
                        } => {
                            let uplc_ids = self.provenance.uplc_ids(mid_id);
                            self.source_map.register_mid(mid_id, &uplc_ids);

                            let then_id = then_branch.id();
                            let else_id = else_branch.id();
                            let condition_path = self.paths.child(path, 0);
                            let then_path = self.paths.child(path, 1);
                            let else_path = self.paths.child(path, 2);
                            frames.push(Frame::If {
                                mid_id,
                                path,
                                then_id,
                                else_id,
                            });
                            frames.push(Frame::Enter {
                                mid: else_branch,
                                path: else_path,
                            });
                            frames.push(Frame::Enter {
                                mid: then_branch,
                                path: then_path,
                            });
                            frames.push(Frame::Enter {
                                mid: condition,
                                path: condition_path,
                            });
                        }

                        MidExpr::Trace { message, body, .. } => {
                            let uplc_ids = self.provenance.uplc_ids(mid_id);
                            self.source_map.register_mid(mid_id, &uplc_ids);

                            let body_mid_id = body.id();
                            let message_path = self.paths.child(path, 0);
                            let body_path = self.paths.child(path, 1);
                            frames.push(Frame::Trace {
                                mid_id,
                                path,
                                body_mid_id,
                            });
                            frames.push(Frame::Enter {
                                mid: body,
                                path: body_path,
                            });
                            frames.push(Frame::Enter {
                                mid: message,
                                path: message_path,
                            });
                        }

                        // Leaves: `lower_with_path_inner` does not descend.
                        _ => {
                            let lowered = self.lower_with_path_inner(mid, path)?;
                            done.push(lowered);
                        }
                    }
                }

                Frame::Thunk {
                    mid_id,
                    path,
                    cosmetic,
                } => {
                    let body = done.pop().expect("thunk body");
                    let expr = if cosmetic {
                        // Strip cosmetic thunks
                        self.register_mid_on_expr_path(&body, path, mid_id);
                        body
                    } else {
                        PseudoExpr::Delay(PBox::new(body))
                    };
                    self.register_lowered(&expr, path, mid_id);
                    done.push(expr);
                }

                Frame::Closure {
                    mid_id,
                    path,
                    param_binders,
                    recursive,
                } => {
                    let body = done.pop().expect("closure body");
                    let expr = if let Some(self_ref) = recursive {
                        let name = self.interner.resolve(self_ref).to_string();
                        PseudoExpr::RecFn {
                            name: crate::pseudo::ast::Binder::new(name, self_ref),
                            params: param_binders,
                            body: PBox::new(body),
                        }
                    } else {
                        PseudoExpr::Lambda {
                            params: param_binders,
                            body: PBox::new(body),
                        }
                    };
                    self.register_lowered(&expr, path, mid_id);
                    done.push(expr);
                }

                Frame::If {
                    mid_id,
                    path,
                    then_id,
                    else_id,
                } => {
                    let else_branch = done.pop().expect("if else-branch");
                    let then_branch = done.pop().expect("if then-branch");
                    let condition = done.pop().expect("if condition");
                    let expr = PseudoExpr::If {
                        condition: PBox::new(condition),
                        then_branch: PBox::new(then_branch),
                        else_branch: PBox::new(else_branch),
                    };
                    // The If result type is either branch's: bind only when one
                    // of them recorded a type, preferring the then-branch when
                    // the two differ. No unification here.
                    if let Some(ty) = self
                        .type_env
                        .type_of_expr(then_id)
                        .or_else(|| self.type_env.type_of_expr(else_id))
                    {
                        self.type_env.bind_expr(mid_id, ty);
                    }
                    self.register_lowered(&expr, path, mid_id);
                    done.push(expr);
                }

                Frame::Trace {
                    mid_id,
                    path,
                    body_mid_id,
                } => {
                    let value = done.pop().expect("trace value");
                    let message = done.pop().expect("trace message");
                    let expr = PseudoExpr::Trace {
                        message: PBox::new(message),
                        value: PBox::new(value),
                    };
                    // Trace returns its body's value, so its expr_type mirrors
                    // the body's. An untyped body leaves Trace untyped, which
                    // is fine: the invariant check sees through Trace via
                    // `effective_expr_type`.
                    if let Some(ty) = self.type_env.type_of_expr(body_mid_id) {
                        self.type_env.bind_expr(mid_id, ty);
                    }
                    self.register_lowered(&expr, path, mid_id);
                    done.push(expr);
                }

                Frame::LetBetween {
                    var,
                    name,
                    value_mid_id,
                    closure_signature_info,
                } => {
                    if let Some(ty) = self.type_env.type_of_expr(value_mid_id) {
                        self.type_env.bind_var(var, ty);
                    }
                    // If the Let binds a Closure whose body has a recorded
                    // type, emit a function signature keyed by the binder.
                    if let Some((params, body_mid_id, is_recursive)) = closure_signature_info
                        && let Some(return_type) = self.type_env.type_of_expr(body_mid_id)
                    {
                        let param_types: Vec<(
                            crate::pseudo::var_id::VarId,
                            std::rc::Rc<crate::pseudo::ast::PseudoType>,
                        )> = params
                            .iter()
                            .map(|p| {
                                let ty = self.type_env.type_of_var(*p).unwrap_or_else(|| {
                                    std::rc::Rc::new(crate::pseudo::ast::PseudoType::Unknown)
                                });
                                (*p, ty)
                            })
                            .collect();
                        let sig = super::type_env::FnSignature::new(
                            param_types,
                            return_type,
                            is_recursive,
                        );
                        self.type_env.bind_signature(var, sig);
                    }
                    // `done` is a local, so this borrow does not conflict with
                    // `&mut self` below.
                    let value = done.last().expect("let value");
                    self.seed_simplify_state(var, &name, value);
                }

                Frame::LetPost {
                    mid_id,
                    path,
                    var,
                    name,
                } => {
                    let body = done.pop().expect("let body");
                    let value = done.pop().expect("let value");
                    let expr = PseudoExpr::let_bind_with_id(name, var, value, body);
                    self.register_lowered(&expr, path, mid_id);
                    done.push(expr);
                }

                Frame::CaseBranches {
                    mid_id,
                    path,
                    branches,
                    encoding,
                    branch_body_ids,
                } => {
                    // Scott branch tags are POSITIONS, not data tags, so the
                    // (0,0)/(1,0) pair is NOT a data Bool: a church bool (the
                    // `ifThenElse` `\t f -> t` convention) has True at position
                    // 0, a constructor-ordered Scott data Bool at position 1.
                    // Label only on a producer witness; unwitnessed cases keep
                    // honest positional patterns. Shape-keyed Option/Result
                    // pairs stay on the generic path — payload arity
                    // disambiguates them regardless of encoding.
                    let scott_bool = encoding == CaseEncoding::Scott
                        && branches.len() == 2
                        && branches.iter().all(|b| b.binders.is_empty());
                    let orientation = if scott_bool {
                        self.bool_orientations.get(&mid_id).copied()
                    } else {
                        None
                    };
                    // A witnessed Native data-tag church bool — its
                    // `church_true` tag, carried onto the arm shapes so the
                    // collapse is oriented per-bool (not via the program flag).
                    let datatag_ct: Option<usize> = if scott_bool {
                        None
                    } else {
                        self.datatag_conventions.get(&mid_id).copied()
                    };
                    let names = if scott_bool {
                        vec![None; branches.len()]
                    } else {
                        name_case_constructors(branches)
                    };

                    // Patterns are built for every branch before any body is
                    // lowered. Building one is a pure read (the interner is
                    // shared immutably and no id is minted), so this does not
                    // move any observable work across the descents.
                    let patterns: Vec<WhenPattern> = branches
                        .iter()
                        .zip(names)
                        .enumerate()
                        .map(|(index, (b, name))| {
                            let fields: Vec<Binder> = b
                                .binders
                                .iter()
                                .map(|id| Binder::new(self.interner.resolve(*id).to_string(), *id))
                                .collect();
                            if let Some(o) = orientation {
                                use super::bool_orientation::Orientation;
                                // constructor_known keeps tag/arity consistent
                                // with the ABI (True=1/False=0) — going through
                                // from_name_and_tag would reject the
                                // position-vs-canonical-tag mismatch.
                                let kc = match (index, o) {
                                    (0, Orientation::TrueFirst) | (1, Orientation::FalseFirst) => {
                                        KnownConstructor::True
                                    }
                                    _ => KnownConstructor::False,
                                };
                                WhenPattern::constructor_known(kc, fields)
                            } else if let Some(ct) = datatag_ct {
                                // Witnessed Native data-tag church bool: carry
                                // the per-bool `church_true` tag on an Unknown
                                // shape (NOT the CIP `Known(True/False)` that
                                // `recognize_two_branch_adt` would assign) so
                                // `summary.rs` orients true/false by THIS
                                // bool's convention, needing no program-flag
                                // swap.
                                let shape = ConstructorShape::unknown_data(b.tag, fields.len())
                                    .with_church_true(Some(ct));
                                WhenPattern::constructor(shape, fields)
                            } else {
                                let mut shape = ConstructorShape::from_name_and_tag(
                                    name.as_deref(),
                                    b.tag,
                                    fields.len(),
                                );
                                // A Scott-encoded case's tag is a continuation
                                // POSITION, not a data constructor index. Mark
                                // the (un-Known) shape ScottPositional so the
                                // Bool-table consumers (is_true/is_false) don't
                                // apply the CIP data convention to a church
                                // positional tag.
                                if encoding == CaseEncoding::Scott
                                    && let ConstructorShape::Unknown { tag, arity, .. } = shape
                                {
                                    shape = ConstructorShape::scott_positional(tag, arity);
                                }
                                WhenPattern::constructor(shape, fields)
                            }
                        })
                        .collect();

                    let body_paths: Vec<PathId> = (0..branches.len())
                        .map(|index| self.paths.child(path, index as u32 + 1))
                        .collect();
                    frames.push(Frame::CasePost {
                        mid_id,
                        path,
                        patterns,
                        branch_body_ids,
                    });
                    for (b, body_path) in branches.iter().zip(body_paths).rev() {
                        frames.push(Frame::Enter {
                            mid: &b.body,
                            path: body_path,
                        });
                    }
                }

                Frame::CasePost {
                    mid_id,
                    path,
                    patterns,
                    branch_body_ids,
                } => {
                    let bodies: Vec<PseudoExpr> = done.split_off(done.len() - patterns.len());
                    let subject = done.pop().expect("case subject");
                    let clauses: Vec<WhenClause> = patterns
                        .into_iter()
                        .zip(bodies)
                        .map(|(pattern, body)| WhenClause {
                            pattern,
                            guard: None,
                            body,
                        })
                        .collect();
                    // All branches of a well-typed Case return the same type,
                    // so the first branch with a recorded type gives the
                    // Case's expr_type; branches are not unified here.
                    if let Some(ty) = branch_body_ids
                        .iter()
                        .find_map(|id| self.type_env.type_of_expr(*id))
                    {
                        self.type_env.bind_expr(mid_id, ty);
                    }
                    let expr = PseudoExpr::When {
                        subject: PBox::new(subject),
                        subject_name: None,
                        clauses,
                    };
                    self.register_lowered(&expr, path, mid_id);
                    done.push(expr);
                }

                Frame::Force { mid_id, path, kind } => match kind {
                    ForceKind::Resolved { body } => {
                        let lowered = done.pop().expect("force resolved");
                        self.register_mid_on_expr_path(&lowered, path, mid_id);
                        self.register_mid_subtree_on_expr_path(&lowered, path, body);
                        self.register_lowered(&lowered, path, mid_id);
                        done.push(lowered);
                    }
                    ForceKind::ThunkCancel { thunk_id } => {
                        let lowered = done.pop().expect("force thunk body");
                        self.register_mid_on_expr_path(&lowered, path, mid_id);
                        self.register_mid_on_expr_path(&lowered, path, thunk_id);
                        done.push(lowered);
                    }
                    ForceKind::LetThunk {
                        let_id,
                        thunk_id,
                        var,
                        name,
                    } => {
                        let lowered_body = done.pop().expect("force let body");
                        let lowered_val = done.pop().expect("force let value");
                        let lowered =
                            PseudoExpr::let_bind_with_id(name, var, lowered_val, lowered_body);
                        self.register_mid_on_expr_path(&lowered, path, let_id);
                        let thunk_path = self.paths.child(path, 1);
                        self.register_mid_on_expr_path(&lowered, thunk_path, thunk_id);
                        self.register_lowered(&lowered, path, mid_id);
                        done.push(lowered);
                    }
                    ForceKind::Plain => {
                        let lowered = done.pop().expect("force body");
                        // Also cancel at PseudoExpr level: Force(Delay(x)) -> x
                        if let PseudoExpr::Delay(inner) = lowered {
                            let after = inner.into_inner();
                            // `before` exists only for the lineage projection.
                            // Building it clones a subtree as deep as the value,
                            // so skip it unless something will read the projection.
                            if self.track_lineage {
                                let before = PseudoExpr::Force(PBox::new(PseudoExpr::Delay(
                                    PBox::new(after.clone()),
                                )));
                                self.project_lower_rewrite_subtree(mid_id, path, &before, &after);
                            }
                            done.push(after);
                        } else {
                            let expr = PseudoExpr::Force(PBox::new(lowered));
                            self.register_lowered(&expr, path, mid_id);
                            done.push(expr);
                        }
                    }
                },

                Frame::Constr {
                    mid_id,
                    path,
                    tag,
                    count,
                } => {
                    let fields: Vec<PseudoExpr> = done.split_off(done.len() - count);
                    // At MIR time the concrete ADT name is unresolved, but a
                    // Constr's Plutus-level type is always `Data`; later naming
                    // passes specialise it once the blueprint or field-access
                    // context is known.
                    self.type_env.bind_expr(
                        mid_id,
                        std::rc::Rc::new(crate::pseudo::ast::PseudoType::Data),
                    );
                    let arity = fields.len();
                    let expr =
                        PseudoExpr::constr(ConstructorShape::unknown_data(tag, arity), fields);
                    self.register_lowered(&expr, path, mid_id);
                    done.push(expr);
                }

                Frame::Builtin {
                    mid_id,
                    path,
                    fun,
                    mid_args,
                } => {
                    let args: Vec<PseudoExpr> = done.split_off(done.len() - mid_args.len());

                    // Type only saturated calls: a partial application
                    // (`add_integer(1)`) returns a callable, not the base
                    // type, and no curried Function type is synthesized.
                    // Polymorphic builtins derive their result from the
                    // arguments' recorded expr_types instead.
                    if mid_args.len() == fun.arity() {
                        if let Some(ty) = Self::monomorphic_builtin_return_type(fun) {
                            self.type_env.bind_expr(mid_id, ty);
                        } else if let Some(ty) = self.polymorphic_builtin_return_type(fun, mid_args)
                        {
                            self.type_env.bind_expr(mid_id, ty);
                        }
                    }

                    if fun == uplc::builtins::DefaultFunction::ConstrData && args.len() == 2 {
                        let before = builtin_expr("Data.Constr", args)?;
                        let after = if self.track_lineage {
                            let after = normalize_lowered_data_expr(before.clone());
                            // Lowered via rewrite: the projection registers
                            // this node's provenance.
                            self.project_lower_rewrite_subtree(mid_id, path, &before, &after);
                            after
                        } else {
                            // No lineage reader: consume `before` instead of
                            // cloning it.
                            normalize_lowered_data_expr(before)
                        };
                        done.push(after);
                    } else {
                        let expr = lower_builtin(fun, args)?;
                        self.register_lowered(&expr, path, mid_id);
                        done.push(expr);
                    }
                }

                Frame::Apply {
                    mid_id,
                    path,
                    result_type,
                    argc,
                } => {
                    // `done` holds the callee followed by the arguments in
                    // source order, so the arguments split off the top and the
                    // callee is the one below them.
                    let args: Vec<PseudoExpr> = done.split_off(done.len() - argc);
                    let function = done.pop().expect("apply function");
                    // Bind the result type after the children are lowered.
                    if let Some(ty) = result_type {
                        self.type_env.bind_expr(mid_id, ty);
                    }
                    let expr = PseudoExpr::Apply {
                        function: PBox::new(function),
                        args: args.into(),
                    };
                    self.register_lowered(&expr, path, mid_id);
                    done.push(expr);
                }
            }
        }

        debug_assert_eq!(done.len(), 1, "lowering must leave exactly one result");
        Ok(done.pop().expect("lowering result"))
    }

    /// The shared epilogue every lowered node runs: tie the produced
    /// `PseudoExpr` back to the `MidExprId` it came from.
    ///
    /// Only the `Let` arm's rewrite path skips this, and that arm is not
    /// handled by the machine, so here it is unconditional.
    fn register_lowered(&mut self, expr: &PseudoExpr, path: PathId, mid_id: MidExprId) {
        if !self.track_lineage {
            return;
        }
        let pseudo_node_id = expr.provenance_node_id_for_path_hash(self.paths.hash(path));
        self.source_map
            .register_initial_pseudo_mid(pseudo_node_id, mid_id);
    }

    fn merge_initial_pseudo_mid(
        map: &mut std::collections::HashMap<PseudoNodeId, Vec<MidExprId>>,
        pseudo_node_id: PseudoNodeId,
        mid_id: MidExprId,
    ) {
        let mids = map.entry(pseudo_node_id).or_default();
        if !mids.contains(&mid_id) {
            mids.push(mid_id);
        }
    }

    fn merge_initial_projection(
        &mut self,
        projected: std::collections::HashMap<PseudoNodeId, Vec<MidExprId>>,
    ) {
        for (pseudo_node_id, mid_ids) in projected {
            let entry = self
                .source_map
                .initial_pseudo_to_mid
                .entry(pseudo_node_id)
                .or_default();
            for mid_id in mid_ids {
                if !entry.contains(&mid_id) {
                    entry.push(mid_id);
                }
            }
        }
    }

    fn project_lower_rewrite_subtree(
        &mut self,
        mid_id: MidExprId,
        path: PathId,
        before: &PseudoExpr,
        after: &PseudoExpr,
    ) {
        if !self.track_lineage {
            return;
        }
        let before_snapshot = snapshot_expr_at_path(before, &self.paths.indices(path));
        let after_snapshot = snapshot_expr_at_path(after, &self.paths.indices(path));

        let mut initial_subtree = std::collections::HashMap::<PseudoNodeId, Vec<MidExprId>>::new();
        for node in &before_snapshot.nodes {
            if let Some(mid_ids) = self
                .source_map
                .initial_pseudo_to_mid
                .remove(&node.pseudo_node_id)
            {
                initial_subtree.insert(node.pseudo_node_id, mid_ids);
            }
        }

        Self::merge_initial_pseudo_mid(
            &mut initial_subtree,
            before.provenance_node_id_for_path_hash(self.paths.hash(path)),
            mid_id,
        );

        let projected =
            project_final_pseudo_to_mid(&[before_snapshot, after_snapshot], &initial_subtree);
        self.merge_initial_projection(projected);
    }

    fn register_mid_on_expr_path(&mut self, expr: &PseudoExpr, path: PathId, mid_id: MidExprId) {
        // The mid -> uplc direction is consumed by a plain decompile, so it is
        // recorded either way; only the pseudo -> mid map is optional.
        let uplc_ids = self.provenance.uplc_ids(mid_id);
        self.source_map.register_mid(mid_id, &uplc_ids);
        if !self.track_lineage {
            return;
        }
        let pseudo_node_id = expr.provenance_node_id_for_path_hash(self.paths.hash(path));
        self.source_map
            .register_initial_pseudo_mid(pseudo_node_id, mid_id);
    }

    fn register_mid_subtree_on_expr_path(
        &mut self,
        expr: &PseudoExpr,
        path: PathId,
        subtree: &MidExpr,
    ) {
        let pseudo_node_id = expr.provenance_node_id_for_path_hash(self.paths.hash(path));
        let mut stack = vec![subtree];
        while let Some(current) = stack.pop() {
            let mid_id = current.id();
            let uplc_ids = self.provenance.uplc_ids(mid_id);
            self.source_map.register_mid(mid_id, &uplc_ids);
            if self.track_lineage {
                self.source_map
                    .register_initial_pseudo_mid(pseudo_node_id, mid_id);
            }
            let mut children = current.children();
            children.reverse();
            stack.extend(children);
        }
    }

    /// The leaf arms. Every node kind with children is lowered by the machine
    /// in [`Self::lower_at`], so nothing here descends and nothing re-enters
    /// the lowering — this is a flat call, whatever the tree's depth.
    fn lower_with_path_inner(&mut self, mid: &MidExpr, path: PathId) -> Result<PseudoExpr> {
        let mid_id = mid.id();

        let uplc_ids = self.provenance.uplc_ids(mid_id);
        self.source_map.register_mid(mid_id, &uplc_ids);

        let expr = match mid {
            MidExpr::Lit { value, .. } => {
                let lit_ty = Self::literal_type(value);
                self.type_env.bind_expr(mid_id, lit_ty);
                self.lower_literal(value)
            }

            MidExpr::Var { var, .. } => {
                let name = self.interner.resolve(*var).to_string();
                self.source_map.register_var(*var, name.clone());
                // Echo the binding's recorded type onto the Var's
                // MidExprId so consumers can type a use site
                // without chasing the binder.
                if let Some(ty) = self.type_env.type_of_var(*var) {
                    self.type_env.bind_expr(mid_id, ty);
                }
                PseudoExpr::var_with_id(name, *var)
            }

            MidExpr::Thunk { .. } => unreachable!("Thunk is lowered by the machine"),

            MidExpr::Force { .. } => unreachable!("Force is lowered by the machine"),

            MidExpr::Closure { .. } => unreachable!("Closure is lowered by the machine"),

            MidExpr::Apply { .. } => unreachable!("Apply is lowered by the machine"),

            MidExpr::Let { .. } => unreachable!("Let is lowered by the machine"),

            MidExpr::Builtin { .. } => unreachable!("Builtin is lowered by the machine"),

            MidExpr::Constr { .. } => unreachable!("Constr is lowered by the machine"),

            MidExpr::Case { .. } => unreachable!("Case is lowered by the machine"),

            MidExpr::If { .. } => unreachable!("If is lowered by the machine"),

            MidExpr::Error { .. } => PseudoExpr::Error { message: None },

            MidExpr::Trace { .. } => unreachable!("Trace is lowered by the machine"),

            MidExpr::Data { data, .. } => {
                // MidExpr::Data is always Plutus Data by construction.
                self.type_env.bind_expr(
                    mid_id,
                    std::rc::Rc::new(crate::pseudo::ast::PseudoType::Data),
                );
                normalize_lowered_data_expr(PseudoExpr::Data(Box::new(plutus_data_to_pseudo(data))))
            }
        };

        if self.track_lineage {
            let pseudo_node_id = expr.provenance_node_id_for_path_hash(self.paths.hash(path));
            self.source_map
                .register_initial_pseudo_mid(pseudo_node_id, mid_id);
        }
        Ok(expr)
    }

    /// Nested `List`/`Pair` literals walk a heap stack.
    fn lower_literal(&self, lit: &MidLiteral) -> PseudoExpr {
        enum Frame<'a> {
            Visit(&'a MidLiteral),
            /// Rebuild `List { elements, tail: None }` from `n` lowered
            /// elements.
            List(usize),
            /// Rebuild `Pair(a, b)` from two lowered results, `a` then `b`.
            Pair,
        }

        let mut stack: Vec<Frame> = vec![Frame::Visit(lit)];
        let mut results: Vec<PseudoExpr> = Vec::new();

        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Visit(lit) => match lit {
                    MidLiteral::Integer(n) => results.push(PseudoExpr::Int(n.clone())),
                    MidLiteral::ByteString(b) => results.push(PseudoExpr::ByteArray(b.clone())),
                    MidLiteral::String(s) => results.push(PseudoExpr::String(s.clone())),
                    MidLiteral::Bool(b) => results.push(PseudoExpr::Bool(*b)),
                    MidLiteral::Unit => results.push(PseudoExpr::Unit),
                    MidLiteral::Data(d) => results.push(normalize_lowered_data_expr(
                        PseudoExpr::Data(Box::new(plutus_data_to_pseudo(d))),
                    )),
                    MidLiteral::List(items) => {
                        stack.push(Frame::List(items.len()));
                        for item in items.iter().rev() {
                            stack.push(Frame::Visit(item));
                        }
                    }
                    MidLiteral::Pair(a, b) => {
                        stack.push(Frame::Pair);
                        stack.push(Frame::Visit(b));
                        stack.push(Frame::Visit(a));
                    }
                    MidLiteral::Bls12_381G1(_) => {
                        results.push(PseudoExpr::raw("<G1Element>", "BLS12-381"))
                    }
                    MidLiteral::Bls12_381G2(_) => {
                        results.push(PseudoExpr::raw("<G2Element>", "BLS12-381"))
                    }
                },
                Frame::List(n) => {
                    let elements = results.split_off(results.len() - n);
                    results.push(PseudoExpr::List {
                        elements: elements.into(),
                        tail: None,
                    });
                }
                Frame::Pair => {
                    let b = results.pop().unwrap();
                    let a = results.pop().unwrap();
                    results.push(PseudoExpr::Pair(PBox::new(a), PBox::new(b)));
                }
            }
        }

        results.pop().unwrap()
    }

    /// Return type of a builtin fixed by the builtin id alone (no
    /// polymorphic type variables). Builtins whose result depends on
    /// the argument types — `HeadList`, `TailList`, `FstPair`,
    /// `SndPair`, `ChooseList`, `ChooseData`, `ChooseUnit`,
    /// `IfThenElse`, `MkCons` — return `None` here and are typed by
    /// `polymorphic_builtin_return_type` instead.
    fn monomorphic_builtin_return_type(
        fun: uplc::builtins::DefaultFunction,
    ) -> Option<std::rc::Rc<crate::pseudo::ast::PseudoType>> {
        use crate::pseudo::ast::PseudoType;
        use std::rc::Rc;
        use uplc::builtins::DefaultFunction as DF;
        let ty = match fun {
            // Integer arithmetic
            DF::AddInteger
            | DF::SubtractInteger
            | DF::MultiplyInteger
            | DF::DivideInteger
            | DF::QuotientInteger
            | DF::RemainderInteger
            | DF::ModInteger => PseudoType::Int,

            // Integer / ByteString / Data / String comparisons → Bool
            DF::EqualsInteger
            | DF::LessThanInteger
            | DF::LessThanEqualsInteger
            | DF::EqualsByteString
            | DF::LessThanByteString
            | DF::LessThanEqualsByteString
            | DF::EqualsString
            | DF::EqualsData => PseudoType::Bool,

            // ByteString ops that return ByteArray
            DF::AppendByteString
            | DF::ConsByteString
            | DF::SliceByteString
            | DF::Sha2_256
            | DF::Sha3_256
            | DF::Blake2b_224
            | DF::Blake2b_256
            | DF::Keccak_256
            | DF::Ripemd_160
            | DF::IntegerToByteString
            | DF::SerialiseData
            // Logical / bitwise byte ops (CIP-122)
            | DF::AndByteString
            | DF::OrByteString
            | DF::XorByteString
            | DF::ComplementByteString
            | DF::WriteBits
            | DF::ReplicateByte
            | DF::ShiftByteString
            | DF::RotateByteString => PseudoType::ByteArray,

            // ByteString ops that return Int
            DF::LengthOfByteString
            | DF::IndexByteString
            | DF::ByteStringToInteger
            | DF::CountSetBits
            | DF::FindFirstSetBit => PseudoType::Int,

            // Single-bit read returns Bool
            DF::ReadBit => PseudoType::Bool,

            // List emptiness check
            DF::NullList => PseudoType::Bool,

            // String ops
            DF::AppendString | DF::DecodeUtf8 => PseudoType::String,
            DF::EncodeUtf8 => PseudoType::ByteArray,

            // Data constructors with concrete result types
            DF::IData | DF::BData | DF::ListData | DF::MapData | DF::ConstrData => {
                PseudoType::Data
            }

            // Data destructors with concrete (including composite) result types
            DF::UnIData => PseudoType::Int,
            DF::UnBData => PseudoType::ByteArray,
            DF::UnListData => PseudoType::List(Rc::new(PseudoType::Data)),
            DF::UnMapData => PseudoType::List(Rc::new(PseudoType::Pair(
                Rc::new(PseudoType::Data),
                Rc::new(PseudoType::Data),
            ))),
            DF::UnConstrData => PseudoType::Pair(
                Rc::new(PseudoType::Int),
                Rc::new(PseudoType::List(Rc::new(PseudoType::Data))),
            ),

            // Empty lists and pairs
            DF::MkNilData => PseudoType::List(Rc::new(PseudoType::Data)),
            DF::MkNilPairData => PseudoType::List(Rc::new(PseudoType::Pair(
                Rc::new(PseudoType::Data),
                Rc::new(PseudoType::Data),
            ))),
            DF::MkPairData => PseudoType::Pair(
                Rc::new(PseudoType::Data),
                Rc::new(PseudoType::Data),
            ),

            // Verification checks → Bool
            DF::VerifyEcdsaSecp256k1Signature
            | DF::VerifySchnorrSecp256k1Signature
            | DF::VerifyEd25519Signature
            | DF::Bls12_381_G1_Equal
            | DF::Bls12_381_G2_Equal
            | DF::Bls12_381_FinalVerify => PseudoType::Bool,

            // BLS group ops
            DF::Bls12_381_G1_Add
            | DF::Bls12_381_G1_Neg
            | DF::Bls12_381_G1_ScalarMul
            | DF::Bls12_381_G1_HashToGroup
            | DF::Bls12_381_G1_Uncompress => PseudoType::G1Element,
            DF::Bls12_381_G1_Compress => PseudoType::ByteArray,

            DF::Bls12_381_G2_Add
            | DF::Bls12_381_G2_Neg
            | DF::Bls12_381_G2_ScalarMul
            | DF::Bls12_381_G2_HashToGroup
            | DF::Bls12_381_G2_Uncompress => PseudoType::G2Element,
            DF::Bls12_381_G2_Compress => PseudoType::ByteArray,

            DF::Trace => return None, // Trace returns its second argument — polymorphic

            _ => return None,
        };
        Some(Rc::new(ty))
    }

    /// Derive a polymorphic builtin's return type from the arguments'
    /// recorded `expr_type`s.
    ///
    /// The projections read a component of the first argument's type:
    /// `HeadList(List<T>) -> T`
    /// `TailList(List<T>) -> List<T>`
    /// `FstPair(Pair<A, B>) -> A`
    /// `SndPair(Pair<A, B>) -> B`
    ///
    /// `MkCons` and `ChooseUnit` read the second argument; `IfThenElse`,
    /// `ChooseList`, and `ChooseData` unify their continuation branches.
    /// Everything else returns `None`.
    fn polymorphic_builtin_return_type(
        &self,
        fun: uplc::builtins::DefaultFunction,
        args: &[crate::pseudo::mid::expr::MidExpr],
    ) -> Option<std::rc::Rc<crate::pseudo::ast::PseudoType>> {
        use crate::pseudo::ast::PseudoType;
        use uplc::builtins::DefaultFunction as DF;
        let first_arg = args.first()?;
        let first_ty = self.type_env.type_of_expr(first_arg.id())?;
        match fun {
            DF::HeadList => {
                if let PseudoType::List(elem) = first_ty.as_ref() {
                    Some(elem.clone())
                } else {
                    None
                }
            }
            DF::TailList => {
                if let PseudoType::List(_) = first_ty.as_ref() {
                    Some(first_ty)
                } else {
                    None
                }
            }
            DF::FstPair => {
                if let PseudoType::Pair(a, _) = first_ty.as_ref() {
                    Some(a.clone())
                } else {
                    None
                }
            }
            DF::SndPair => {
                if let PseudoType::Pair(_, b) = first_ty.as_ref() {
                    Some(b.clone())
                } else {
                    None
                }
            }
            // MkCons(elem: T, tail: List<T>) -> List<T>. A missing or
            // Unknown tail type falls back to `List<first_ty>`; a KNOWN
            // non-list tail yields no type at all, so the contradiction
            // stays visible instead of being papered over.
            DF::MkCons => {
                let second_arg = args.get(1)?;
                match self.type_env.type_of_expr(second_arg.id()) {
                    Some(ty) if matches!(ty.as_ref(), PseudoType::List(_)) => Some(ty),
                    Some(ty) if matches!(ty.as_ref(), PseudoType::Unknown) => {
                        Some(std::rc::Rc::new(PseudoType::List(first_ty)))
                    }
                    Some(_) => None, // contradiction: tail is not a list
                    None => Some(std::rc::Rc::new(PseudoType::List(first_ty))),
                }
            }
            // ChooseUnit(_: unit, k: T) -> T. The continuation is the
            // second argument; its expr_type is the whole expression's
            // type. Pre-compute has usually already unwrapped a Delay
            // around it.
            DF::ChooseUnit => {
                let second_arg = args.get(1)?;
                self.type_env.type_of_expr(second_arg.id())
            }
            // IfThenElse(cond, then_thunk, else_thunk) -> T where both
            // branches produce T; `branch_type_through_thunk` peels the
            // Thunk wrappers before unification.
            DF::IfThenElse => Self::unify_branch_types(&[
                Self::branch_type_through_thunk(&self.type_env, args.get(1)?),
                Self::branch_type_through_thunk(&self.type_env, args.get(2)?),
            ]),
            // ChooseList(list, if_empty, if_non_empty) -> T.
            DF::ChooseList => Self::unify_branch_types(&[
                Self::branch_type_through_thunk(&self.type_env, args.get(1)?),
                Self::branch_type_through_thunk(&self.type_env, args.get(2)?),
            ]),
            // ChooseData(data, on_constr, on_map, on_list, on_int,
            // on_bytestring) -> T. All 5 continuation branches share T.
            DF::ChooseData => {
                let branches: Vec<_> = args
                    .iter()
                    .skip(1)
                    .map(|arg| Self::branch_type_through_thunk(&self.type_env, arg))
                    .collect();
                Self::unify_branch_types(&branches)
            }
            _ => None,
        }
    }

    /// Unify branch expr_type entries: prefer the most specific
    /// (non-`Unknown`) type, `None` when no branch has a type,
    /// and `None` again when two concrete types disagree —
    /// picking one would lock a wrong type in downstream.
    fn unify_branch_types(
        branches: &[Option<std::rc::Rc<crate::pseudo::ast::PseudoType>>],
    ) -> Option<std::rc::Rc<crate::pseudo::ast::PseudoType>> {
        use crate::pseudo::ast::PseudoType;
        let mut chosen: Option<std::rc::Rc<PseudoType>> = None;
        for candidate in branches.iter().flatten() {
            let is_unknown = matches!(candidate.as_ref(), PseudoType::Unknown);
            match &chosen {
                None => chosen = Some(candidate.clone()),
                Some(existing) => {
                    let existing_unknown = matches!(existing.as_ref(), PseudoType::Unknown);
                    if existing_unknown && !is_unknown {
                        chosen = Some(candidate.clone());
                    } else if !existing_unknown
                        && !is_unknown
                        && existing.as_ref() != candidate.as_ref()
                    {
                        // Concrete types disagree; None beats a guess.
                        return None;
                    }
                }
            }
        }
        chosen
    }

    /// Look up a branch's effective type through any chain of Thunk
    /// wrappers, so `Thunk(Thunk(body))` still returns the body's
    /// type: cosmetic thunks stack in post-pattern MIR when both a
    /// force-guard wrapper and a lazy-body wrapper survive.
    fn branch_type_through_thunk(
        env: &TypeEnvironment,
        arg: &crate::pseudo::mid::expr::MidExpr,
    ) -> Option<std::rc::Rc<crate::pseudo::ast::PseudoType>> {
        use crate::pseudo::mid::expr::MidExpr;
        let mut cursor = arg;
        loop {
            match cursor {
                MidExpr::Thunk { body, .. } => cursor = body,
                _ => return env.type_of_expr(cursor.id()),
            }
        }
    }

    /// Map a MidLiteral to its static PseudoType.
    ///
    /// Compound literals (List / Pair) recurse so the outermost type
    /// reflects the literal's shape; the children get no entry of their
    /// own, their MidExprId not being available at this call site.
    fn literal_type(lit: &MidLiteral) -> std::rc::Rc<crate::pseudo::ast::PseudoType> {
        use crate::pseudo::ast::PseudoType;
        use std::rc::Rc;
        match lit {
            MidLiteral::Integer(_) => Rc::new(PseudoType::Int),
            MidLiteral::ByteString(_) => Rc::new(PseudoType::ByteArray),
            MidLiteral::String(_) => Rc::new(PseudoType::String),
            MidLiteral::Bool(_) => Rc::new(PseudoType::Bool),
            MidLiteral::Unit => Rc::new(PseudoType::Unit),
            MidLiteral::Data(_) => Rc::new(PseudoType::Data),
            MidLiteral::List(items) => {
                let elem = items
                    .first()
                    .map(Self::literal_type)
                    .unwrap_or_else(|| Rc::new(PseudoType::Unknown));
                Rc::new(PseudoType::List(elem))
            }
            MidLiteral::Pair(a, b) => Rc::new(PseudoType::Pair(
                Self::literal_type(a),
                Self::literal_type(b),
            )),
            MidLiteral::Bls12_381G1(_) => Rc::new(PseudoType::G1Element),
            MidLiteral::Bls12_381G2(_) => Rc::new(PseudoType::G2Element),
        }
    }

    fn seed_simplify_state(
        &mut self,
        var: crate::pseudo::var_id::VarId,
        name: &str,
        value: &PseudoExpr,
    ) {
        if let PseudoExpr::BuiltinCall {
            name: builtin_name,
            args,
        } = value
        {
            if args.is_empty() {
                self.simplify_state.naming.builtin_aliases.insert_binding(
                    name.to_string(),
                    Some(var),
                    *builtin_name,
                );
            }

            if (*builtin_name == crate::BuiltinId::ConstrUnpack
                || *builtin_name == crate::BuiltinId::DataUnConstr)
                && args.len() == 1
            {
                self.simplify_state
                    .constructors
                    .constr_unpack_subjects
                    .insert_binding(name.to_string(), Some(var), args[0].clone());
            }
        }
    }
}

/// Which of `Force`'s shapes a [`Frame::Force`] is finishing.
///
/// The shape is decided on the way down and carried across the descent so
/// the continuation can rebuild the right node.
enum ForceKind<'m> {
    /// `resolved` was present: the lowered result stands in for this node.
    Resolved { body: &'m MidExpr },
    /// `Force(Thunk(x))` cancelled — `x`'s lowering stands in for both nodes.
    ThunkCancel { thunk_id: MidExprId },
    /// `Force(Let(v, val, Thunk(x)))` -> `Let(v, val, x)`.
    LetThunk {
        let_id: MidExprId,
        thunk_id: MidExprId,
        var: crate::pseudo::var_id::VarId,
        name: String,
    },
    /// Anything else: rebuild `Force`, cancelling `Force(Delay(x))`.
    Plain,
}

/// One pending step of [`Lowerer::lower_at`].
///
/// Every variant other than `Enter` is a continuation: rebuild the node
/// after its children, holding the fields that are not children.
enum Frame<'m> {
    /// Lower this node.
    Enter { mid: &'m MidExpr, path: PathId },
    Thunk {
        mid_id: MidExprId,
        path: PathId,
        cosmetic: bool,
    },
    Closure {
        mid_id: MidExprId,
        path: PathId,
        param_binders: Vec<crate::pseudo::ast::Binder>,
        recursive: Option<crate::pseudo::var_id::VarId>,
    },
    /// Rebuild `If` once condition, then- and else-branch are lowered.
    If {
        mid_id: MidExprId,
        path: PathId,
        then_id: MidExprId,
        else_id: MidExprId,
    },
    /// Rebuild `Trace` once message and body are lowered.
    Trace {
        mid_id: MidExprId,
        path: PathId,
        body_mid_id: MidExprId,
    },
    /// The work a `Let` does *between* its value and its body: bind the
    /// value's type onto the binder and emit a signature if it bound a
    /// closure. The body is lowered after this, so it sees both.
    LetBetween {
        var: crate::pseudo::var_id::VarId,
        name: String,
        value_mid_id: MidExprId,
        closure_signature_info: Option<(Vec<crate::pseudo::var_id::VarId>, MidExprId, bool)>,
    },
    /// Rebuild `Let` once value and body are lowered.
    LetPost {
        mid_id: MidExprId,
        path: PathId,
        var: crate::pseudo::var_id::VarId,
        name: String,
    },
    /// Build the clause patterns and descend into the branch bodies, once the
    /// scrutinee is lowered.
    CaseBranches {
        mid_id: MidExprId,
        path: PathId,
        branches: &'m [MidBranch],
        encoding: CaseEncoding,
        branch_body_ids: Vec<MidExprId>,
    },
    /// Rebuild `When` once the scrutinee and every branch body are lowered.
    CasePost {
        mid_id: MidExprId,
        path: PathId,
        patterns: Vec<WhenPattern>,
        branch_body_ids: Vec<MidExprId>,
    },
    /// Finish a `Force`, whose shape decides what gets rebuilt.
    Force {
        mid_id: MidExprId,
        path: PathId,
        kind: ForceKind<'m>,
    },
    /// Rebuild `Constr` once all `count` fields are lowered.
    Constr {
        mid_id: MidExprId,
        path: PathId,
        tag: usize,
        count: usize,
    },
    /// Rebuild a non-folded `Builtin` once all its arguments are lowered.
    ///
    /// `mid_args` rides along because the result type of a polymorphic builtin
    /// is derived from the *mid* arguments, not the lowered ones.
    Builtin {
        mid_id: MidExprId,
        path: PathId,
        fun: uplc::builtins::DefaultFunction,
        mid_args: &'m [MidExpr],
    },
    /// Rebuild `Apply` once the callee and all `argc` arguments are lowered.
    ///
    /// `result_type` is read off the callee's signature *before* its children
    /// are lowered, because lowering consumes the `MidExpr` shape the peek
    /// needs — so it travels on the frame rather than being recomputed here.
    Apply {
        mid_id: MidExprId,
        path: PathId,
        result_type: Option<std::rc::Rc<crate::pseudo::ast::PseudoType>>,
        argc: usize,
    },
}

/// A node's path from the root of the tree being lowered.
///
/// An index into [`PathArena`], not the path itself — `Copy`, 4 bytes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct PathId(u32);

/// Paths from the root, stored as parent links plus a rolling hash rather than
/// as an absolute `Vec<u32>` per node.
///
/// An absolute path of length `depth` at every node is O(n²) memory and
/// hashing on a deep spine, which exhausts the wasm heap before lowering
/// finishes. A parent link plus the incremental hash is O(1) per node. Almost
/// every consumer only wants the hash (it is all a `PseudoNodeId` is derived
/// from); the full index list is materialized only by the few callers that
/// genuinely need to walk it, via [`PathArena::indices`].
pub(crate) struct PathArena {
    /// `(parent, index within the parent, rolling hash of the whole path)`.
    /// Entry 0 is the root: no parent, and the empty path's hash.
    nodes: Vec<(Option<PathId>, u32, u64)>,
}

impl PathArena {
    fn new() -> Self {
        Self {
            nodes: vec![(None, 0, PseudoExpr::root_path_hash())],
        }
    }

    /// The empty path.
    fn root(&self) -> PathId {
        PathId(0)
    }

    /// The path of `parent`'s `child_index`-th child.
    fn child(&mut self, parent: PathId, child_index: u32) -> PathId {
        let hash = PseudoExpr::extend_path_hash(self.hash(parent), child_index);
        self.nodes.push((Some(parent), child_index, hash));
        PathId((self.nodes.len() - 1) as u32)
    }

    /// The rolling hash of this path. Equal to hashing the materialized
    /// indices left to right, which is what `stable_path_hash` does.
    fn hash(&self, path: PathId) -> u64 {
        self.nodes[path.0 as usize].2
    }

    /// The path as child indices, root first. O(depth) — only for callers that
    /// really need to walk it.
    fn indices(&self, path: PathId) -> Vec<u32> {
        let mut out = Vec::new();
        let mut cursor = Some(path);
        while let Some(node) = cursor {
            let (parent, index, _) = self.nodes[node.0 as usize];
            // The root contributes no index.
            if parent.is_none() {
                break;
            }
            out.push(index);
            cursor = parent;
        }
        out.reverse();
        out
    }
}

/// Infer constructor names from Case branch patterns.
///
/// A two-branch Case is often identifiable from the branches'
/// `(tag, arity)` pairs. Delegates to
/// [`KnownConstructor::recognize_two_branch_adt`] so the recognition
/// table lives in one place; any other branch count or shape yields
/// `None`s.
fn name_case_constructors(branches: &[MidBranch]) -> Vec<Option<String>> {
    if let [a, b] = branches
        && let Some((kc_a, kc_b)) = KnownConstructor::recognize_two_branch_adt(
            (a.tag, a.binders.len()),
            (b.tag, b.binders.len()),
        )
    {
        return vec![
            Some(kc_a.pretty_name().to_string()),
            Some(kc_b.pretty_name().to_string()),
        ];
    }
    branches.iter().map(|_| None).collect()
}

/// Stage label `BuiltinId::parse_known` reports when a
/// builtin name fails to resolve during lowering.
const MIR_LOWER_BUILTIN_STAGE: &str = "mir_lower_builtin";

fn builtin_expr(name: &'static str, args: Vec<PseudoExpr>) -> Result<PseudoExpr> {
    Ok(PseudoExpr::BuiltinCall {
        name: BuiltinId::parse_known(name, MIR_LOWER_BUILTIN_STAGE)?,
        args: args.into(),
    })
}

fn lower_builtin(
    fun: uplc::builtins::DefaultFunction,
    args: Vec<PseudoExpr>,
) -> Result<PseudoExpr> {
    use uplc::builtins::DefaultFunction::*;

    match (fun, args.as_slice()) {
        // Pair access → FieldAccess
        (FstPair, [_]) => {
            let record = args.into_iter().next().unwrap();
            Ok(PseudoExpr::field_access_typed(
                record,
                FieldSelector::PairFst,
            ))
        }
        (SndPair, [_]) => {
            let record = args.into_iter().next().unwrap();
            Ok(PseudoExpr::field_access_typed(
                record,
                FieldSelector::PairSnd,
            ))
        }
        // List operations → FieldAccess/BuiltinCall
        (HeadList, [_]) => {
            let list = args.into_iter().next().unwrap();
            Ok(PseudoExpr::field_access_typed(
                list,
                FieldSelector::ListHead,
            ))
        }
        (TailList, [_]) => {
            let list = args.into_iter().next().unwrap();
            builtin_expr("List.tail", vec![list])
        }
        // Data constructors & destructors → direct PseudoExpr forms
        (UnConstrData, [_]) => {
            let data = args.into_iter().next().unwrap();
            builtin_expr("Constr.unpack", vec![data])
        }
        // ConstrData(tag, fields) → Data.Constr(tag, fields)
        (ConstrData, [_, _]) => {
            let mut it = args.into_iter();
            let tag = it.next().unwrap();
            let fields = it.next().unwrap();
            Ok(normalize_lowered_data_expr(builtin_expr(
                "Data.Constr",
                vec![tag, fields],
            )?))
        }
        // Data constructors
        (IData, [_]) => builtin_expr("Data.Int", args),
        (BData, [_]) => builtin_expr("Data.ByteArray", args),
        (ListData, [_]) => builtin_expr("Data.List", args),
        (MapData, [_]) => builtin_expr("Data.Map", args),
        // Data destructors
        (UnIData, [_]) => builtin_expr("Data.un_int", args),
        (UnBData, [_]) => builtin_expr("Data.un_bytearray", args),
        (UnListData, [_]) => builtin_expr("Data.un_list", args),
        (UnMapData, [_]) => builtin_expr("Data.un_map", args),
        // MkCons → List.cons
        (MkCons, [_, _]) => builtin_expr("List.cons", args),
        // NullList → List.is_empty
        (NullList, [_]) => builtin_expr("List.is_empty", args),
        // MkPairData → Pair.new
        (MkPairData, [_, _]) => builtin_expr("Pair.new", args),
        // Arithmetic → BinOp
        (AddInteger, [_, _]) => Ok(binop(BinaryOp::Add, args)),
        (SubtractInteger, [_, _]) => Ok(binop(BinaryOp::Sub, args)),
        (MultiplyInteger, [_, _]) => Ok(binop(BinaryOp::Mul, args)),
        (DivideInteger, [_, _]) => Ok(binop(BinaryOp::Div, args)),
        (ModInteger, [_, _]) => Ok(binop(BinaryOp::Mod, args)),

        // Comparison → BinOp
        (EqualsInteger, [_, _])
        | (EqualsByteString, [_, _])
        | (EqualsString, [_, _])
        | (EqualsData, [_, _]) => Ok(binop(BinaryOp::Eq, args)),
        (LessThanInteger, [_, _]) | (LessThanByteString, [_, _]) => Ok(binop(BinaryOp::Lt, args)),
        (LessThanEqualsInteger, [_, _]) | (LessThanEqualsByteString, [_, _]) => {
            Ok(binop(BinaryOp::Lte, args))
        }

        // String/Bytes → BinOp
        (AppendByteString, [_, _]) | (AppendString, [_, _]) => Ok(binop(BinaryOp::Concat, args)),

        // Everything else → BuiltinCall with surface-style name
        _ => Ok(PseudoExpr::BuiltinCall {
            name: pseudonym_builtin_id(fun)?,
            args: args.into(),
        }),
    }
}

/// Surface tokens the renderer can print for a UPLC builtin.
///
/// Derived by calling [`lower_builtin`] at every arity it accepts and
/// reading back the shape it chose, plus the builtin's own display
/// names, so the set cannot drift from the real lowering.
///
/// Diagnostics only (`src/bin/line_audit.rs`): the *name* half of a
/// witness for "does the line a term is mapped to mention that term".
/// It omits the renderer's later sugar (index brackets for list spines,
/// `when` for a recovered destructure), so callers that want those add
/// them explicitly and the widening stays visible at the use site.
pub(crate) fn builtin_render_surface_forms(fun: uplc::builtins::DefaultFunction) -> Vec<String> {
    use crate::builtins::BuiltinDisplayStyle;

    fn push(forms: &mut Vec<String>, form: &str) {
        if !form.is_empty() && !forms.iter().any(|existing| existing == form) {
            forms.push(form.to_string());
        }
    }
    fn push_names(forms: &mut Vec<String>, id: BuiltinId) {
        push(forms, id.display_name(BuiltinDisplayStyle::Pretty));
        push(forms, id.canonical_name());
    }

    let mut forms: Vec<String> = Vec::new();
    if let Ok(id) = pseudonym_builtin_id(fun) {
        push_names(&mut forms, id);
    }

    // Every arity: a builtin applied to fewer arguments than it consumes stays
    // a `BuiltinCall` and prints its name, while the saturated form may become
    // an operator or an accessor.
    for arity in 1..=3usize {
        let args: Vec<PseudoExpr> = (0..arity)
            .map(|i| PseudoExpr::var(format!("__audit_arg_{i}")))
            .collect();
        let Ok(lowered) = lower_builtin(fun, args) else {
            continue;
        };
        match lowered {
            PseudoExpr::BinOp { op, .. } => push(&mut forms, op.symbol()),
            PseudoExpr::BuiltinCall { name, .. } => push_names(&mut forms, name),
            PseudoExpr::FieldAccess { selector, .. } => {
                push(&mut forms, &format!(".{}", selector.as_surface_accessor()));
                push(&mut forms, &format!(".{}", selector.as_pretty_name()));
            }
            _ => {}
        }
    }

    forms
}

/// Only Data-shaped kinds (`Data.Constr` calls, `Data`, `List`, `Pair`).
/// Embedded Lambda/Let is left alone.
fn normalize_lowered_data_expr(expr: PseudoExpr) -> PseudoExpr {
    enum Frame {
        /// Rebuild `BuiltinCall { DataConstr, [tag, fields] }` from the two
        /// normalized child results (tag first, then fields).
        DataConstr,
        /// Rebuild `List { elements, tail }` from `n` normalized elements
        /// followed by (if `has_tail`) one normalized tail.
        List {
            n: usize,
            has_tail: bool,
        },
        Pair,
    }
    enum Step {
        Visit(PseudoExpr),
        Build(Frame),
    }

    let mut stack: Vec<Step> = vec![Step::Visit(expr)];
    let mut results: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = stack.pop() {
        match step {
            Step::Visit(e) => match e {
                PseudoExpr::BuiltinCall { name, args }
                    if *name == crate::BuiltinId::DataConstr && args.len() == 2 =>
                {
                    let mut args = args.into_iter();
                    let tag_expr = args.next().unwrap();
                    let fields_expr = args.next().unwrap();
                    stack.push(Step::Build(Frame::DataConstr));
                    stack.push(Step::Visit(fields_expr));
                    stack.push(Step::Visit(tag_expr));
                }
                PseudoExpr::Data(data) => {
                    results.push(normalize_convertible_data_expr(PseudoExpr::Data(data)));
                }
                PseudoExpr::List { elements, tail } => {
                    let n = elements.len();
                    let has_tail = tail.is_some();
                    stack.push(Step::Build(Frame::List { n, has_tail }));
                    if let Some(tail) = tail {
                        stack.push(Step::Visit(tail.into_inner()));
                    }
                    for element in elements.into_iter().rev() {
                        stack.push(Step::Visit(element));
                    }
                }
                PseudoExpr::Pair(left, right) => {
                    stack.push(Step::Build(Frame::Pair));
                    stack.push(Step::Visit(right.into_inner()));
                    stack.push(Step::Visit(left.into_inner()));
                }
                other => results.push(other),
            },
            Step::Build(frame) => match frame {
                Frame::DataConstr => {
                    let fields_expr = results.pop().unwrap();
                    let tag_expr = results.pop().unwrap();
                    results.push(normalize_constructor_data_expr(tag_expr, fields_expr));
                }
                Frame::List { n, has_tail } => {
                    let tail = if has_tail {
                        Some(PBox::new(results.pop().unwrap()))
                    } else {
                        None
                    };
                    let mut elements = Vec::with_capacity(n);
                    for _ in 0..n {
                        elements.push(results.pop().unwrap());
                    }
                    elements.reverse();
                    results.push(PseudoExpr::List {
                        elements: elements.into(),
                        tail,
                    });
                }
                Frame::Pair => {
                    let right = results.pop().unwrap();
                    let left = results.pop().unwrap();
                    results.push(PseudoExpr::Pair(PBox::new(left), PBox::new(right)));
                }
            },
        }
    }

    debug_assert_eq!(
        results.len(),
        1,
        "normalize_lowered_data_expr: imbalanced stack"
    );
    results.pop().unwrap()
}

fn binop(op: BinaryOp, mut args: Vec<PseudoExpr>) -> PseudoExpr {
    let right = args.pop().unwrap();
    let left = args.pop().unwrap();
    PseudoExpr::BinOp {
        op,
        left: PBox::new(left),
        right: PBox::new(right),
    }
}

/// Map a UPLC builtin to the [`BuiltinId`] whose canonical name is this
/// crate's internal pseudonym for it (`List.head`, `Data.Constr`, …).
///
/// The pseudonym is not what reaches the page. Rendering goes through
/// [`BuiltinId::display_name`], which prints the compilable `builtin.*` form
/// for the whole `Data.*` family by default; only a few data-access builtins
/// keep the pseudonym, and only until the compilable-data-access option is on.
fn pseudonym_builtin_id(fun: uplc::builtins::DefaultFunction) -> Result<BuiltinId> {
    use uplc::builtins::DefaultFunction::*;
    let name = match fun {
        AddInteger => "add_integer",
        SubtractInteger => "subtract_integer",
        MultiplyInteger => "multiply_integer",
        DivideInteger => "divide_integer",
        QuotientInteger => "quotient_integer",
        RemainderInteger => "remainder_integer",
        ModInteger => "mod_integer",
        EqualsInteger => "equals_integer",
        LessThanInteger => "less_than_integer",
        LessThanEqualsInteger => "less_than_equals_integer",
        AppendByteString => "ByteArray.concat",
        ConsByteString => "ByteArray.push",
        SliceByteString => "ByteArray.slice",
        LengthOfByteString => "ByteArray.length",
        IndexByteString => "ByteArray.at",
        EqualsByteString => "equals_bytearray",
        LessThanByteString => "less_than_bytearray",
        LessThanEqualsByteString => "less_than_equals_bytearray",
        Sha2_256 => "sha2_256",
        Sha3_256 => "sha3_256",
        Blake2b_256 => "blake2b_256",
        Blake2b_224 => "blake2b_224",
        Keccak_256 => "keccak_256",
        VerifyEd25519Signature => "verify_ed25519_signature",
        AppendString => "String.concat",
        EqualsString => "equals_string",
        EncodeUtf8 => "encode_utf8",
        DecodeUtf8 => "decode_utf8",
        IfThenElse => "if_then_else",
        ChooseUnit => "choose_unit",
        Trace => "trace",
        FstPair => "Pair.first",
        SndPair => "Pair.second",
        ChooseList => "choose_list",
        MkCons => "List.cons",
        HeadList => "List.head",
        TailList => "List.tail",
        NullList => "List.is_empty",
        ChooseData => "choose_data",
        ConstrData => "Data.Constr",
        MapData => "Data.Map",
        ListData => "Data.List",
        IData => "Data.Int",
        BData => "Data.ByteArray",
        UnConstrData => "Data.un_constr",
        UnMapData => "Data.un_map",
        UnListData => "Data.un_list",
        UnIData => "Data.un_int",
        UnBData => "Data.un_bytearray",
        EqualsData => "equals_data",
        MkPairData => "Pair.new",
        MkNilData => "List.empty",
        MkNilPairData => "List.empty_pairs",
        SerialiseData => "serialise_data",
        VerifyEcdsaSecp256k1Signature => "verify_ecdsa_secp256k1",
        VerifySchnorrSecp256k1Signature => "verify_schnorr_secp256k1",
        Ripemd_160 => "ripemd_160",
        IntegerToByteString => "int_to_bytearray",
        ByteStringToInteger => "bytearray_to_int",
        // BLS12-381 builtins. The snake_case names below are the ones
        // `BuiltinId::from_name` accepts; the `Debug` spelling
        // (`Bls12_381_G1_ScalarMul`) is not, and `parse_known` fails
        // the whole script on an unrecognised name.
        Bls12_381_G1_Add => "bls12_381_g1_add",
        Bls12_381_G1_Neg => "bls12_381_g1_neg",
        Bls12_381_G1_ScalarMul => "bls12_381_g1_scalar_mul",
        Bls12_381_G1_Equal => "bls12_381_g1_equal",
        Bls12_381_G1_Compress => "bls12_381_g1_compress",
        Bls12_381_G1_Uncompress => "bls12_381_g1_uncompress",
        Bls12_381_G1_HashToGroup => "bls12_381_g1_hash_to_group",
        Bls12_381_G2_Add => "bls12_381_g2_add",
        Bls12_381_G2_Neg => "bls12_381_g2_neg",
        Bls12_381_G2_ScalarMul => "bls12_381_g2_scalar_mul",
        Bls12_381_G2_Equal => "bls12_381_g2_equal",
        Bls12_381_G2_Compress => "bls12_381_g2_compress",
        Bls12_381_G2_Uncompress => "bls12_381_g2_uncompress",
        Bls12_381_G2_HashToGroup => "bls12_381_g2_hash_to_group",
        Bls12_381_MillerLoop => "bls12_381_miller_loop",
        Bls12_381_MulMlResult => "bls12_381_mul_miller_loop_result",
        Bls12_381_FinalVerify => "bls12_381_final_verify",
        // Conway-era bytestring bit-operation builtins. Like the BLS
        // group, these need explicit names: the snake_case spellings
        // below are the aliases `BuiltinId::from_name` accepts.
        AndByteString => "and_bytearray",
        OrByteString => "or_bytearray",
        XorByteString => "xor_bytearray",
        ComplementByteString => "complement_bytearray",
        ReadBit => "read_bit",
        WriteBits => "write_bits",
        ReplicateByte => "replicate_byte",
        ShiftByteString => "shift_bytearray",
        RotateByteString => "rotate_bytearray",
        CountSetBits => "count_set_bits",
        FindFirstSetBit => "find_first_set_bit",
    };
    BuiltinId::parse_known(name, MIR_LOWER_BUILTIN_STAGE)
}

/// Convert `uplc::PlutusData` to `pseudo::ast::PseudoData`,
/// delegating to `basic.rs`, which handles the pallas types.
fn plutus_data_to_pseudo(data: &uplc::PlutusData) -> crate::pseudo::ast::PseudoData {
    super::super::basic::convert_plutus_data(data)
}

/// Disambiguate binding names within Closures and their bodies.
///
/// The rec_var, params, and Let-bound vars of one Closure can all
/// carry the same DeBruijn name ("v"), which collides once PseudoExpr
/// keys on strings; duplicates are renamed so each binding site is
/// unique within its Closure scope.
pub(crate) fn disambiguate_all_bindings(expr: &MidExpr, interner: &mut VarInterner) {
    enum Step<'a> {
        Visit(&'a MidExpr),
        /// Drop the scope a closure body was walked under.
        PopScope,
    }

    // Innermost entry is the scope in force. `None` means outside any
    // closure: a `let` binder there is left alone. A closure's fresh
    // scope covers exactly its body.
    let mut scopes: Vec<Option<std::collections::HashMap<String, usize>>> = vec![None];
    let mut steps: Vec<Step<'_>> = vec![Step::Visit(expr)];

    while let Some(step) = steps.pop() {
        match step {
            Step::PopScope => {
                scopes.pop();
            }
            Step::Visit(expr) => match expr {
                MidExpr::Closure {
                    params,
                    body,
                    recursive,
                    ..
                } => {
                    // Start fresh scope for this Closure
                    let mut seen = std::collections::HashMap::<String, usize>::new();
                    if let Some(rec_var) = recursive {
                        let rec_name = interner.resolve(*rec_var).to_string();
                        seen.insert(rec_name, 1);
                    }
                    for p in params {
                        let name = interner.resolve(*p).to_string();
                        let count = seen.entry(name.clone()).or_insert(0);
                        *count += 1;
                        if *count > 1 {
                            interner.rename(*p, &format!("{}_{}", name, count));
                        }
                    }
                    // The scope reaches the body so Let-bound vars are also
                    // disambiguated against the params.
                    scopes.push(Some(seen));
                    steps.push(Step::PopScope);
                    steps.push(Step::Visit(body));
                }
                MidExpr::Let { var, .. } => {
                    // If inside a Closure, disambiguate this Let var against Closure scope
                    if let Some(seen) = scopes.last_mut().expect("scope stack is never empty") {
                        let name = interner.resolve(*var).to_string();
                        let count = seen.entry(name.clone()).or_insert(0);
                        *count += 1;
                        if *count > 1 {
                            interner.rename(*var, &format!("{}_{}", name, count));
                        }
                    }
                    for child in expr.children().into_iter().rev() {
                        steps.push(Step::Visit(child));
                    }
                }
                other => {
                    for child in other.children().into_iter().rev() {
                        steps.push(Step::Visit(child));
                    }
                }
            },
        }
    }
}

/// Run the full MIR pipeline: translate → analyze → precompute → lower.
pub(crate) fn decompile_via_mir_output(
    program: &uplc::ast::Program<uplc::ast::NamedDeBruijn>,
    script_version: Option<crate::decompile::ScriptVersion>,
) -> Result<MirDecompileOutput> {
    decompile_via_mir_output_with_options(program, script_version, false, true)
}

/// Run the full MIR pipeline; `safe_mode` skips the aggressive
/// rewrites (inverse cancellation, Y-combinator heuristics).
pub(crate) fn decompile_via_mir_output_with_options(
    program: &uplc::ast::Program<uplc::ast::NamedDeBruijn>,
    script_version: Option<crate::decompile::ScriptVersion>,
    safe_mode: bool,
    track_lineage: bool,
) -> Result<MirDecompileOutput> {
    use super::analyze::run_analysis;
    use super::patterns::seed_validator_params;
    use super::precompute::run_precompute;
    use super::translate::MidTranslator;

    // Translate
    let mut translator = MidTranslator::new();
    let mut mid = translator.translate(&program.term);
    super::validate::enforce_mid_invariants("translate", &mid, &translator.provenance)?;

    // Seed validator parameter names from Plutus version
    seed_validator_params(&mid, script_version, &mut translator.var_registry);

    // Analyze (use counting + abstract interpretation env updates)
    run_analysis(&mut mid);

    // Pre-compute (patterns, force resolution, inverse cancellation, DCE)
    run_precompute(&mut mid, &mut translator.provenance, safe_mode);
    super::validate::enforce_mid_invariants("precompute", &mid, &translator.provenance)?;

    // Precompute (inlining, dead code elimination, Y-comb conversion)
    // invalidates the use_count from the earlier analysis, so re-run it.
    run_analysis(&mut mid);
    super::validate::enforce_mid_invariants("analysis_refresh", &mid, &translator.provenance)?;

    // Closure params that share a name need unique display names for PseudoExpr.
    // Let binders are disambiguated only inside a Closure scope — the
    // simplifier relies on name equality for f(f) self-application cleanup.
    disambiguate_all_bindings(&mid, &mut translator.interner);
    translator
        .var_registry
        .sync_display_names(&translator.interner);

    // Producer-witnessed church-bool orientations for the
    // Scott 2x0-binder cases. Runs on the final pre-lower tree so the
    // witnesses key the exact Case ids the lowering will see.
    let bool_orientations = super::bool_orientation::analyze_bool_orientations(&mid);
    // Per-bool data-tag church-bool conventions (Native
    // `if c {Constr<a>} else {Constr<b>}` -> church_true=a), keyed by the
    // consumer Case id. Seeds the per-bool collapse orientation below.
    let datatag_conventions = super::bool_orientation::analyze_datatag_church_conventions(&mid);

    // Lower
    let mut lowerer = Lowerer::new(&translator.interner, &translator.provenance)
        .with_lineage_tracking(track_lineage);
    lowerer.bool_orientations = bool_orientations;
    lowerer.datatag_conventions = datatag_conventions;
    let pseudo = lowerer.lower(&mid)?;

    // The mid tree is finished. Drop it on a heap stack: the generated
    // destructor would otherwise take one call-stack frame per level.
    crate::pseudo::mid::expr::drop_iteratively(mid);

    let mut type_env = lowerer.type_env;
    type_env.freeze();

    Ok(MirDecompileOutput {
        pseudo,
        source_map: lowerer.source_map,
        var_registry: translator.var_registry,
        simplify_state: lowerer.simplify_state,
        type_env: std::rc::Rc::new(type_env),
    })
}

pub(crate) fn decompile_via_mir(
    program: &uplc::ast::Program<uplc::ast::NamedDeBruijn>,
    script_version: Option<crate::decompile::ScriptVersion>,
) -> Result<(PseudoExpr, SourceMap, super::var_registry::VarRegistry)> {
    let output = decompile_via_mir_output(program, script_version)?;
    Ok((output.pseudo, output.source_map, output.var_registry))
}

/// Build source spans by matching rendered pseudo-node spans to MidExpr IDs.
///
/// Uses the projected pseudo-node -> mid lineage when the source map has
/// one; otherwise distributes mids proportionally over the rendered spans
/// in pretty-printed order, which is an approximation but deterministic.
fn finalize_source_map_from_rendered_spans(
    rendered_spans: &[(
        crate::pseudo::ast::PseudoNodeId,
        crate::pseudo::mid::expr_id::SourceSpan,
    )],
    source_map: &mut SourceMap,
) -> bool {
    use crate::pseudo::mid::expr_id::{MidExprId, SourceSpan};

    if rendered_spans.is_empty() {
        return false;
    }

    if !source_map.final_pseudo_to_mid.is_empty() {
        // Claim order: the SMALLEST projected lineage claims its mids first.
        // The lineage is a containment view: a node carries its own mids
        // and its subtree's, so the smallest set containing a mid belongs to
        // the deepest — most specific — carrier that owns it. Ordering by
        // span specificity alone lets a narrow-span node with a huge
        // inherited union claim most of the program onto one line.
        let mut ordered_rendered_spans = rendered_spans.to_vec();
        ordered_rendered_spans.sort_by(|(left_id, left_span), (right_id, right_span)| {
            let left_lineage_len = source_map
                .final_pseudo_to_mid
                .get(left_id)
                .map(|mids| mids.len())
                .unwrap_or(0);
            let right_lineage_len = source_map
                .final_pseudo_to_mid
                .get(right_id)
                .map(|mids| mids.len())
                .unwrap_or(0);
            left_lineage_len
                .cmp(&right_lineage_len)
                .then_with(|| {
                    span_specificity_key(*left_span).cmp(&span_specificity_key(*right_span))
                })
                .then_with(|| left_id.cmp(right_id))
        });
        ordered_rendered_spans.dedup();

        let mut exact_mid_spans = std::collections::HashMap::<MidExprId, SourceSpan>::new();
        for (pseudo_node_id, span) in ordered_rendered_spans {
            let Some(mid_ids) = source_map.final_pseudo_to_mid.get(&pseudo_node_id) else {
                continue;
            };
            for mid_id in mid_ids {
                exact_mid_spans.entry(*mid_id).or_insert(span);
            }
        }

        if !exact_mid_spans.is_empty() {
            source_map.mid_to_source.clear();
            source_map.uplc_to_source.clear();
            source_map.line_to_uplc.clear();

            for mid_id in source_map.mid_order.clone() {
                if let Some(span) = exact_mid_spans.get(&mid_id).copied() {
                    source_map.set_mid_span(mid_id, span);
                }
            }
            return true;
        }
    }

    let mid_ids = source_map.mid_order.clone();
    if mid_ids.is_empty() {
        return false;
    }

    let mut ordered_spans: Vec<SourceSpan> = rendered_spans.iter().map(|(_, span)| *span).collect();
    ordered_spans.sort_by(|a, b| {
        a.start_line
            .cmp(&b.start_line)
            .then_with(|| a.start_col.cmp(&b.start_col))
            .then_with(|| a.end_line.cmp(&b.end_line))
            .then_with(|| a.end_col.cmp(&b.end_col))
    });
    ordered_spans.dedup();

    if ordered_spans.is_empty() {
        return false;
    }

    source_map.mid_to_source.clear();
    source_map.uplc_to_source.clear();
    source_map.line_to_uplc.clear();

    let span_count = ordered_spans.len();
    for (i, mid_id) in mid_ids.iter().enumerate() {
        let span_idx = (i * span_count / mid_ids.len()).min(span_count - 1);
        source_map.set_mid_span(*mid_id, ordered_spans[span_idx]);
    }

    true
}

/// Finalize rendered source spans without densifying direct UPLC coverage.
///
/// Diagnostics and tests use it to measure whether any original UPLC ids
/// still depend on late saturation.
pub(crate) fn finalize_source_map_exact_from_rendered_spans(
    rendered_spans: &[(
        crate::pseudo::ast::PseudoNodeId,
        crate::pseudo::mid::expr_id::SourceSpan,
    )],
    source_map: &mut SourceMap,
) -> bool {
    finalize_source_map_from_rendered_spans(rendered_spans, source_map)
}

/// Finalize rendered source spans and densify direct UPLC coverage for the
/// original concrete program tree.
pub(crate) fn finalize_source_map_for_program_from_rendered_spans(
    rendered_spans: &[(
        crate::pseudo::ast::PseudoNodeId,
        crate::pseudo::mid::expr_id::SourceSpan,
    )],
    source_map: &mut SourceMap,
    term: &uplc::ast::Term<uplc::ast::NamedDeBruijn>,
) -> bool {
    let finalized = finalize_source_map_exact_from_rendered_spans(rendered_spans, source_map);
    if finalized {
        // Claiming hands a mid the tightest *rendered node* that carries it,
        // which for a collapsed mid is a whole block, so every term the mid
        // owns reports that block's header. Narrowing before saturation both
        // fixes those positions and gives saturation better seeds. Going
        // through the one shared sequence keeps this path from drifting from
        // the stepper's.
        source_map.resolve_spans_for_stepping(term, true);
    }
    finalized
}

pub(crate) fn span_specificity_key(
    span: crate::pseudo::mid::expr_id::SourceSpan,
) -> (u32, u32, u32, u32, u32, u32) {
    (
        span.end_line.saturating_sub(span.start_line),
        if span.start_line == span.end_line {
            span.end_col.saturating_sub(span.start_col)
        } else {
            span.end_col
        },
        span.start_line,
        span.start_col,
        span.end_line,
        span.end_col,
    )
}

/// Build source spans by matching significant code lines to UPLC IDs.
///
/// Fallback for callers without rendered pseudo-node spans: distributes
/// MidExprIds in order over the lines that look like code.
fn finalize_source_map(source_code: &str, source_map: &mut SourceMap) {
    use crate::pseudo::mid::expr_id::SourceSpan;

    let lines: Vec<&str> = source_code.lines().collect();
    if lines.is_empty() {
        return;
    }

    let significant_lines: Vec<u32> = lines
        .iter()
        .enumerate()
        .filter(|(_, line)| {
            let trimmed = line.trim();
            !trimmed.is_empty()
                && (trimmed.starts_with("let ")
                    || trimmed.starts_with("expect!") // internal marker, not surface
                    || trimmed.starts_with("expect ") // surface keyword
                    || trimmed.starts_with("fn(")
                    || trimmed.starts_with("fn ")
                    || trimmed.starts_with("rec fn")
                    || trimmed.starts_with("if ")
                    || trimmed.starts_with("when ")
                    || trimmed.starts_with("trace")
                    || trimmed.contains("==")
                    || trimmed.contains("&&")
                    || trimmed.contains("||")
                    || trimmed.contains('(')
                    || trimmed.starts_with('}')
                    || (!trimmed.starts_with("//") && trimmed.len() > 2))
        })
        .map(|(i, _)| i as u32)
        .collect();

    let mid_ids = source_map.mid_order.clone();
    if mid_ids.is_empty() {
        return;
    }

    source_map.mid_to_source.clear();
    source_map.uplc_to_source.clear();
    source_map.line_to_uplc.clear();

    // Map MidExprIds to significant lines, distributing proportionally
    // when there are more mids than significant lines.
    let sig_count = significant_lines.len();
    for (i, mid_id) in mid_ids.iter().enumerate() {
        let sig_idx = if sig_count > 0 {
            (i * sig_count / mid_ids.len()).min(sig_count - 1)
        } else {
            0
        };
        let line_0based = significant_lines.get(sig_idx).copied().unwrap_or(0);
        let span = SourceSpan {
            start_line: line_0based + 1, // 1-based
            start_col: 1,
            end_line: line_0based + 1,
            end_col: lines
                .get(line_0based as usize)
                .map(|l| l.len() as u32)
                .unwrap_or(1),
        };
        source_map.set_mid_span(*mid_id, span);
    }
}

/// Finalize fallback line-based source spans, WITHOUT densifying UPLC coverage.
///
/// Saturation stays the caller's call: bundling the two hides the boundary
/// between spans this finalizer assigned and spans saturation guessed, and
/// the stepping bridge has to tell those apart. A caller that wants both
/// runs [`SourceMap::saturate_uplc_term_spans`] itself, capturing whatever
/// it needs in between.
pub(crate) fn finalize_source_map_fallback_lines(source_code: &str, source_map: &mut SourceMap) {
    finalize_source_map(source_code, source_map);
}

#[cfg(test)]
mod tests;
