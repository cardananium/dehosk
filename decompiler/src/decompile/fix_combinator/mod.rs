use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

mod pair_fix;
pub(crate) use pair_fix::recover_pair_fixpoint;

/// ```text
/// // Before:
/// rec fn self_fn_11(acc_11) {
///   rec fn self_fn_12(acc_12) { acc_11(rec_fn_5, acc_12) }
/// }
/// // After:
/// rec fn self_fn_11(acc_11) {
///   fn(acc_12) { acc_11(rec_fn_5, acc_12) }
/// }
/// ```
pub(crate) fn simplify_double_rec_fn(expr: PseudoExpr) -> PseudoExpr {
    struct DoubleRecSimplifier;

    impl ExprFolder for DoubleRecSimplifier {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_recfn(
            &mut self,
            name: Binder,
            params: Vec<Binder>,
            body: PseudoExpr,
        ) -> PseudoExpr {
            if let PseudoExpr::RecFn {
                name: ref inner_name,
                params: ref inner_params,
                body: ref inner_body,
            } = body
                && !crate::decompile::simplify::Simplifier::is_var_used_by_id(
                    inner_body,
                    inner_name.as_str(),
                    Some(inner_name.var_id()),
                )
            {
                return PseudoExpr::RecFn {
                    name,
                    params,
                    body: PBox::new(PseudoExpr::Lambda {
                        params: inner_params.clone(),
                        body: inner_body.clone(),
                    }),
                };
            }
            PseudoExpr::RecFn {
                name,
                params,
                body: PBox::new(body),
            }
        }
    }

    DoubleRecSimplifier.fold(expr)
}

/// The Z-combinator (strict Y-combinator) step pattern becomes
/// `fix(captured_fn)`:
///
/// ```text
/// // Before:
/// rec fn self_fn_33(acc_33) { fn(acc_34) { acc_33(rec_fn_16, acc_34) } }
/// // After:
/// fix(rec_fn_16)
/// ```
///
/// The Y-combinator definition itself becomes `fix`:
///
/// ```text
/// // Before:
/// rec fn a(acc) { rec fn self_fn_2(acc_2) { acc(self_fn_2, acc_2) } }
/// // After:
/// fix
/// ```
pub(crate) fn simplify_z_combinator(expr: PseudoExpr) -> PseudoExpr {
    struct ZCombinatorSimplifier;

    fn is_fix_step_lambda(expr: &PseudoExpr, self_id: VarId) -> bool {
        match expr {
            PseudoExpr::Lambda { params, body } if params.len() == 1 => {
                if let PseudoExpr::Apply {
                    function: ref func,
                    args: ref apply_args,
                } = **body
                {
                    if let PseudoExpr::Var { id: ref fn_id, .. } = **func {
                        if *fn_id == Some(self_id) {
                            match apply_args.as_slice() {
                                [PseudoExpr::Var { id: arg_id, .. }] => {
                                    *arg_id == Some(params[0].var_id())
                                }
                                [
                                    PseudoExpr::Var { id: first_id, .. },
                                    PseudoExpr::Var { id: second_id, .. },
                                ] => {
                                    *first_id == Some(self_id)
                                        && *second_id == Some(params[0].var_id())
                                }
                                _ => false,
                            }
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    impl ExprFolder for ZCombinatorSimplifier {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_recfn(
            &mut self,
            name: Binder,
            params: Vec<Binder>,
            body: PseudoExpr,
        ) -> PseudoExpr {
            if params.len() == 1 {
                // Pattern 1: Z-combinator step
                // rec fn self(acc) { fn(next) { acc(captured, next) } }
                // → fix(captured)
                if let PseudoExpr::Lambda {
                    params: ref inner_params,
                    body: ref inner_body,
                } = body
                    && inner_params.len() == 1
                    && let PseudoExpr::Apply {
                        function: ref func,
                        args: ref apply_args,
                    } = **inner_body
                    && let PseudoExpr::Var { id: ref fn_id, .. } = **func
                    && *fn_id == Some(params[0].var_id())
                    && apply_args.len() == 2
                    && let PseudoExpr::Var {
                        name: ref captured,
                        id: ref captured_id,
                        ..
                    } = apply_args[0]
                    && let PseudoExpr::Var {
                        id: ref next_id, ..
                    } = apply_args[1]
                    && *next_id == Some(inner_params[0].var_id())
                {
                    let captured_concrete = captured_id
                        .get()
                        .unwrap_or_else(VarId::fresh_compat_placeholder);
                    return PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::fix_helper()),
                        args: vec![PseudoExpr::var_with_id(captured.clone(), captured_concrete)]
                            .into(),
                    };
                }

                // Pattern 2: Y-combinator definition itself
                // rec fn a(acc) { rec fn inner(x) { acc(inner, x) } }
                // → fix (the fix-point combinator itself)
                if let PseudoExpr::RecFn {
                    name: ref inner_name,
                    params: ref inner_params,
                    body: ref inner_body,
                } = body
                    && inner_params.len() == 1
                    && let PseudoExpr::Apply {
                        function: ref func,
                        args: ref apply_args,
                    } = **inner_body
                    && let PseudoExpr::Var { id: ref fn_id, .. } = **func
                    && *fn_id == Some(params[0].var_id())
                    && apply_args.len() == 2
                    && let PseudoExpr::Var {
                        id: ref self_ref_id,
                        ..
                    } = apply_args[0]
                    && let PseudoExpr::Var { id: ref arg_id, .. } = apply_args[1]
                    && *self_ref_id == Some(inner_name.var_id())
                    && *arg_id == Some(inner_params[0].var_id())
                {
                    return PseudoExpr::fix_helper();
                }

                // Pattern 3: Let-wrapped fix definition with eta/self-application step
                // rec fn a(acc) {
                //   let inner = acc(inner) in
                //   rec fn inner(x) { acc(fn(v) { x(x, v) }) }
                // }
                // → fix
                if let PseudoExpr::Let {
                    id: ref let_id,
                    value: ref let_value,
                    body: ref let_body,
                    ..
                } = body
                    && let PseudoExpr::RecFn {
                        name: ref inner_name,
                        params: ref inner_params,
                        body: ref inner_body,
                    } = **let_body
                    && *let_id == Some(inner_name.var_id())
                    && inner_params.len() == 1
                    && let PseudoExpr::Apply {
                        function: ref outer_func,
                        args: ref outer_args,
                    } = **let_value
                    && let PseudoExpr::Var {
                        id: ref outer_id, ..
                    } = **outer_func
                    && *outer_id == Some(params[0].var_id())
                    && outer_args.len() == 1
                    && let PseudoExpr::Var {
                        id: ref outer_arg_id,
                        ..
                    } = outer_args[0]
                    && *outer_arg_id == Some(inner_name.var_id())
                    && let PseudoExpr::Apply {
                        function: ref inner_func,
                        args: ref inner_args,
                    } = **inner_body
                    && let PseudoExpr::Var {
                        id: ref inner_acc_id,
                        ..
                    } = **inner_func
                    && *inner_acc_id == Some(params[0].var_id())
                    && inner_args.len() == 1
                    && is_fix_step_lambda(&inner_args[0], inner_params[0].var_id())
                {
                    return PseudoExpr::fix_helper();
                }

                // Pattern 4: Let-bound recursive step followed by acc(inner)
                // rec fn a(acc) {
                //   let inner = rec fn inner(x) { acc(fn(v) { x(x, v) }) } in
                //   acc(inner)
                // }
                // → fix
                if let PseudoExpr::Let {
                    id: ref let_id,
                    value: ref let_value,
                    body: ref let_body,
                    ..
                } = body
                    && let PseudoExpr::RecFn {
                        name: ref inner_name,
                        params: ref inner_params,
                        body: ref inner_body,
                    } = **let_value
                    && *let_id == Some(inner_name.var_id())
                    && inner_params.len() == 1
                    && let PseudoExpr::Apply {
                        function: ref outer_func,
                        args: ref outer_args,
                    } = **let_body
                    && let PseudoExpr::Var {
                        id: ref outer_id, ..
                    } = **outer_func
                    && *outer_id == Some(params[0].var_id())
                    && outer_args.len() == 1
                    && let PseudoExpr::Var {
                        id: ref outer_arg_id,
                        ..
                    } = outer_args[0]
                    && *outer_arg_id == Some(inner_name.var_id())
                    && let PseudoExpr::Apply {
                        function: ref inner_func,
                        args: ref inner_args,
                    } = **inner_body
                    && let PseudoExpr::Var {
                        id: ref inner_acc_id,
                        ..
                    } = **inner_func
                    && *inner_acc_id == Some(params[0].var_id())
                    && inner_args.len() == 1
                    && is_fix_step_lambda(&inner_args[0], inner_params[0].var_id())
                {
                    return PseudoExpr::fix_helper();
                }
            }

            // Not a Z/Y-combinator, keep as-is
            PseudoExpr::RecFn {
                name,
                params,
                body: PBox::new(body),
            }
        }
    }

    ZCombinatorSimplifier.fold(expr)
}

#[cfg(test)]
mod tests;
