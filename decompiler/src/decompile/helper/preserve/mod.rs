//! Identify signature-bearing Let-bound helpers and return a set of
//! `VarId`s that downstream passes should refuse to inline.
//!
//! The compiler lifts user-declared helpers like
//! `fn is_small(n: Int) -> Bool { n < 10 }` into `let`-bound
//! lambdas at the validator's entry, and MIR lower registers an
//! `FnSignature` for those bindings in `TypeEnvironment`. Without
//! that set, the post-MIR inliner substitutes the lambda body at
//! every call site, rendering
//! `int < 10 && int == 7` instead of `is_small(int) && int == 7`.
//!
//! A helper the compile-time optimiser already inlined before
//! producing UPLC has no recorded signature, so nothing here can
//! recover it.

use std::collections::HashSet;

use crate::decompile::mid::type_env::{FnSignature, TypeEnvironment};
use crate::pseudo::ast::{PseudoExpr, PseudoType};
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

/// Walk `expr` and return the set of Let-binding `VarId`s whose value
/// is a `Lambda`/`RecFn` and whose MIR-registered signature is present
/// in `type_env` **and** fully concrete (no `Unknown` or type variables
/// anywhere in param/return types). These are the user-declared helpers
/// that the rest of the pipeline must keep as-is instead of inlining.
///
/// # Why require a fully concrete signature?
///
/// MIR lower registers an `FnSignature` for every Let-bound closure
/// whose body has a recorded type, including the closures the compiler
/// synthesizes for CPS transforms, Scott-encoded case clauses and
/// curry/eta lifts. Those typically carry at least one `Unknown` or
/// `Var(_)` in their parameter or return types, because the MIR type
/// inferencer cannot pin down their usage-polymorphic shape, whereas a
/// user-declared helper is concrete end to end from its source
/// annotation.
pub(crate) fn preserved_helper_ids(
    expr: &PseudoExpr,
    type_env: &TypeEnvironment,
) -> HashSet<VarId> {
    let mut collector = Collector {
        type_env,
        preserved: HashSet::new(),
    };
    collector.walk(expr);
    collector.preserved
}

struct Collector<'a> {
    type_env: &'a TypeEnvironment,
    preserved: HashSet<VarId>,
}

impl<'a> ExprVisitor for Collector<'a> {
    fn visit_let(
        &mut self,
        _name: &str,
        id: &Option<VarId>,
        value: &PseudoExpr,
        _body: &PseudoExpr,
    ) {
        if !matches!(value, PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. }) {
            return;
        }
        let Some(vid) = id.get() else {
            return;
        };
        if let Some(sig) = self.type_env.signature_of(vid)
            && signature_is_fully_concrete(sig)
        {
            self.preserved.insert(vid);
        }
    }
}

/// True iff every parameter type and the return type of `sig` is
/// fully concrete — no `PseudoType::Unknown` or `PseudoType::Var(_)`
/// anywhere in the tree.
fn signature_is_fully_concrete(sig: &FnSignature) -> bool {
    sig.params
        .iter()
        .all(|(_, ty)| pseudo_type_is_concrete(ty.as_ref()))
        && pseudo_type_is_concrete(sig.return_type.as_ref())
}

fn pseudo_type_is_concrete(ty: &PseudoType) -> bool {
    match ty {
        PseudoType::Int
        | PseudoType::ByteArray
        | PseudoType::String
        | PseudoType::Bool
        | PseudoType::Unit
        | PseudoType::Data
        | PseudoType::G1Element
        | PseudoType::G2Element
        | PseudoType::MillerLoopResult
        | PseudoType::Named(_) => true,
        PseudoType::Unknown | PseudoType::Var(_) => false,
        PseudoType::List(inner) | PseudoType::Option(inner) => pseudo_type_is_concrete(inner),
        PseudoType::Tuple(items) => items.iter().all(|t| pseudo_type_is_concrete(t)),
        PseudoType::Pair(a, b) => pseudo_type_is_concrete(a) && pseudo_type_is_concrete(b),
        PseudoType::Result(ok, err) => pseudo_type_is_concrete(ok) && pseudo_type_is_concrete(err),
        PseudoType::Function { params, ret } => {
            params.iter().all(|t| pseudo_type_is_concrete(t)) && pseudo_type_is_concrete(ret)
        }
    }
}

#[cfg(test)]
mod tests;
