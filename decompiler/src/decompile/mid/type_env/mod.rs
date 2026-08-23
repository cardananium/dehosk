//! Side table of inferred types, populated at MIR lowering and
//! read (not mutated) afterwards.
//!
//! Inline `Var { tipo }` makes the printer emit `x: Int` on every
//! reference and forces invalidation when a rewrite touches a
//! subtree. Keyed by `VarId` / `MidExprId` so consumers look up
//! without stale inline state. Some still read `tipo:`.

use std::collections::HashMap;
use std::rc::Rc;

use crate::pseudo::ast::{PseudoExpr, PseudoType, TypeResolution};
use crate::pseudo::mid::expr_id::MidExprId;
use crate::pseudo::var_id::VarId;

/// Signature of a function-typed binding.
///
/// Kept separate from `var_types` so consumers can ask "is this VarId a
/// function?" without pattern-matching on `PseudoType::Function`, and so
/// helper_hoist / inlining get param and return types without re-deriving
/// them each pass.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FnSignature {
    /// Parameter bindings in declaration order.
    pub params: Vec<(VarId, Rc<PseudoType>)>,
    /// Inferred return type.
    pub return_type: Rc<PseudoType>,
    /// True if the function is self-referential (Y-combinator / RecFn).
    pub is_recursive: bool,
}

impl FnSignature {
    pub(crate) fn new(
        params: Vec<(VarId, Rc<PseudoType>)>,
        return_type: Rc<PseudoType>,
        is_recursive: bool,
    ) -> Self {
        Self {
            params,
            return_type,
            is_recursive,
        }
    }

    pub(crate) fn arity(&self) -> usize {
        self.params.len()
    }
}

/// Side table of inferred types for a single decompilation run.
///
/// # Lifecycle
/// - **Construction** — `TypeEnvironment::new()` during MIR lowering.
/// - **Population** — `bind_var`, `bind_expr`, `bind_signature` from
///   lowering passes.
/// - **Freeze** — `freeze()` once at the end of MIR lowering; later
///   mutation panics. The environment is then wrapped in an `Rc` and
///   shared with post-MIR consumers.
/// - **Consumption** — `type_of_var`, `type_of_expr`, `signature_of` by
///   naming, pretty printing, type invariants, etc.
///
/// # ID lifecycle contract
///
/// Env keys (`VarId`, `MidExprId`) must be **canonical** — the IDs assigned
/// at MIR translate time by `VarInterner::intern_fresh` and
/// `ProvenanceBuilder::fresh_id`, stable through MIR translate / analyze /
/// precompute / lower.
///
/// Post-MIR passes may rewrite VarIds (`rewrite_reference_id_opt` in
/// `decompile/types.rs`), and lookups by the *new* ID then miss. Freeze
/// precedes any such rewrite, so the environment holds canonical MIR IDs
/// only; consumers needing env lookups after a rewrite must run **before**
/// it, or map the new ID back through the provenance map.
///
/// # Clone cost
///
/// Cloning the three maps is O(n) — fine for snapshots/debug, bad for hot
/// paths. Post-freeze, prefer sharing an `Rc<TypeEnvironment>`.
///
/// Single-threaded by construction.
#[derive(Debug, Clone, Default)]
pub(crate) struct TypeEnvironment {
    /// Types of variable declarations (Let, Lambda params, RecFn).
    var_types: HashMap<VarId, Rc<PseudoType>>,
    /// Types of specific MIR expression nodes (literals, calls, computed
    /// subexpressions).
    expr_types: HashMap<MidExprId, Rc<PseudoType>>,
    /// Function signatures keyed by the function's binding `VarId`.
    fn_signatures: HashMap<VarId, FnSignature>,
    /// After `freeze()`, every mutating call panics.
    frozen: bool,
}

impl TypeEnvironment {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn is_frozen(&self) -> bool {
        self.frozen
    }

    /// Freeze the environment. Further mutation panics.
    pub(crate) fn freeze(&mut self) {
        self.frozen = true;
    }

    fn assert_mutable(&self, op: &'static str) {
        if self.frozen {
            panic!(
                "TypeEnvironment: attempted `{op}` after freeze(); all type writes must happen during MIR LOWER"
            );
        }
    }

    // Writers ---------------------------------------------------------------

    /// Bind a variable declaration's inferred type. The **last** write for
    /// a `VarId` wins, so unification refinements can narrow a fresh type
    /// variable to a concrete one.
    pub(crate) fn bind_var(&mut self, id: VarId, ty: Rc<PseudoType>) {
        self.assert_mutable("bind_var");
        self.var_types.insert(id, ty);
    }

    /// Bind the inferred type of a specific MIR expression node. Same
    /// last-write-wins semantics as `bind_var`.
    pub(crate) fn bind_expr(&mut self, id: MidExprId, ty: Rc<PseudoType>) {
        self.assert_mutable("bind_expr");
        self.expr_types.insert(id, ty);
    }

    /// Record a function signature for a binding that represents a lambda /
    /// recursive function.
    pub(crate) fn bind_signature(&mut self, id: VarId, signature: FnSignature) {
        self.assert_mutable("bind_signature");
        self.fn_signatures.insert(id, signature);
    }

    // Readers --------------------------------------------------------------

    pub(crate) fn type_of_var(&self, id: VarId) -> Option<Rc<PseudoType>> {
        self.var_types.get(&id).cloned()
    }

    pub(crate) fn type_of_expr(&self, id: MidExprId) -> Option<Rc<PseudoType>> {
        self.expr_types.get(&id).cloned()
    }

    pub(crate) fn signature_of(&self, id: VarId) -> Option<&FnSignature> {
        self.fn_signatures.get(&id)
    }

    pub(crate) fn is_function(&self, id: VarId) -> bool {
        self.fn_signatures.contains_key(&id)
    }

    /// Resolve the effective type for a variable reference, in priority
    /// order:
    ///
    /// 1. `inline` if it is a concrete (non-`Unknown`) type — this
    ///    preserves later refinements (`Data` → `ScriptInfo` etc.)
    ///    written back to the inline field by post-MIR type propagation.
    /// 2. `var_types[id]` from this env when the inline slot is absent or
    ///    `Unknown`.
    /// 3. The inline slot as a last resort (even if `Unknown`).
    ///
    /// Call this rather than reinventing the priority rule.
    pub(crate) fn effective_type_for_var(
        &self,
        id: VarId,
        inline: &crate::pseudo::ast::TypeResolution,
    ) -> crate::pseudo::ast::TypeResolution {
        use crate::pseudo::ast::PseudoType;
        let inline_is_refined = inline
            .as_deref()
            .map(|t| !matches!(t, PseudoType::Unknown))
            .unwrap_or(false);
        if inline_is_refined {
            inline.clone()
        } else if let Some(env_ty) = self.type_of_var(id) {
            crate::pseudo::ast::TypeResolution::known(env_ty)
        } else {
            inline.clone()
        }
    }

    // Bulk iteration (diagnostics) -----------------------------------------

    pub(crate) fn var_type_count(&self) -> usize {
        self.var_types.len()
    }

    pub(crate) fn expr_type_count(&self) -> usize {
        self.expr_types.len()
    }

    pub(crate) fn signature_count(&self) -> usize {
        self.fn_signatures.len()
    }
}

/// Resolve the effective type of any expression, checking `TypeEnvironment`
/// for `Var` and `Let` nodes before falling back to the inline `tipo` field.
///
/// Canonical env-aware replacement for `PseudoExpr::type_resolution()`.
/// When `env` is `None`, the result is identical to `expr.type_resolution()`.
pub(crate) fn resolve_type_with_env(
    expr: &PseudoExpr,
    env: Option<&TypeEnvironment>,
) -> TypeResolution {
    match expr {
        PseudoExpr::Var { id, .. } | PseudoExpr::Let { id, .. } => {
            if let Some(env) = env {
                id.and_then(|vid| env.type_of_var(vid))
                    .map(TypeResolution::known)
                    .unwrap_or_default()
            } else {
                TypeResolution::Unknown
            }
        }
        _ => expr.type_resolution(),
    }
}

#[cfg(test)]
mod tests;
