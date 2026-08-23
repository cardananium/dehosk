use std::collections::HashMap;
use std::rc::Rc;

use crate::pseudo::ast::PseudoType;
use crate::pseudo::var_id::VarId;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(super) struct TypeVarId(u32);

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(super) enum BindingKey {
    VarId(VarId),
    FreeName(String),
}

/// A type expression: either an unresolved variable or a concrete PseudoType.
#[derive(Clone, Debug)]
pub(super) enum TypeExpr {
    Var(TypeVarId),
    Known(Rc<PseudoType>),
}

/// A single unification constraint: `left` should unify with `right`.
struct Constraint {
    left: TypeVarId,
    right: TypeExpr,
}

/// The constraint solver state.
pub(super) struct TypeSolver {
    next_id: u32,
    /// Union-find parent map: each var either points to another TypeExpr
    /// or is its own root (absent from the map).
    parent: HashMap<TypeVarId, TypeExpr>,
    constraints: Vec<Constraint>,
    /// Map from binding identity to its type variable.
    pub(super) var_map: HashMap<BindingKey, TypeVarId>,
}

#[derive(Default, Clone)]
pub(super) struct LexicalEnv {
    bindings: Vec<(String, BindingKey)>,
}

impl LexicalEnv {
    pub(super) fn push(&mut self, name: String, key: BindingKey) {
        self.bindings.push((name, key));
    }

    pub(super) fn pop(&mut self) {
        self.bindings.pop();
    }

    pub(super) fn resolve(&self, name: &str) -> Option<BindingKey> {
        self.bindings
            .iter()
            .rev()
            .find_map(|(binding_name, key)| (binding_name == name).then_some(key.clone()))
    }
}

impl TypeSolver {
    pub(super) fn new() -> Self {
        Self {
            next_id: 0,
            parent: HashMap::new(),
            constraints: Vec::new(),
            var_map: HashMap::new(),
        }
    }

    /// Allocate a fresh type variable.
    pub(super) fn fresh(&mut self) -> TypeVarId {
        let id = TypeVarId(self.next_id);
        self.next_id += 1;
        id
    }

    /// Get or create the type variable for a binding identity.
    pub(super) fn var_for_binding_key(&mut self, key: BindingKey) -> TypeVarId {
        if let Some(&id) = self.var_map.get(&key) {
            id
        } else {
            let id = self.fresh();
            self.var_map.insert(key, id);
            id
        }
    }

    pub(super) fn var_for_var_id(&mut self, id: VarId) -> TypeVarId {
        self.var_for_binding_key(BindingKey::VarId(id))
    }

    pub(super) fn var_for_free_name(&mut self, name: &str) -> TypeVarId {
        self.var_for_binding_key(BindingKey::FreeName(name.to_string()))
    }

    pub(super) fn resolve_binding_in_env(
        &mut self,
        name: &str,
        id: Option<VarId>,
        env: &LexicalEnv,
    ) -> TypeVarId {
        if let Some(id) = id {
            return self.var_for_var_id(id);
        }

        if let Some(binding_key) = env.resolve(name) {
            return self.var_for_binding_key(binding_key);
        }

        self.var_for_free_name(name)
    }

    /// Add a constraint: `var = expr`.
    pub(super) fn constrain(&mut self, var: TypeVarId, expr: TypeExpr) {
        self.constraints.push(Constraint {
            left: var,
            right: expr,
        });
    }

    /// Constrain a var to a concrete PseudoType.
    pub(super) fn constrain_known(&mut self, var: TypeVarId, ty: PseudoType) {
        self.constrain(var, TypeExpr::Known(Rc::new(ty)));
    }

    /// Constrain two vars to be equal.
    pub(super) fn constrain_eq(&mut self, a: TypeVarId, b: TypeVarId) {
        self.constrain(a, TypeExpr::Var(b));
    }

    /// Find the representative for a type variable.
    pub(super) fn find(&self, id: TypeVarId) -> TypeExpr {
        match self.parent.get(&id) {
            None => TypeExpr::Var(id),
            Some(TypeExpr::Var(parent)) if *parent == id => TypeExpr::Var(id),
            Some(TypeExpr::Var(parent)) => self.find(*parent),
            Some(TypeExpr::Known(t)) => TypeExpr::Known(t.clone()),
        }
    }

    /// Process all constraints via unification.
    pub(super) fn solve(&mut self) {
        let constraints = std::mem::take(&mut self.constraints);
        for c in constraints {
            self.unify(c.left, c.right);
        }
    }

    /// Resolved concrete type for a final-AST `VarId`.
    ///
    /// `None` when no type variable was allocated for this id, or when
    /// the solver never committed it to a concrete `PseudoType`.
    pub(super) fn solved_type_of_var(&self, id: VarId) -> Option<Rc<PseudoType>> {
        let tv = *self.var_map.get(&BindingKey::VarId(id))?;
        match self.find(tv) {
            TypeExpr::Known(t) => Some(t),
            TypeExpr::Var(_) => None,
        }
    }

    /// Unify a variable with a type expression.
    fn unify(&mut self, a: TypeVarId, b: TypeExpr) {
        let a_resolved = self.find(a);
        match (&a_resolved, &b) {
            // Both vars: point one to the other.
            (TypeExpr::Var(v1), TypeExpr::Var(v2)) => {
                let v2_resolved = self.find(*v2);
                match v2_resolved {
                    TypeExpr::Var(v2r) => {
                        if *v1 != v2r {
                            self.parent.insert(*v1, TypeExpr::Var(v2r));
                        }
                    }
                    TypeExpr::Known(t) => {
                        self.parent.insert(*v1, TypeExpr::Known(t));
                    }
                }
            }
            // a is a var, b is known: bind a to the known type.
            (TypeExpr::Var(v), TypeExpr::Known(t)) => {
                self.parent.insert(*v, TypeExpr::Known(t.clone()));
            }
            // a is known, b is a var: bind b to the known type.
            (TypeExpr::Known(t), TypeExpr::Var(v)) => {
                let v_resolved = self.find(*v);
                if let TypeExpr::Var(vr) = v_resolved {
                    self.parent.insert(vr, TypeExpr::Known(t.clone()));
                } else if let TypeExpr::Known(t2) = v_resolved {
                    // Both sides resolved to known types — try structural unification.
                    if let Some(merged) = self.unify_pseudo_types(t, &t2) {
                        // Update a's root to the more specific merged type.
                        self.parent.insert(a, TypeExpr::Known(Rc::new(merged)));
                    }
                }
            }
            // Both known: try structural unification.
            (TypeExpr::Known(t1), TypeExpr::Known(t2)) => {
                if let Some(merged) = self.unify_pseudo_types(t1, t2) {
                    // Store merged result on a's root.
                    self.parent.insert(a, TypeExpr::Known(Rc::new(merged)));
                }
            }
        }
    }

    /// Structurally unify two PseudoTypes. Returns a merged type if possible.
    /// Unknown unifies with anything (taking the other side).
    fn unify_pseudo_types(&self, t1: &PseudoType, t2: &PseudoType) -> Option<PseudoType> {
        match (t1, t2) {
            // Unknown absorbs anything.
            (PseudoType::Unknown, other) | (other, PseudoType::Unknown) => Some(other.clone()),
            // Var absorbs anything concrete.
            (PseudoType::Var(_), other) | (other, PseudoType::Var(_)) => Some(other.clone()),

            // Recursive structural cases.
            (PseudoType::Option(a), PseudoType::Option(b)) => {
                let inner = self.unify_pseudo_types(a, b)?;
                Some(PseudoType::Option(Rc::new(inner)))
            }
            (PseudoType::Result(a1, b1), PseudoType::Result(a2, b2)) => {
                let ok = self.unify_pseudo_types(a1, a2)?;
                let err = self.unify_pseudo_types(b1, b2)?;
                Some(PseudoType::Result(Rc::new(ok), Rc::new(err)))
            }
            (PseudoType::List(a), PseudoType::List(b)) => {
                let inner = self.unify_pseudo_types(a, b)?;
                Some(PseudoType::List(Rc::new(inner)))
            }
            (PseudoType::Pair(a1, b1), PseudoType::Pair(a2, b2)) => {
                let fst = self.unify_pseudo_types(a1, a2)?;
                let snd = self.unify_pseudo_types(b1, b2)?;
                Some(PseudoType::Pair(Rc::new(fst), Rc::new(snd)))
            }
            // Function unification: arity must match;
            // params and ret unify recursively.
            (
                PseudoType::Function {
                    params: p1,
                    ret: r1,
                },
                PseudoType::Function {
                    params: p2,
                    ret: r2,
                },
            ) => {
                if p1.len() != p2.len() {
                    return None;
                }
                let mut merged_params = Vec::with_capacity(p1.len());
                for (a, b) in p1.iter().zip(p2.iter()) {
                    merged_params.push(Rc::new(self.unify_pseudo_types(a, b)?));
                }
                let merged_ret = Rc::new(self.unify_pseudo_types(r1, r2)?);
                Some(PseudoType::Function {
                    params: merged_params,
                    ret: merged_ret,
                })
            }

            // Same concrete type — identity.
            (a, b) if a == b => Some(a.clone()),

            // Constructor/data evidence should beat stale scalar guesses.
            _ => self.prefer_conflict_resolution(t1, t2),
        }
    }

    fn prefer_conflict_resolution(&self, t1: &PseudoType, t2: &PseudoType) -> Option<PseudoType> {
        // Function is a weak hint emitted for every Lambda/RecFn
        // value, so concrete structural evidence beats it — a
        // Pair-pattern on a let-binder whose value was a Lambda
        // that reduces to a Pair keeps the Pair. Otherwise the
        // type-invariant check rejects the mixed `Function ⊓ Pair`
        // constraints that inlining-collapsed binders produce.
        if matches!(t1, PseudoType::Function { .. })
            && !matches!(t2, PseudoType::Function { .. } | PseudoType::Unknown)
        {
            return Some(t2.clone());
        }
        if matches!(t2, PseudoType::Function { .. })
            && !matches!(t1, PseudoType::Function { .. } | PseudoType::Unknown)
        {
            return Some(t1.clone());
        }

        if Self::is_constructor_carrier_type(t1) && Self::is_weak_scalar_type(t2) {
            return Some(t1.clone());
        }

        if Self::is_constructor_carrier_type(t2) && Self::is_weak_scalar_type(t1) {
            return Some(t2.clone());
        }

        if matches!(t1, PseudoType::Data) && Self::is_sum_or_named_data_shape(t2) {
            return Some(t2.clone());
        }

        if matches!(t2, PseudoType::Data) && Self::is_sum_or_named_data_shape(t1) {
            return Some(t1.clone());
        }

        if matches!(t1, PseudoType::Data) && Self::is_raw_collection_type(t2) {
            return Some(PseudoType::Data);
        }

        if matches!(t2, PseudoType::Data) && Self::is_raw_collection_type(t1) {
            return Some(PseudoType::Data);
        }

        None
    }

    fn is_weak_scalar_type(ty: &PseudoType) -> bool {
        matches!(
            ty,
            PseudoType::Int
                | PseudoType::ByteArray
                | PseudoType::String
                | PseudoType::Bool
                | PseudoType::Unit
        )
    }

    fn is_specific_data_shape(ty: &PseudoType) -> bool {
        matches!(
            ty,
            PseudoType::List(_)
                | PseudoType::Tuple(_)
                | PseudoType::Pair(_, _)
                | PseudoType::Option(_)
                | PseudoType::Result(_, _)
                | PseudoType::Named(_)
        )
    }

    fn is_raw_collection_type(ty: &PseudoType) -> bool {
        matches!(
            ty,
            PseudoType::List(_) | PseudoType::Tuple(_) | PseudoType::Pair(_, _)
        )
    }

    fn is_sum_or_named_data_shape(ty: &PseudoType) -> bool {
        matches!(
            ty,
            PseudoType::Option(_) | PseudoType::Result(_, _) | PseudoType::Named(_)
        )
    }

    fn is_constructor_carrier_type(ty: &PseudoType) -> bool {
        matches!(ty, PseudoType::Data) || Self::is_specific_data_shape(ty)
    }
}
