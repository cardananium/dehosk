use crate::decompile::simplify::Simplifier;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};

impl Simplifier {
    /// Simple values need no delay wrapper: booleans, `Void`, integers,
    /// `fail`, the empty list, and the nullary constructors `True`,
    /// `False`, `None` and tag-0 stubs.
    pub(crate) fn is_simple_value(expr: &PseudoExpr) -> bool {
        match expr {
            PseudoExpr::Bool(_) => true,
            PseudoExpr::Unit => true,
            PseudoExpr::Int(_) => true,
            PseudoExpr::Error { .. } => true,
            PseudoExpr::BuiltinCall { name, args }
                if args.is_empty() && (*name == crate::BuiltinId::Error) =>
            {
                true
            }
            PseudoExpr::List { elements, tail } if elements.is_empty() && tail.is_none() => true,
            PseudoExpr::Constr { shape, fields, .. }
                if fields.is_empty()
                    && matches!(
                        shape,
                        ConstructorShape::Known(KnownConstructor::True)
                            | ConstructorShape::Known(KnownConstructor::False)
                            | ConstructorShape::Known(KnownConstructor::None)
                            | ConstructorShape::Unknown {
                                tag: 0,
                                arity: 0,
                                ..
                            }
                    ) =>
            {
                true
            }
            _ => false,
        }
    }

    /// Values that are already in normal/value form for pseudo output and
    /// therefore do not need an explicit `force(...)` wrapper.
    pub(crate) fn is_non_thunk_value(expr: &PseudoExpr) -> bool {
        if Self::is_simple_value(expr) {
            return true;
        }

        match expr {
            // Structural values
            PseudoExpr::Constr { .. }
            | PseudoExpr::List { .. }
            | PseudoExpr::Pair(..)
            | PseudoExpr::Tuple(_)
            | PseudoExpr::FieldAccess { .. }
            | PseudoExpr::IndexAccess { .. } => true,

            // Fully-applied builtin calls represent computed values in pseudo AST.
            PseudoExpr::BuiltinCall { args, .. } if !args.is_empty() => true,

            _ => false,
        }
    }
}
