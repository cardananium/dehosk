//! Rendering a `WhenPattern` to text through the constructor-name
//! registry.
//!
//! This used to be `WhenPattern::to_string_with_registry`, an inherent
//! method on the AST node — which meant `pseudo::ast` had to import
//! `BlueprintHintRegistry` from the layer above it. The registry is a
//! RENDER concern (it is seeded from the Cardano schema and the
//! project's `plutus.json`), so the function lives here and the AST's
//! own `Display` stays registry-free.

use crate::decompile::BlueprintHintRegistry;
use crate::pseudo::ast::WhenPattern;

/// Format `pattern`, consulting `registry` for constructor display
/// names. An `Unknown` shape with no registered user entry renders as
/// `Constr<tag>`.
pub(crate) fn pattern_to_string(pattern: &WhenPattern, registry: &BlueprintHintRegistry) -> String {
    match pattern {
        WhenPattern::Constructor {
            type_hint,
            tag,
            fields,
            shape,
            ..
        } => {
            let n = registry
                .resolve(*shape, type_hint.as_ref())
                .map(|s| s.to_string())
                .unwrap_or_else(|| format!("Constr{}", tag));
            if fields.is_empty() {
                n
            } else {
                format!(
                    "{}({})",
                    n,
                    fields
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
        WhenPattern::List { elements, tail } => {
            let mut parts: Vec<String> = elements.iter().map(ToString::to_string).collect();
            if let Some(t) = tail {
                parts.push(format!("..{}", t));
            }
            format!("[{}]", parts.join(", "))
        }
        WhenPattern::Tuple(fields) => format!(
            "({})",
            fields
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        WhenPattern::Pair(a, b) => format!("Pair({}, {})", a, b),
        WhenPattern::Wildcard => "_".to_string(),
        WhenPattern::Var(name) => name.to_string(),
        WhenPattern::Literal(expr) => format!("{:?}", expr),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pseudo::ast::Binder;
    use crate::pseudo::constructor::ConstructorShape;
    use crate::pseudo::type_hint::TypeHintId;

    #[test]
    fn test_when_pattern_to_string_resolves_user_name_via_registry() {
        // Unknown shape: rendering resolves the user-ADT constructor name
        // from `BlueprintHintRegistry` via the pattern's `TypeHintId`.
        let hint = TypeHintId::new("MyList");
        let pat = WhenPattern::constructor_with_hint(
            ConstructorShape::unknown_data(0, 2),
            vec![Binder::from("h".to_string()), Binder::from("t".to_string())],
            Some(hint.clone()),
        );
        let mut registry = BlueprintHintRegistry::new();
        registry.register_user(hint, 0, "Cons");
        assert_eq!(pattern_to_string(&pat, &registry), "Cons(h, t)");
    }
}
