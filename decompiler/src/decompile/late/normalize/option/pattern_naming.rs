use crate::decompile::blueprint_registry::{OPTION_TYPE_HINT_NAME, TypeHintId};
use crate::pseudo::ast::{WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};

pub(in crate::decompile::late::normalize) fn rename_option_pattern(
    pattern: WhenPattern,
) -> WhenPattern {
    match pattern {
        WhenPattern::Constructor {
            tag: 0,
            fields,
            shape: ConstructorShape::Unknown { .. },
            type_hint: None,
            ..
        } if fields.len() == 1 => WhenPattern::constructor_known(KnownConstructor::Some, fields),
        WhenPattern::Constructor {
            tag: 0,
            fields,
            shape: ConstructorShape::Unknown { .. },
            type_hint: None,
        } if fields.is_empty() => {
            let shape = ConstructorShape::from_name_and_tag(None, 0, fields.len());
            WhenPattern::Constructor {
                type_hint: Some(TypeHintId::new(OPTION_TYPE_HINT_NAME)),
                tag: 0,
                fields,
                shape,
            }
        }
        WhenPattern::Constructor {
            tag: 1,
            fields,
            shape: ConstructorShape::Unknown { .. },
            type_hint: None,
        } if fields.is_empty() => WhenPattern::constructor_known(KnownConstructor::None, fields),
        other => other,
    }
}

pub(in crate::decompile::late::normalize) fn fill_option_wildcard_pattern(
    clauses: &mut [WhenClause],
) {
    let has_some = clauses.iter().any(|clause| {
        matches!(
            &clause.pattern,
            WhenPattern::Constructor {
                type_hint,
                tag: 0,
                shape,
                ..
            } if matches!(shape, ConstructorShape::Known(KnownConstructor::Some))
                || type_hint.as_ref().map(TypeHintId::as_str) == Some(OPTION_TYPE_HINT_NAME)
        )
    });
    let has_none = clauses.iter().any(|clause| {
        matches!(
            &clause.pattern,
            WhenPattern::Constructor {
                tag: 1,
                fields,
                shape,
                ..
            } if matches!(shape, ConstructorShape::Known(KnownConstructor::None))
                && fields.is_empty()
        )
    });

    if has_some && !has_none {
        for clause in clauses.iter_mut() {
            if clause.guard.is_none() && matches!(clause.pattern, WhenPattern::Wildcard) {
                clause.pattern = WhenPattern::constructor_known(KnownConstructor::None, vec![]);
            }
        }
    }

    if has_none && !has_some {
        for clause in clauses.iter_mut() {
            if clause.guard.is_none() && matches!(clause.pattern, WhenPattern::Wildcard) {
                let shape = ConstructorShape::from_name_and_tag(None, 0, 0);
                clause.pattern = WhenPattern::Constructor {
                    type_hint: Some(TypeHintId::new(OPTION_TYPE_HINT_NAME)),
                    tag: 0,
                    fields: vec![],
                    shape,
                };
            }
        }
    }
}
