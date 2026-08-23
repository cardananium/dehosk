use crate::pseudo::ast::{Binder, WhenPattern};

pub(super) fn pattern_has_matching_binder(
    pattern: &WhenPattern,
    mut matches: impl FnMut(&Binder) -> bool,
) -> bool {
    match pattern {
        WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
            fields.iter().any(&mut matches)
        }
        WhenPattern::List { elements, tail } => {
            elements.iter().any(&mut matches) || tail.as_ref().is_some_and(&mut matches)
        }
        WhenPattern::Pair(first, second) => matches(first) || matches(second),
        WhenPattern::Var(binder) => matches(binder),
        WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
    }
}
