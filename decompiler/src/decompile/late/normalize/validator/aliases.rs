use crate::pseudo::ast::Binder;

pub(in crate::decompile::late::normalize) fn choose_generated_record_subject_alias(
    candidates: &[Binder],
    subject_name: &Binder,
) -> Option<Binder> {
    let mut unique = candidates.to_vec();
    unique.sort_by_key(|binder| binder.name.len());
    unique.dedup_by_key(|binder| binder.id);

    if unique
        .iter()
        .any(|binder| is_authoritative_same_name_different_id(binder, subject_name))
    {
        return None;
    }

    let shortest = unique.first()?.clone();
    if unique
        .iter()
        .any(|binder| binder.id != shortest.id && binder.name == shortest.name)
    {
        return None;
    }
    if unique.iter().all(|binder| {
        binder.id == shortest.id
            || binder.name == shortest.name
            || binder
                .name
                .strip_prefix(shortest.name.as_str())
                .is_some_and(|suffix| suffix.starts_with('_'))
    }) {
        Some(shortest)
    } else {
        None
    }
}

pub(in crate::decompile::late::normalize) fn is_authoritative_same_name_different_id(
    candidate: &Binder,
    subject_name: &Binder,
) -> bool {
    candidate.name == subject_name.name
        && candidate.id != subject_name.id
        && candidate.id.get().is_some()
        && subject_name.id.get().is_some()
}
