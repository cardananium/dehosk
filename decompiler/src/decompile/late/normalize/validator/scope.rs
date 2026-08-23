use std::collections::HashSet;

use crate::pseudo::ast::Binder;
use crate::pseudo::var_id::VarId;

#[derive(Clone, Default)]
pub(in crate::decompile::late::normalize) struct ScopeFrame {
    pub(in crate::decompile::late::normalize) bound: HashSet<String>,
    pub(in crate::decompile::late::normalize) binders: Vec<Binder>,
    pub(in crate::decompile::late::normalize) list_head: Option<Binder>,
    pub(in crate::decompile::late::normalize) constructor_subject: Option<Binder>,
    pub(in crate::decompile::late::normalize) constructor_fields: Vec<Binder>,
}

pub(in crate::decompile::late::normalize) fn is_bound(scopes: &[ScopeFrame], name: &str) -> bool {
    scopes.iter().rev().any(|scope| scope.bound.contains(name))
}

pub(in crate::decompile::late::normalize) fn nearest_list_head(
    scopes: &[ScopeFrame],
) -> Option<&Binder> {
    scopes
        .iter()
        .rev()
        .find_map(|scope| scope.list_head.as_ref())
}

pub(in crate::decompile::late::normalize) fn nearest_constructor_subject(
    scopes: &[ScopeFrame],
) -> Option<&Binder> {
    scopes
        .iter()
        .rev()
        .find_map(|scope| scope.constructor_subject.as_ref())
}

pub(in crate::decompile::late::normalize) fn nearest_constructor_field(
    scopes: &[ScopeFrame],
    index: usize,
) -> Option<&Binder> {
    scopes.iter().rev().find_map(|scope| {
        scope
            .constructor_fields
            .get(index)
            .filter(|binder| binder.name != "_")
    })
}

fn find_binder(scopes: &[ScopeFrame], name: &str) -> Option<Binder> {
    scopes
        .iter()
        .rev()
        .find_map(|scope| {
            scope
                .binders
                .iter()
                .rev()
                .find(|binder| binder.name == name)
        })
        .cloned()
}

pub(in crate::decompile::late::normalize) fn find_subject_binder(
    scopes: &[ScopeFrame],
    subject_name: &str,
    subject_id: Option<VarId>,
) -> Binder {
    scopes
        .iter()
        .rev()
        .find_map(|scope| {
            scope.binders.iter().rev().find(|binder| match subject_id {
                Some(sid) => binder.id == sid,
                None => false,
            })
        })
        .cloned()
        .or_else(|| {
            subject_id
                .is_none()
                .then(|| find_binder(scopes, subject_name))
                .flatten()
        })
        .unwrap_or_else(|| {
            Binder::new(
                subject_name.to_string(),
                subject_id.unwrap_or_else(VarId::fresh_compat_placeholder),
            )
        })
}

pub(in crate::decompile::late::normalize) fn binder_matches_var(
    binder: &Binder,
    name: &str,
    id: Option<VarId>,
) -> bool {
    crate::decompile::var_match::ref_matches_binder(name, id, binder)
}
