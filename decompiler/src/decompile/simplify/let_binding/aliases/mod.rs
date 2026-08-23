use super::Simplifier;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;
use std::collections::HashSet;

impl Simplifier {
    /// Introduce aliases for repeated field/index access patterns.
    ///
    /// When the body accesses `name[i]` and `name` is a `.fields` binding, bind
    /// `field_0 = name[0]` for readability; for any other binding the index
    /// must appear more than once.
    ///
    /// The synthetic `field_N` binder is tagged with
    /// `VarKind::FieldIndexAlias { parent, index }` in
    /// [`SimplifyState::var_kinds`] when the parent's VarId is known (the
    /// source is a Var), so downstream consumers (kind_inference, nameless
    /// post-pipeline) read the kind by VarId instead of reverse-engineering
    /// the `field_N` name.
    pub(crate) fn introduce_field_index_aliases(
        &mut self,
        name: &str,
        value: &PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        let binding_id = self.binding_id(name, None);
        // capture parent's VarId if the source is a Var,
        // for VarKind::FieldIndexAlias annotation at mint time.
        let parent_id: Option<VarId> = match value {
            PseudoExpr::FieldAccess { record, .. } => match record.as_ref() {
                PseudoExpr::Var { id, .. } => *id,
                _ => None,
            },
            _ => None,
        };
        let is_fields_binding = if let PseudoExpr::FieldAccess {
            record, selector, ..
        } = value
        {
            if selector.as_pretty_name() == "fields" {
                if let PseudoExpr::Var {
                    name: record_name,
                    id: Some(record_id),
                    ..
                } = record.as_ref()
                {
                    let record_id_concrete = *record_id;
                    let record_name = self.get_renamed_with_id(record_name, Some(*record_id));
                    self.constructors.fields_bindings.insert_binding(
                        name.to_string(),
                        binding_id,
                        PseudoExpr::var_with_id(record_name, record_id_concrete),
                    );
                }
                true
            } else {
                false
            }
        } else {
            false
        };

        let index_counts = Self::collect_index_access_counts(&body, name, binding_id);

        if index_counts.is_empty() {
            return body;
        }

        let threshold = if is_fields_binding { 1 } else { 2 };

        let mut result = body;
        let mut used_names = HashSet::new();
        Self::collect_var_names(value, &mut used_names);
        Self::collect_var_names(&result, &mut used_names);
        used_names.insert(name.to_string());
        let mut indices: Vec<_> = index_counts.iter().collect();
        indices.sort_by_key(|(idx, _)| *idx);
        for &(&idx, &count) in indices.iter().rev() {
            if count >= threshold {
                // Prefer a Cardano-domain semantic name (`tx_info`,
                // `redeemer`) over the generic `field_N` when the alias
                // indexes into a known Cardano context.
                // `resolve_context_field_name` derives it from either
                // `<source>.fields[idx]` or `<fields_var>[idx]`, so
                // synthesize `<alias-parent>[idx]` — the outer Let's
                // name, itself bound to `<expr>.fields`, matches the
                // second shape.
                let synthesized_value = PseudoExpr::IndexAccess {
                    collection: PBox::new(self.make_var(name)),
                    index: idx,
                };
                let semantic_name = self
                    .resolve_context_field_name("", &synthesized_value)
                    .filter(|s| !used_names.contains(s));
                let has_semantic = semantic_name.is_some();
                let alias_name = match semantic_name {
                    Some(name) => {
                        used_names.insert(name.clone());
                        name
                    }
                    None => self.fresh_name_for_scope(&mut used_names, format!("field_{}", idx)),
                };
                let binder = self.fresh_synthetic_binder(&alias_name);
                // Tag FieldIndexAlias only when falling back to the
                // generic name — a Cardano-domain semantic name gets
                // CardanoContext instead, or the FieldIndexAlias arm in
                // `assign_names::candidate_name` overwrites it back to
                // `field_N` at render time.
                if let Some(parent) = parent_id {
                    let kind = if has_semantic {
                        let context_type =
                            crate::decompile::simplify::postprocess::ContextType::from_display_name(
                                &alias_name,
                            )
                            .map(|t| t.display_name().to_string())
                            .unwrap_or_else(|| alias_name.clone());
                        VarKind::CardanoContext { context_type }
                    } else {
                        VarKind::FieldIndexAlias { parent, index: idx }
                    };
                    self.var_kinds.kind_annotations.insert(binder.id, kind);
                }
                let access_expr = PseudoExpr::IndexAccess {
                    collection: PBox::new(self.make_var(name)),
                    index: idx,
                };
                let new_body = Self::replace_index_access(
                    result,
                    name,
                    binding_id,
                    idx,
                    &binder.name,
                    binder.id,
                );
                result = self.make_let_for_binder(binder, access_expr, new_body);
            }
        }
        result
    }
}

#[cfg(test)]
mod tests;
