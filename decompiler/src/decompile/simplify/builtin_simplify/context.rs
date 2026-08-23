use super::super::Simplifier;
use super::super::postprocess::{
    ContextField, ContextType, context_field_at, singular_of_list_field,
};
use crate::BuiltinId;
use crate::decompile::ScriptVersion;
use crate::decompile::list_traversal::list_tail_argument;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

impl Simplifier {
    /// Extract the argument of a `List.tail` / `tail_list` call, in
    /// `BuiltinCall(name, [arg])`, `Apply(Var(name), [arg])`, or
    /// `Apply(BuiltinCall(name, []), [arg])` form.
    pub(in crate::decompile::simplify) fn extract_tail_arg(
        expr: &PseudoExpr,
    ) -> Option<&PseudoExpr> {
        list_tail_argument(expr)
    }

    /// Resolve a semantic name for a let binding from ScriptContext field access.
    ///
    /// Handles inline chains like `script_context.fields[0].fields[N]` as well as
    /// plain variable lookups.
    pub(in crate::decompile::simplify) fn resolve_context_field_name(
        &self,
        _binding_name: &str,
        value: &PseudoExpr,
    ) -> Option<String> {
        let version = self.script_version?;

        // Pattern 1: let x = expr.fields[N] - resolve expr recursively
        if let PseudoExpr::IndexAccess { collection, index } = value {
            if let PseudoExpr::FieldAccess {
                record, selector, ..
            } = collection.as_ref()
                && selector.as_pretty_name() == "fields"
            {
                if let Some(parent) = self.resolve_expr_context_name(record)
                    && let Some(field_name) =
                        self.resolve_context_child_name(&parent, *index, version)
                {
                    return Some(field_name);
                }
            }
            // Pattern 2: let x = known_fields_var[N]
            if let Some(parent_name) = self.resolve_expr_context_name(collection)
                && let Some(parent) = parent_name.strip_suffix("_fields")
                && let Some(field_name) = self.resolve_context_child_name(parent, *index, version)
            {
                return Some(field_name);
            }
            // Pattern 2b: `let x = inputs[N]` on a known list-typed
            // context field binds the singular form (`input`).
            if let Some(singular) = self.resolve_list_element_singular(collection) {
                return Some(singular.to_string());
            }
        }

        // Pattern 3: let x = expr.fields - track as fields-list
        if let PseudoExpr::FieldAccess {
            record, selector, ..
        } = value
            && selector.as_pretty_name() == "fields"
            && let Some(parent) = self.resolve_expr_context_name(record)
        {
            return Some(format!("{}_fields", parent));
        }

        // Pattern 4: `List.head(inputs)` and equivalent forms, on a
        // list-typed context field. Same naming as Pattern 2b.
        if let Some(singular) = self.resolve_builtin_list_element_singular(value) {
            return Some(singular.to_string());
        }

        // Pattern 5: `let x = expr.<named-cardano-field>` — the
        // binder adopts the field's own semantic name (`tx_info`,
        // `inputs`, `address`). Only reachable once `.fields[N]` /
        // `.#N` has been rewritten to `.<named>` upstream, or when an
        // earlier pass minted the access with a Cardano-domain name.
        if let PseudoExpr::FieldAccess { selector, .. } = value {
            let field = selector.as_pretty_name();
            if field != "fields" && ContextField::from_display_name(field).is_some() {
                return Some(field.to_string());
            }
        }

        None
    }

    /// If `expr` is a `Var` whose semantic name is a recognized
    /// list-typed `ContextField`, return its singular form.
    fn resolve_list_element_singular(&self, expr: &PseudoExpr) -> Option<&'static str> {
        let name = self.resolve_expr_context_name(expr)?;
        let field = ContextField::from_display_name(&name)?;
        singular_of_list_field(field)
    }

    /// If `value` is a `List.head` call or apply against a list-typed
    /// Cardano field, return the field's singular form.
    fn resolve_builtin_list_element_singular(&self, value: &PseudoExpr) -> Option<&'static str> {
        match value {
            PseudoExpr::BuiltinCall { name, args } => {
                if matches!(name, BuiltinId::ListHead) {
                    return self.resolve_list_element_singular(args.first()?);
                }
                None
            }
            PseudoExpr::Apply { function, args } => {
                if let PseudoExpr::BuiltinCall {
                    name,
                    args: builtin_args,
                } = function.as_ref()
                    && matches!(name, BuiltinId::ListHead)
                {
                    let arg = builtin_args.first().or_else(|| args.first())?;
                    return self.resolve_list_element_singular(arg);
                }
                None
            }
            _ => None,
        }
    }

    fn resolve_context_child_name(
        &self,
        parent: &str,
        index: usize,
        version: ScriptVersion,
    ) -> Option<String> {
        if let Some(name) =
            ContextType::from_display_name(parent).and_then(|t| context_field_at(t, index, version))
        {
            return Some(name.display_name().to_string());
        }
        if let Some(fields) = self.context.sum_type_field_overrides.get(parent)
            && let Some((name, _)) = fields.get(index)
        {
            return Some(name.clone());
        }
        if let Some(parent_type) = self.context.context_var_types.get(parent) {
            return ContextType::from_display_name(parent_type)
                .and_then(|t| context_field_at(t, index, version))
                .map(|f| f.display_name().to_string());
        }
        None
    }

    fn resolve_context_var_name(&self, name: &str, id: Option<VarId>) -> Option<String> {
        if let Some(var_id) = id.get() {
            if let Some(semantic) = self.context.context_field_names_by_id.get(&var_id) {
                return Some(semantic.clone());
            }
            if let Some(semantic) = self.context.context_field_names.get(name) {
                let semantic_is_id_owned = self
                    .context
                    .context_field_names_by_id
                    .values()
                    .any(|known| known == semantic);
                if semantic_is_id_owned {
                    return None;
                }
                return Some(semantic.clone());
            }
            return None;
        }
        self.context.context_field_names.get(name).cloned()
    }

    /// Iteratively resolve an expression to its semantic context name.
    ///
    /// `Var(name)` -> lookup in context_field_names;
    /// `expr.fields[N]` -> resolve expr, then look up field N;
    /// `expr.fields` -> resolve expr, return "{name}_fields";
    /// `fields_var[N]` -> resolve var, strip _fields, look up field N.
    pub(in crate::decompile::simplify::builtin_simplify) fn resolve_expr_context_name(
        &self,
        expr: &PseudoExpr,
    ) -> Option<String> {
        let version = self.script_version?;
        enum ResolveStep {
            AppendFieldsSuffix,
            IndexFromParentFields(usize),
            IndexFromFieldsVar(usize),
        }

        let mut steps = Vec::new();
        let mut current = expr;
        loop {
            match current {
                PseudoExpr::Var { name, id, .. } => {
                    let mut resolved = self.resolve_context_var_name(name, *id)?;
                    while let Some(step) = steps.pop() {
                        resolved = match step {
                            ResolveStep::AppendFieldsSuffix => format!("{}_fields", resolved),
                            ResolveStep::IndexFromParentFields(index) => {
                                self.resolve_context_child_name(&resolved, index, version)?
                            }
                            ResolveStep::IndexFromFieldsVar(index) => {
                                let parent = resolved.strip_suffix("_fields")?;
                                self.resolve_context_child_name(parent, index, version)?
                            }
                        };
                    }
                    return Some(resolved);
                }
                PseudoExpr::FieldAccess {
                    record, selector, ..
                } if selector.as_pretty_name() == "fields" => {
                    steps.push(ResolveStep::AppendFieldsSuffix);
                    current = record.as_ref();
                }
                PseudoExpr::IndexAccess { collection, index } => {
                    if let PseudoExpr::FieldAccess {
                        record, selector, ..
                    } = collection.as_ref()
                        && selector.as_pretty_name() == "fields"
                    {
                        steps.push(ResolveStep::IndexFromParentFields(*index));
                        current = record.as_ref();
                        continue;
                    }
                    steps.push(ResolveStep::IndexFromFieldsVar(*index));
                    current = collection.as_ref();
                }
                _ => return None,
            }
        }
    }

    /// Get the context type and semantic name for a variable, checking
    /// context_var_types, context_field_names, and renames.
    pub(in crate::decompile::simplify) fn get_var_context_info(
        &self,
        var_name: &str,
        var_id: Option<VarId>,
    ) -> Option<(String, String)> {
        if let Some(id) = var_id.get() {
            if let Some(t) = self.context.context_var_types_by_id.get(&id) {
                let sem = self
                    .context
                    .context_field_names_by_id
                    .get(&id)
                    .cloned()
                    .unwrap_or_else(|| var_name.to_string());
                return Some((t.clone(), sem));
            }
            if let Some(semantic) = self.context.context_field_names_by_id.get(&id)
                && let Some(t) = self.context.context_var_types.get(semantic.as_str())
            {
                return Some((t.clone(), semantic.clone()));
            }
            if let Some(semantic) = self.context.context_field_names.get(var_name) {
                let semantic_is_id_owned = self
                    .context
                    .context_field_names_by_id
                    .values()
                    .any(|known| known == semantic);
                if semantic_is_id_owned {
                    return None;
                }
            }
        }

        // Direct check: var itself in context_var_types
        if let Some(t) = self.context.context_var_types.get(var_name) {
            let sem = self
                .context
                .context_field_names
                .get(var_name)
                .cloned()
                .unwrap_or_else(|| var_name.to_string());
            return Some((t.clone(), sem));
        }
        // Via context_field_names -> semantic name -> type
        if let Some(semantic) = self.context.context_field_names.get(var_name)
            && let Some(t) = self.context.context_var_types.get(semantic.as_str())
        {
            return Some((t.clone(), semantic.clone()));
        }
        // Via renames -> renamed name -> type
        if let Some(renamed) = self
            .binding_id(var_name, var_id.get())
            .and_then(|vid| self.naming.renames.get(vid))
        {
            if let Some(t) = self.context.context_var_types.get(renamed.as_str()) {
                let sem = self
                    .context
                    .context_field_names
                    .get(renamed.as_str())
                    .cloned()
                    .unwrap_or_else(|| renamed.clone());
                return Some((t.clone(), sem));
            }
            if let Some(semantic) = self.context.context_field_names.get(renamed.as_str())
                && let Some(t) = self.context.context_var_types.get(semantic.as_str())
            {
                return Some((t.clone(), semantic.clone()));
            }
        }
        None
    }
}
