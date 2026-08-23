use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{PseudoExpr, WhenClause};
use crate::pseudo::fold::{ExprFolder, FoldAction};
use crate::pseudo::var_id::VarId;

use super::{rename_compat_var_in_expr, rename_var_use_by_id_in_expr};

#[cfg(test)]
pub(crate) fn debug_prefix_bare_extractor_lets_with_field_name(expr: PseudoExpr) -> PseudoExpr {
    prefix_bare_extractor_lets_with_field_name(expr)
}

// Prefix `let list = Data.un_list(X.field)` with the field name
//
// `simplify::helpers::naming::suggest_generated_binding_name` skips the
// `{src}_{stem}` form when the source var is a synthetic alias, falling
// back to the bare stem (`list`, `map`, `int`, `bytes`). Once
// Cardano-context naming resolves the alias and the let value displays
// as `Data.un_X(parent.field)`, the richer `field_stem` name
// (`outputs_list`, `mint_map`) is recoverable — the same shape an
// already-named source produces directly.

const EXTRACTOR_TYPE_STEMS: &[(&str, &str)] = &[
    ("Data.un_list", "list"),
    ("Data.to_list", "list"),
    ("Data.un_map", "map"),
    ("Data.to_map", "map"),
    ("Data.un_int", "int"),
    ("Data.to_int", "int"),
    ("Data.un_bytearray", "bytes"),
    ("Data.to_bytes", "bytes"),
];

fn extractor_type_stem(name: &str) -> Option<&'static str> {
    EXTRACTOR_TYPE_STEMS
        .iter()
        .find_map(|(b, stem)| (*b == name).then_some(*stem))
}

struct ExtractorPrefixer {
    used_names: HashSet<String>,
}

impl ExprFolder for ExtractorPrefixer {
    // The original visited a clause's body before its guard (reversed from
    // the trait's default guard-then-body) and never touched the pattern
    // (so a `Literal` pattern's expression was left alone) — matched here
    // rather than widened.
    fn fold_clause(&mut self, clause: WhenClause) -> WhenClause {
        let mut clause = clause;
        clause.body = self.fold(clause.body);
        clause.guard = clause.guard.map(|g| self.fold(g));
        clause
    }

    fn pre_let(
        &mut self,
        name: &str,
        id: &Option<VarId>,
        value: &PseudoExpr,
        body: &PseudoExpr,
    ) -> FoldAction {
        let value = self.fold(value.clone());
        let bare_stem = extractor_type_stem(match &value {
            PseudoExpr::BuiltinCall { name, args } if args.len() == 1 => name.as_str(),
            _ => "",
        });
        let new_name = if let Some(stem) = bare_stem {
            // Rename when the binding name is exactly the bare type stem
            // (`list`, `map`, `int`, `bytes`) OR a numeric dedup suffix of
            // it (`map_1`, `int_2`). Skip names with non-numeric prefixes
            // (e.g. `inputs_bytes`) — those are already meaningful.
            let is_dedup_suffix = name.starts_with(stem)
                && name.len() > stem.len()
                && name.as_bytes()[stem.len()] == b'_'
                && name[stem.len() + 1..].chars().all(|c| c.is_ascii_digit());
            let is_renamable = name == stem || is_dedup_suffix;
            if !is_renamable {
                name.to_string()
            } else if let Some(field_name) = source_field_name(&value) {
                let candidate = format!("{}_{}", field_name, stem);
                if !self.used_names.contains(&candidate) {
                    candidate
                } else {
                    name.to_string()
                }
            } else {
                name.to_string()
            }
        } else {
            name.to_string()
        };

        self.used_names.insert(new_name.clone());
        let body = if new_name != name {
            let renamed_body = if let Some(real_id) = id.get() {
                rename_var_use_by_id_in_expr(body, real_id, &new_name)
            } else {
                rename_compat_var_in_expr(body, name, &new_name)
            };
            self.fold(renamed_body)
        } else {
            self.fold(body.clone())
        };

        FoldAction::Replace(PseudoExpr::Let {
            name: new_name,
            id: *id,
            value: PBox::new(value),
            body: PBox::new(body),
        })
    }
}

pub(super) fn prefix_bare_extractor_lets_with_field_name(expr: PseudoExpr) -> PseudoExpr {
    ExtractorPrefixer {
        used_names: HashSet::new(),
    }
    .fold(expr)
}

fn source_field_name(value: &PseudoExpr) -> Option<String> {
    let PseudoExpr::BuiltinCall { args, .. } = value else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    match &args[0] {
        PseudoExpr::FieldAccess { selector, .. } => {
            let name = selector.as_pretty_name();
            if name == "fields" || name == "tag" {
                None
            } else {
                Some(name.to_string())
            }
        }
        _ => None,
    }
}
