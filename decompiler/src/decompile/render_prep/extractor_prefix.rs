use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::rename_compat_var_in_expr;
use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

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

/// One pending step of [`prefix_bare_extractor_lets_with_field_name`]'s walk.
///
/// A job stack, not recursion: the nesting depth is the script's to choose,
/// and on `wasm32` the call stack cannot grow to match it. The order is the
/// one the pass has always had — a `let`'s value, then its name, then its
/// body; a clause's body before its guard, and never its pattern — because
/// the names taken so far decide the next one.
enum PrefixStep {
    Enter(PseudoExpr),
    /// The value is on `done`: name the binding, then walk the body under it.
    LetBody {
        name: String,
        id: Option<VarId>,
        body: PseudoExpr,
    },
    /// Value and body are on `done`.
    Let {
        name: String,
        id: Option<VarId>,
        /// The binding was renamed by id: its uses in the body are renamed
        /// as the walk meets them, until this step closes the body.
        renamed_id: Option<VarId>,
    },
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    /// The subject, then each clause's body and guard, are on `done`.
    When {
        subject_name: Option<Binder>,
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

pub(super) fn prefix_bare_extractor_lets_with_field_name(expr: PseudoExpr) -> PseudoExpr {
    let mut used_names: HashSet<String> = HashSet::new();
    // Bindings renamed by id whose bodies are still being walked. A `Var`
    // with one of these ids takes the newest name given to it.
    let mut renamed: Vec<(VarId, String)> = Vec::new();
    let rename_of = |renamed: &[(VarId, String)], id: VarId| {
        renamed
            .iter()
            .rev()
            .find_map(|(vid, name)| (*vid == id).then(|| name.clone()))
    };

    let mut steps: Vec<PrefixStep> = vec![PrefixStep::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();
    while let Some(step) = steps.pop() {
        match step {
            PrefixStep::Enter(expr) => match expr {
                PseudoExpr::Var { name, id } => {
                    let name = id
                        .and_then(|id| rename_of(&renamed, id))
                        .unwrap_or(name);
                    done.push(PseudoExpr::Var { name, id });
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(PrefixStep::LetBody {
                        name,
                        id,
                        body: body.into_inner(),
                    });
                    steps.push(PrefixStep::Enter(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(PrefixStep::Lambda { params });
                    steps.push(PrefixStep::Enter(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(PrefixStep::RecFn { name, params });
                    steps.push(PrefixStep::Enter(body.into_inner()));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let subject_name = subject_name.map(|binder| {
                        match rename_of(&renamed, binder.id) {
                            Some(new_name) => binder.renamed(new_name),
                            None => binder,
                        }
                    });
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    let mut children: Vec<PseudoExpr> = Vec::new();
                    for clause in clauses {
                        clause_meta.push((clause.pattern, clause.guard.is_some()));
                        children.push(clause.body);
                        if let Some(guard) = clause.guard {
                            children.push(guard);
                        }
                    }
                    steps.push(PrefixStep::When {
                        subject_name,
                        clause_meta,
                    });
                    for child in children.into_iter().rev() {
                        steps.push(PrefixStep::Enter(child));
                    }
                    steps.push(PrefixStep::Enter(subject.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(PrefixStep::Plain(kind));
                        for child in children.into_iter().rev() {
                            steps.push(PrefixStep::Enter(child));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            PrefixStep::LetBody { name, id, body } => {
                let value = done.last().expect("let value");
                let new_name = prefixed_name(&name, value, &used_names);
                used_names.insert(new_name.clone());
                let mut renamed_id = None;
                let body = if new_name == name {
                    body
                } else if let Some(real_id) = id.get() {
                    renamed.push((real_id, new_name.clone()));
                    renamed_id = Some(real_id);
                    body
                } else {
                    rename_compat_var_in_expr(&body, &name, &new_name)
                };
                steps.push(PrefixStep::Let {
                    name: new_name,
                    id,
                    renamed_id,
                });
                steps.push(PrefixStep::Enter(body));
            }
            PrefixStep::Let {
                name,
                id,
                renamed_id,
            } => {
                if renamed_id.is_some() {
                    renamed.pop();
                }
                let body = done.pop().expect("let body");
                let value = done.pop().expect("let value");
                done.push(PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(body),
                });
            }
            PrefixStep::Lambda { params } => {
                let body = done.pop().expect("lambda body");
                done.push(PseudoExpr::Lambda {
                    params,
                    body: PBox::new(body),
                });
            }
            PrefixStep::RecFn { name, params } => {
                let body = done.pop().expect("recfn body");
                done.push(PseudoExpr::RecFn {
                    name,
                    params,
                    body: PBox::new(body),
                });
            }
            PrefixStep::When {
                subject_name,
                clause_meta,
            } => {
                let total = 1 + clause_meta
                    .iter()
                    .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                    .sum::<usize>();
                let mut parts = take(&mut done, total).into_iter();
                let subject = parts.next().expect("when subject");
                let clauses = clause_meta
                    .into_iter()
                    .map(|(pattern, has_guard)| {
                        let body = parts.next().expect("when clause body");
                        let guard = has_guard.then(|| parts.next().expect("when guard"));
                        WhenClause {
                            pattern,
                            guard,
                            body,
                        }
                    })
                    .collect();
                done.push(PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                });
            }
            PrefixStep::Plain(kind) => {
                let rebuilt = rebuild_plain(kind, &mut done);
                done.push(rebuilt);
            }
        }
    }
    done.pop().expect("one result")
}

/// The name for a binding `name = value`, given the names already taken.
fn prefixed_name(name: &str, value: &PseudoExpr, used_names: &HashSet<String>) -> String {
    let bare_stem = extractor_type_stem(match value {
        PseudoExpr::BuiltinCall { name, args } if args.len() == 1 => name.as_str(),
        _ => "",
    });
    let Some(stem) = bare_stem else {
        return name.to_string();
    };
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
        return name.to_string();
    }
    match source_field_name(value) {
        Some(field_name) => {
            let candidate = format!("{}_{}", field_name, stem);
            if !used_names.contains(&candidate) {
                candidate
            } else {
                name.to_string()
            }
        }
        None => name.to_string(),
    }
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
