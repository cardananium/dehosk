//! `MapRenamer` — applies a decided `VarId → name` map to a tree.
//!
//! The commit half of the naming pass: everything else decides, this
//! rewrites.

use super::*;
use crate::pseudo::ast::PBox;

/// An ExprFolder that applies a pre-computed rename map.
pub(super) struct MapRenamer<'a> {
    pub(super) fallback_rename_map: &'a HashMap<String, String>,
    pub(super) let_rename_map: &'a HashMap<VarId, String>,
    pub(super) binder_rename_map: &'a HashMap<VarId, String>,
    /// Var-ref ids whose nearest in-scope binder by name carries
    /// the same VarId. Only these take the `fallback_rename_map`
    /// name-keyed path; free or mismatched-id refs are left alone
    /// rather than renamed into render-time orphans.
    pub(super) consistent_ref_ids: &'a HashSet<VarId>,
}

impl<'a> ExprFolder for MapRenamer<'a> {
    fn fold_clause(&mut self, clause: WhenClause) -> WhenClause {
        let pattern = self.rename_pattern(clause.pattern);
        let guard = clause.guard.map(|g| self.fold(g));
        let body = self.fold(clause.body);
        WhenClause {
            pattern,
            guard,
            body,
        }
    }

    fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
        // id-keyed rename takes precedence and looks up the raw stored
        // id: `binder_rename_map` is keyed by whatever VarId the binder
        // carries, so `.get()` would strip compat placeholders and miss
        // entries inserted under compat keys (e.g. `record_let_rename`).
        //
        // The name-keyed fallback fires only for "consistent" refs —
        // nearest in-scope binder by name has the same id — otherwise an
        // unrelated same-named free var is renamed into an orphan. Ids
        // that are compat placeholders carry no stable identity, so they
        // always fall back to the name.
        if let Some(vid) = id
            && let Some(renamed) = self.binder_rename_map.get(&vid)
        {
            return PseudoExpr::Var {
                name: renamed.clone(),
                id: Some(vid),
            };
        }
        let allow_name_fallback = id
            .get()
            .map(|vid| self.consistent_ref_ids.contains(&vid))
            .unwrap_or(true);
        let new_name = if allow_name_fallback {
            self.fallback_rename_map.get(&name).cloned().unwrap_or(name)
        } else {
            name
        };
        PseudoExpr::Var { name: new_name, id }
    }

    fn post_lambda(&mut self, params: Vec<Binder>, body: PseudoExpr) -> PseudoExpr {
        let params = params
            .into_iter()
            .map(|param| self.renamed_binder(param))
            .collect();
        PseudoExpr::Lambda {
            params,
            body: PBox::new(body),
        }
    }

    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        // `decompiled` is a reserved sentinel:
        // `pipeline::wrap_validator_entry_for_render` mints it so
        // `validator_shape::wrap_rendered` can find and wrap the
        // validator block. A heuristic rename would fold it into a
        // helper-cluster family (e.g. `decode_pairs_bytes_8`) and
        // break that wrap.
        if name == "decompiled" {
            return PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            };
        }
        // Look up `let_rename_map` by the raw stored id, compat
        // placeholders included: `record_let_rename` keys the map by
        // whatever VarId was on the Let, and `.get()` would strip
        // compat ids and lose the entry.
        let new_name = id
            .and_then(|vid| self.let_rename_map.get(&vid).cloned())
            .or_else(|| self.fallback_rename_map.get(&name).cloned())
            .unwrap_or(name);
        PseudoExpr::Let {
            name: new_name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }

    fn post_recfn(
        &mut self,
        name: crate::pseudo::ast::Binder,
        params: Vec<crate::pseudo::ast::Binder>,
        body: PseudoExpr,
    ) -> PseudoExpr {
        let new_name = self.renamed_binder(name);
        let params = params
            .into_iter()
            .map(|param| self.renamed_binder(param))
            .collect();
        PseudoExpr::RecFn {
            name: new_name,
            params,
            body: PBox::new(body),
        }
    }

    fn post_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name: subject_name.map(|binder| self.renamed_binder(binder)),
            clauses,
        }
    }

    fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
        // Nothing to add: the callee `Var` was already renamed by
        // `post_var` when the function child was folded.
        PseudoExpr::Apply {
            function: PBox::new(function),
            args: args.into(),
        }
    }
}

impl MapRenamer<'_> {
    fn renamed_binder(&self, binder: Binder) -> Binder {
        self.binder_rename_map
            .get(&binder.id)
            .cloned()
            .or_else(|| self.fallback_rename_map.get(binder.as_str()).cloned())
            .map(|new| binder.renamed(new))
            .unwrap_or(binder)
    }

    fn rename_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
        match pattern {
            WhenPattern::Constructor {
                type_hint,
                tag,
                fields,
                shape,
            } => WhenPattern::Constructor {
                type_hint,
                tag,
                fields: fields
                    .into_iter()
                    .map(|field| self.renamed_binder(field))
                    .collect(),
                shape,
            },
            WhenPattern::List { elements, tail } => WhenPattern::List {
                elements: elements
                    .into_iter()
                    .map(|element| self.renamed_binder(element))
                    .collect(),
                tail: tail.map(|tail| self.renamed_binder(tail)),
            },
            WhenPattern::Tuple(fields) => WhenPattern::Tuple(
                fields
                    .into_iter()
                    .map(|field| self.renamed_binder(field))
                    .collect(),
            ),
            WhenPattern::Pair(a, b) => {
                WhenPattern::Pair(self.renamed_binder(a), self.renamed_binder(b))
            }
            WhenPattern::Var(name) => WhenPattern::Var(self.renamed_binder(name)),
            WhenPattern::Wildcard => WhenPattern::Wildcard,
            WhenPattern::Literal(expr) => WhenPattern::Literal(self.fold(expr)),
        }
    }
}

// ============================================================
// Tests
// ============================================================
