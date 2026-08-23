//! Unify the field-arity of each unresolved stub constructor across
//! all of its destructuring sites.
//!
//! A Scott-encoded constructor the decompiler can't name is emitted
//! as a synthetic `Unknown_S_<ord>_<tag>` whose arity is captured at
//! collection time from the `when`/`expect` pattern — often nullary.
//! `inline_pattern_field_access::expand_pattern_for_overflow_accesses`
//! then grows each pattern site independently, so the same constructor
//! is destructured at different arities. A constructor has one fixed
//! arity, so that neither parses nor type-checks.
//!
//! Per `(type_hint, tag)` of an unresolved `ConstructorShape::Unknown`,
//! take the max field-arity over every `when`/`expect` pattern, then
//! pad every shorter pattern of that pair with `_` binders and bump
//! the pattern's shape arity to match. The matching declaration arity
//! is reconciled separately by [`super::stub_adt::reconcile_declared_arities`],
//! which reads the padded patterns back out of the rendered AST.
//!
//! Only `Unknown`-shape constructors carrying a `type_hint` are
//! touched: `Known(_)` constructors have a fixed prelude arity that
//! must not change. `_` binders introduce no referenceable name, so
//! the padded fields render as ignored.

use std::collections::HashMap;

use crate::decompile::blueprint_registry::TypeHintId;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::children;

pub(super) fn unify_constructor_pattern_arity(expr: PseudoExpr) -> PseudoExpr {
    let mut max: HashMap<(TypeHintId, usize), usize> = HashMap::new();
    collect_max_arity(&expr, &mut max);
    if max.is_empty() {
        return expr;
    }
    pad(expr, &max)
}

/// Record, per `(type_hint, tag)`, the maximum field count of any
/// unresolved-constructor `when`/`expect` pattern.
fn collect_max_arity(expr: &PseudoExpr, max: &mut HashMap<(TypeHintId, usize), usize>) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::When { clauses, .. } = cur {
            for clause in clauses {
                record_pattern(&clause.pattern, max);
            }
        }
        // Fold in value-position constructions too: a `Constr` value isn't
        // paddable, so its field count sets the floor the patterns must be
        // padded up to, keeping value, patterns and declaration uniform.
        if let PseudoExpr::Constr {
            type_hint: Some(hint),
            tag,
            fields,
            shape,
        } = cur
            && matches!(shape, ConstructorShape::Unknown { .. })
        {
            let entry = max.entry((hint.clone(), *tag)).or_insert(0);
            *entry = (*entry).max(fields.len());
        }
        for child in children(cur).into_iter().rev() {
            pending.push(child);
        }
    }
}

fn record_pattern(pattern: &WhenPattern, max: &mut HashMap<(TypeHintId, usize), usize>) {
    if let WhenPattern::Constructor {
        type_hint: Some(hint),
        tag,
        fields,
        shape,
    } = pattern
        && matches!(shape, ConstructorShape::Unknown { .. })
    {
        let entry = max.entry((hint.clone(), *tag)).or_insert(0);
        *entry = (*entry).max(fields.len());
    }
}

struct PadFolder<'a> {
    max: &'a HashMap<(TypeHintId, usize), usize>,
}

impl ExprFolder for PadFolder<'_> {
    fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
        pad_pattern(pattern, self.max)
    }

    // `pad_pattern` allocates fresh `VarId`s in call order
    // (`VarId::fresh_binding`). A `when`'s clauses are folded before its
    // subject, the reverse of `ExprFolder::fold_when`'s default, so that
    // relative order is preserved here.
    fn fold_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        let clauses = clauses.into_iter().map(|c| self.fold_clause(c)).collect();
        let subject = self.fold(subject);
        self.post_when(subject, subject_name, clauses)
    }
}

fn pad(expr: PseudoExpr, max: &HashMap<(TypeHintId, usize), usize>) -> PseudoExpr {
    PadFolder { max }.fold(expr)
}

fn pad_pattern(pattern: WhenPattern, max: &HashMap<(TypeHintId, usize), usize>) -> WhenPattern {
    if let WhenPattern::Constructor {
        type_hint: Some(hint),
        tag,
        mut fields,
        shape,
    } = pattern
    {
        if let ConstructorShape::Unknown { tag: shape_tag, .. } = shape
            && let Some(&target) = max.get(&(hint.clone(), tag))
            && fields.len() < target
        {
            while fields.len() < target {
                fields.push(Binder::new("_", VarId::fresh_binding()));
            }
            return WhenPattern::Constructor {
                type_hint: Some(hint),
                tag,
                shape: ConstructorShape::unknown_data(shape_tag, fields.len()),
                fields,
            };
        }
        return WhenPattern::Constructor {
            type_hint: Some(hint),
            tag,
            fields,
            shape,
        };
    }
    pattern
}
