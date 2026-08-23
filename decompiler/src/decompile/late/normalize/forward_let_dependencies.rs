use crate::decompile::helper::hoist::var_is_referenced_id_aware;
use crate::decompile::ref_retarget::{refs_need_retarget_by_scope, retarget_refs_by_scope};
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

pub(crate) fn repair_forward_let_dependencies(expr: PseudoExpr) -> PseudoExpr {
    struct ForwardLetDependencyRewriter;

    impl ExprFolder for ForwardLetDependencyRewriter {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_let(
            &mut self,
            name: String,
            id: Option<VarId>,
            value: PseudoExpr,
            body: PseudoExpr,
        ) -> PseudoExpr {
            if let PseudoExpr::Let {
                name: inner_name,
                id: Some(inner_id),
                value: inner_value,
                body: inner_body,
            } = body
            {
                let outer_depends_on_inner =
                    var_is_referenced_id_aware(&value, inner_id, &inner_name);
                let inner_depends_on_outer = var_is_referenced_id_aware(
                    &inner_value,
                    id.unwrap_or_else(VarId::fresh_compat_placeholder),
                    &name,
                );

                if outer_depends_on_inner && !inner_depends_on_outer {
                    return PseudoExpr::Let {
                        name: inner_name,
                        id: Some(inner_id),
                        value: inner_value,
                        body: PBox::new(PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: inner_body,
                        }),
                    };
                }

                return PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(PseudoExpr::Let {
                        name: inner_name,
                        id: Some(inner_id),
                        value: inner_value,
                        body: inner_body,
                    }),
                };
            }

            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }
    }

    let repaired = ForwardLetDependencyRewriter.fold(expr);

    if refs_need_retarget_by_scope(&repaired) {
        retarget_refs_by_scope(repaired)
    } else {
        repaired
    }
}
