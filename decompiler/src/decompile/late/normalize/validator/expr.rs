use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr};

pub(in crate::decompile::late::normalize) fn script_context_field_expr(
    script_context: &Binder,
    field: &str,
) -> PseudoExpr {
    let tx_info = PseudoExpr::field_access(
        PseudoExpr::var_with_id(script_context.name.clone(), script_context.id),
        "tx_info",
    );
    PseudoExpr::field_access(tx_info, field.to_string())
}

pub(in crate::decompile::late::normalize) fn redeemer_field_expr(
    redeemer: &Binder,
    index: usize,
) -> PseudoExpr {
    PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var_with_id(redeemer.name.clone(), redeemer.id),
            "fields",
        )),
        index,
    }
}

pub(in crate::decompile::late::normalize) fn field_binder_expr(
    record: &Binder,
    index: usize,
) -> PseudoExpr {
    PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var_with_id(record.name.clone(), record.id),
            "fields",
        )),
        index,
    }
}
