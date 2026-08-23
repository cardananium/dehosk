use super::super::*;
use crate::decompile::final_type_table::FinalTypeTable;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, PseudoType};
use crate::pseudo::var_id::VarId;
use std::rc::Rc;

#[test]
fn p3_3a_seeds_int_args_from_int_add() {
    // `IntAdd(x, y)` → x: Int, y: Int.
    let x_id = VarId::new(3500);
    let y_id = VarId::new(3501);
    let expr = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::IntAdd,
        args: vec![
            PseudoExpr::var_with_id("x", x_id),
            PseudoExpr::var_with_id("y", y_id),
        ]
        .into(),
    };

    let mut table = FinalTypeTable::new();
    super::seed_builtin_arg_types(&expr, &mut table);

    assert!(
        matches!(table.type_of_var(x_id).as_deref(), Some(PseudoType::Int)),
        "x must be Int from IntAdd, got {:?}",
        table.type_of_var(x_id)
    );
    assert!(
        matches!(table.type_of_var(y_id).as_deref(), Some(PseudoType::Int)),
        "y must be Int from IntAdd, got {:?}",
        table.type_of_var(y_id)
    );
}

#[test]
fn p3_3a_seeds_bytearray_arg_from_sha256() {
    // `Sha256(b)` → b: ByteArray.
    let b_id = VarId::new(3510);
    let expr = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::HashSha256,
        args: vec![PseudoExpr::var_with_id("b", b_id)].into(),
    };

    let mut table = FinalTypeTable::new();
    super::seed_builtin_arg_types(&expr, &mut table);

    assert!(
        matches!(
            table.type_of_var(b_id).as_deref(),
            Some(PseudoType::ByteArray)
        ),
        "b must be ByteArray from Sha256, got {:?}",
        table.type_of_var(b_id)
    );
}

#[test]
fn p3_3a_overrides_data_default_with_int() {
    // Solver may land Data on a Var; the builtin's Int evidence
    // overwrites Data (the implicit default).
    let x_id = VarId::new(3520);
    let expr = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::IntAdd,
        args: vec![PseudoExpr::var_with_id("x", x_id), PseudoExpr::int(0)].into(),
    };

    let mut table = FinalTypeTable::new();
    table.bind_var(x_id, Rc::new(PseudoType::Data));
    super::seed_builtin_arg_types(&expr, &mut table);

    assert!(
        matches!(table.type_of_var(x_id).as_deref(), Some(PseudoType::Int)),
        "Data is implicit default; should be overwritten with Int, got {:?}",
        table.type_of_var(x_id)
    );
}

#[test]
fn p3_3a_does_not_override_concrete_non_data_type() {
    // If the solver lands a concrete non-Data type (e.g. Bool from
    // a downstream `not(...)` constraint), the seeder must NOT
    // overwrite even if the builtin signature expects Int.
    let x_id = VarId::new(3530);
    let expr = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::IntAdd,
        args: vec![PseudoExpr::var_with_id("x", x_id), PseudoExpr::int(0)].into(),
    };

    let mut table = FinalTypeTable::new();
    table.bind_var(x_id, Rc::new(PseudoType::Bool));
    super::seed_builtin_arg_types(&expr, &mut table);

    assert!(
        matches!(table.type_of_var(x_id).as_deref(), Some(PseudoType::Bool)),
        "concrete non-Data type must not be demoted; got {:?}",
        table.type_of_var(x_id)
    );
}

#[test]
fn p3_3a_skips_polymorphic_builtins() {
    // `ListHead(xs)` is polymorphic — no signature. Must not seed.
    let xs_id = VarId::new(3540);
    let expr = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::ListHead,
        args: vec![PseudoExpr::var_with_id("xs", xs_id)].into(),
    };

    let mut table = FinalTypeTable::new();
    super::seed_builtin_arg_types(&expr, &mut table);

    assert!(
        table.type_of_var(xs_id).is_none(),
        "polymorphic builtin must not seed; got {:?}",
        table.type_of_var(xs_id)
    );
}

#[test]
fn p3_3a_slice_byte_string_signature_int_int_bytearray() {
    // `sliceByteString` takes (start: Int, length: Int, src:
    // ByteArray) in that order per the Plutus core spec — not
    // (ByteArray, Int, Int), which mis-seeds every arg.
    let start_id = VarId::new(3570);
    let length_id = VarId::new(3571);
    let src_id = VarId::new(3572);
    let expr = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::ByteArraySlice,
        args: vec![
            PseudoExpr::var_with_id("start", start_id),
            PseudoExpr::var_with_id("length", length_id),
            PseudoExpr::var_with_id("src", src_id),
        ]
        .into(),
    };

    let mut table = FinalTypeTable::new();
    super::seed_builtin_arg_types(&expr, &mut table);

    assert!(
        matches!(
            table.type_of_var(start_id).as_deref(),
            Some(PseudoType::Int)
        ),
        "slice arg 0 must be Int (start), got {:?}",
        table.type_of_var(start_id)
    );
    assert!(
        matches!(
            table.type_of_var(length_id).as_deref(),
            Some(PseudoType::Int)
        ),
        "slice arg 1 must be Int (length), got {:?}",
        table.type_of_var(length_id)
    );
    assert!(
        matches!(
            table.type_of_var(src_id).as_deref(),
            Some(PseudoType::ByteArray)
        ),
        "slice arg 2 must be ByteArray (src), got {:?}",
        table.type_of_var(src_id)
    );
}

#[test]
fn p3_3a_bytearray_logical_ops_have_bool_first_arg() {
    // `andByteString` (and `orByteString`, `xorByteString`) is
    // (pad_or_no: Bool, a: ByteArray, b: ByteArray).
    let pad_id = VarId::new(3580);
    let a_id = VarId::new(3581);
    let b_id = VarId::new(3582);
    let expr = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::ByteArrayAnd,
        args: vec![
            PseudoExpr::var_with_id("pad", pad_id),
            PseudoExpr::var_with_id("a", a_id),
            PseudoExpr::var_with_id("b", b_id),
        ]
        .into(),
    };

    let mut table = FinalTypeTable::new();
    super::seed_builtin_arg_types(&expr, &mut table);

    assert!(matches!(
        table.type_of_var(pad_id).as_deref(),
        Some(PseudoType::Bool)
    ));
    assert!(matches!(
        table.type_of_var(a_id).as_deref(),
        Some(PseudoType::ByteArray)
    ));
    assert!(matches!(
        table.type_of_var(b_id).as_deref(),
        Some(PseudoType::ByteArray)
    ));
}

#[test]
fn p3_3a_int_to_bytearray_signature_bool_int_int() {
    // `IntToByteArray(big_endian: Bool, size: Int, value: Int)`.
    let be_id = VarId::new(3590);
    let size_id = VarId::new(3591);
    let value_id = VarId::new(3592);
    let expr = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::IntToByteArray,
        args: vec![
            PseudoExpr::var_with_id("be", be_id),
            PseudoExpr::var_with_id("size", size_id),
            PseudoExpr::var_with_id("value", value_id),
        ]
        .into(),
    };

    let mut table = FinalTypeTable::new();
    super::seed_builtin_arg_types(&expr, &mut table);

    assert!(matches!(
        table.type_of_var(be_id).as_deref(),
        Some(PseudoType::Bool)
    ));
    assert!(matches!(
        table.type_of_var(size_id).as_deref(),
        Some(PseudoType::Int)
    ));
    assert!(matches!(
        table.type_of_var(value_id).as_deref(),
        Some(PseudoType::Int)
    ));
}

#[test]
fn p3_3a_seeds_nested_builtin_calls() {
    // Nested: `IntEq(IntAdd(a, b), c)` → a, b, c all Int.
    let a_id = VarId::new(3550);
    let b_id = VarId::new(3551);
    let c_id = VarId::new(3552);
    let expr = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::IntEq,
        args: vec![
            PseudoExpr::BuiltinCall {
                name: crate::builtins::BuiltinId::IntAdd,
                args: vec![
                    PseudoExpr::var_with_id("a", a_id),
                    PseudoExpr::var_with_id("b", b_id),
                ]
                .into(),
            },
            PseudoExpr::var_with_id("c", c_id),
        ]
        .into(),
    };

    let mut table = FinalTypeTable::new();
    super::seed_builtin_arg_types(&expr, &mut table);

    assert!(matches!(
        table.type_of_var(a_id).as_deref(),
        Some(PseudoType::Int)
    ));
    assert!(matches!(
        table.type_of_var(b_id).as_deref(),
        Some(PseudoType::Int)
    ));
    assert!(matches!(
        table.type_of_var(c_id).as_deref(),
        Some(PseudoType::Int)
    ));
}

#[test]
fn p3_3a_v3_solver_path_seeds_int_args_through_full_pipeline() {
    // Integration test: the full solver path with a Lambda whose
    // body uses IntAdd should land Int on the relevant param VarIds.
    let x_id = VarId::new(3560);
    let y_id = VarId::new(3561);
    let f_id = VarId::new(3562);
    let lambda = PseudoExpr::Lambda {
        params: vec![
            crate::pseudo::ast::Binder::new("x", x_id),
            crate::pseudo::ast::Binder::new("y", y_id),
        ],
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::builtins::BuiltinId::IntAdd,
            args: vec![
                PseudoExpr::var_with_id("x", x_id),
                PseudoExpr::var_with_id("y", y_id),
            ]
            .into(),
        }),
    };
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(lambda),
        body: PBox::new(PseudoExpr::var_with_id("f", f_id)),
    };

    let (_expr, table) = solve_type_constraints_with_final_table_versioned(
        expr,
        Some(crate::decompile::ScriptVersion::PlutusV3),
    );

    // x and y get Int from the IntAdd seed; the Lambda's Function
    // entry gets Function([Int, Int], Int) via enrichment.
    assert!(
        matches!(table.type_of_var(x_id).as_deref(), Some(PseudoType::Int)),
        "x_id must be Int through full pipeline, got {:?}",
        table.type_of_var(x_id)
    );
    let f_ty = table.type_of_var(f_id).expect("f_id must be in table");
    let PseudoType::Function { params, ret } = f_ty.as_ref() else {
        panic!("expected Function, got {:?}", f_ty);
    };
    assert!(matches!(params[0].as_ref(), PseudoType::Int));
    assert!(matches!(params[1].as_ref(), PseudoType::Int));
    assert!(matches!(ret.as_ref(), PseudoType::Int));
}
