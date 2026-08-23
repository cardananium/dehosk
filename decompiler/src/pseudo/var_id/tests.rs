use super::*;
use std::cell::Cell;

#[test]
fn test_intern_returns_same_id() {
    let mut interner = VarInterner::new();
    let id1 = interner.intern("x");
    let id2 = interner.intern("x");
    assert_eq!(id1, id2);
}

#[test]
fn test_intern_fresh_always_new() {
    let mut interner = VarInterner::new();
    let id1 = interner.intern_fresh("tail");
    let id2 = interner.intern_fresh("tail");
    assert_ne!(id1, id2);
    // Each intern_fresh creates a globally unique display name.
    assert!(interner.resolve(id1).starts_with("tail_"));
    assert!(interner.resolve(id2).starts_with("tail_"));
    assert_ne!(interner.resolve(id1), interner.resolve(id2));
}

#[test]
fn test_resolve() {
    let mut interner = VarInterner::new();
    let id = interner.intern("my_var");
    assert_eq!(interner.resolve(id), "my_var");
}

#[test]
fn test_rename() {
    let mut interner = VarInterner::new();
    let id = interner.intern_fresh("x");
    assert!(interner.resolve(id).starts_with("x_"));
    interner.rename(id, "script_context");
    assert_eq!(interner.resolve(id), "script_context");
}

#[test]
fn test_rename_clears_reverse_lookup() {
    let mut interner = VarInterner::new();
    let id = interner.intern("x");
    interner.rename(id, "y");
    // After rename, intern("x") should create a new VarId, not return the old one.
    let id2 = interner.intern("x");
    assert_ne!(id, id2);
    assert_eq!(interner.resolve(id), "y");
    assert_eq!(interner.resolve(id2), "x");
}

#[test]
fn test_different_names_different_ids() {
    let mut interner = VarInterner::new();
    let id_x = interner.intern("x");
    let id_y = interner.intern("y");
    assert_ne!(id_x, id_y);
}

#[test]
fn test_display() {
    let id = VarId(42);
    assert_eq!(format!("{}", id), "v42");
}

#[test]
fn test_allocate_from_cell_rejects_binding_range_exhaustion() {
    let counter = Cell::new(COMPAT_PLACEHOLDER_START);
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = allocate_from_cell(
            &counter,
            AUTHORITATIVE_BINDING_START,
            COMPAT_PLACEHOLDER_START,
            "test_binding",
        );
    }))
    .expect_err("expected out-of-range authoritative allocation to panic");

    let message = if let Some(s) = panic.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = panic.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic>".to_string()
    };
    assert!(message.contains("test_binding"));
    assert!(message.contains("exhausted or corrupted"));
}

#[test]
fn test_allocate_from_cell_rejects_synthetic_wraparound() {
    let counter = Cell::new(SYNTHETIC_UPPER_EXCLUSIVE);
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = allocate_from_cell(
            &counter,
            COMPAT_PLACEHOLDER_START,
            SYNTHETIC_UPPER_EXCLUSIVE,
            "test_synthetic",
        );
    }))
    .expect_err("expected exhausted synthetic allocation to panic");

    let message = if let Some(s) = panic.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = panic.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic>".to_string()
    };
    assert!(message.contains("test_synthetic"));
    assert!(message.contains("exhausted or corrupted"));
}

#[test]
fn test_interner_next_id_allocates_sequentially() {
    let id0 = interner_next_id(0);
    let id1 = interner_next_id(1);
    let id_mid = interner_next_id(12345);
    assert_eq!(id0.as_u32(), 0);
    assert_eq!(id1.as_u32(), 1);
    assert_eq!(id_mid.as_u32(), 12345);
}

#[test]
fn test_interner_next_id_panics_at_upper_bound() {
    let panic = std::panic::catch_unwind(|| {
        let _ = interner_next_id(INTERNER_UPPER_EXCLUSIVE as usize);
    })
    .expect_err("expected interner_next_id to panic at upper bound");

    let message = if let Some(s) = panic.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = panic.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic>".to_string()
    };
    assert!(message.contains("VarInterner exhausted"));
    assert!(message.contains("1000000000"));
}

#[test]
fn test_interner_next_id_panics_above_upper_bound() {
    let panic = std::panic::catch_unwind(|| {
        let _ = interner_next_id(INTERNER_UPPER_EXCLUSIVE as usize + 1);
    })
    .expect_err("expected interner_next_id to panic above upper bound");

    assert!(
        panic.downcast_ref::<&str>().is_some() || panic.downcast_ref::<String>().is_some(),
        "panic payload was not a string"
    );
}

#[test]
fn fresh_binding_is_thread_local() {
    // Cross-thread isolation: a burner thread's allocations must not
    // advance this thread's counter.
    let before = VarId::fresh_binding();
    std::thread::spawn(|| {
        // Burner: advance a different thread's counter by 5000 ids.
        for _ in 0..5000 {
            let _ = VarId::fresh_binding();
        }
    })
    .join()
    .unwrap();
    let after = VarId::fresh_binding();
    // Main thread counter should advance by exactly 1 — not by ~5000.
    assert_eq!(
        after.as_u32(),
        before.as_u32() + 1,
        "fresh_binding must be thread-local; burner thread's allocations must not advance our counter",
    );
}
