//! Shared helpers for orphan-guard tests.
//!
//! Named-corpus gates live in the overlay; this module only keeps
//! the stack and env helpers those tests call.

#![cfg(test)]

use crate::decompile::tests::pipeline_parity_test_lock;

pub(crate) fn run_with_large_stack<F>(f: F)
where
    F: FnOnce() + Send + 'static,
{
    let handle = std::thread::Builder::new()
        .name("large_stack".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn large_stack test thread");
    if let Err(payload) = handle.join() {
        std::panic::resume_unwind(payload);
    }
}

#[allow(dead_code)] // overlay opt-in orphan-assert probe
/// Run `f` with the pipeline's per-pass orphan assert on.
///
/// The switch is process-wide, so the pipeline-parity mutex serializes
/// callers. It used to be an environment variable set through
/// `unsafe { env::set_var }` — sound only if nothing reads the
/// environment concurrently, which the pipeline itself did on every pass.
pub(crate) fn with_orphan_assert_enabled<T>(f: impl FnOnce() -> T) -> T {
    let _lock = pipeline_parity_test_lock()
        .lock()
        .expect("pipeline env test lock poisoned");
    let _on = crate::decompile::pipeline::pipeline_runtime::self_checks::orphan_assert_enabled();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    match result {
        Ok(value) => value,
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

/// Former name, kept so the overlay suite keeps compiling.
#[allow(dead_code)]
pub(crate) fn with_orphan_assert_env_enabled<T>(f: impl FnOnce() -> T) -> T {
    with_orphan_assert_enabled(f)
}
