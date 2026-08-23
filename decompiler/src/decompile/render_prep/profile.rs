//! Per-step timing for [`prepare_for_render`].
//!
//! `prepare_for_render` is a chain of ~140 passes, and a single render
//! runs the whole chain several times (the stub-ADT provenance view, the
//! DCE view, one per purpose handler, and the printer's own). It is the
//! largest single cost in a decompile, and until this existed there was
//! no way to ask which of the 140 was responsible: the core pipeline one
//! layer up reports per-pass telemetry through `PipelineExecutor`, but
//! render-prep was a straight line of `let` bindings that reported
//! nothing.
//!
//! Every step goes through [`PrepRun::step`], which also puts the pass's
//! NAME at each call site — the chain had 141 bindings drawn from 54
//! names, `ctor_inlined` shadowing itself 29 times in a row, so the
//! binding names had long stopped saying which pass had just run.
//!
//! [`prepare_for_render`]: super::prepare_for_render

use std::time::Duration;

// Only the `debug_assertions` dependency check below reads this. Left
// unconditional it is an unused import in a release build, which the
// workspace's `unused = "deny"` turns into a hard error — a break that no
// debug build or test can see, because both have `debug_assertions` on.
#[cfg(debug_assertions)]
use super::pass_order::MUST_RUN_AFTER;

/// A monotonic reading, where the platform has one.
///
/// `wasm32-unknown-unknown` has no clock: `Instant::now()` there is a
/// `panic!("time not implemented on this platform")`, which surfaces in
/// a browser as `RuntimeError: unreachable`. The decompiler ships to the
/// browser, so timing every one of ~140 steps unconditionally — which is
/// what this module first did — broke every render on that target.
///
/// The shim keeps the call sites identical and reports `Duration::ZERO`
/// where there is nothing to read; [`PrepProfile::is_measured`] says
/// which case a caller is looking at, so a zeroed profile is never
/// printed as if it had been measured.
mod clock {
    use std::time::Duration;

    /// Whether this target can time anything at all.
    pub(super) const MEASURES: bool = cfg!(not(target_arch = "wasm32"));

    #[cfg(not(target_arch = "wasm32"))]
    pub(super) struct Start(std::time::Instant);
    #[cfg(target_arch = "wasm32")]
    pub(super) struct Start;

    #[cfg(not(target_arch = "wasm32"))]
    pub(super) fn start() -> Start {
        Start(std::time::Instant::now())
    }
    #[cfg(target_arch = "wasm32")]
    pub(super) fn start() -> Start {
        Start
    }

    #[cfg(not(target_arch = "wasm32"))]
    pub(super) fn elapsed(start: Start) -> Duration {
        start.0.elapsed()
    }
    #[cfg(target_arch = "wasm32")]
    pub(super) fn elapsed(_start: Start) -> Duration {
        Duration::ZERO
    }

    // Compiling is not proof: `std::time::Instant` EXISTS on wasm, it
    // just panics when read. This fails the wasm build outright if the
    // `cfg` split above ever stops holding.
    #[cfg(target_arch = "wasm32")]
    const _: () = assert!(
        !MEASURES,
        "the wasm build must not take the clock path — `Instant::now()` panics there",
    );
    #[cfg(not(target_arch = "wasm32"))]
    const _: () = assert!(MEASURES, "a native build should be timing the passes");
}

/// The steps of one `prepare_for_render` call, in the order they ran.
#[derive(Debug, Clone, Default)]
pub(crate) struct PrepProfile {
    steps: Vec<(&'static str, Duration)>,
}

impl PrepProfile {
    /// Total time across every step.
    pub(crate) fn total(&self) -> Duration {
        self.steps.iter().map(|(_, d)| *d).sum()
    }

    /// Whether the durations mean anything on this target.
    ///
    /// `false` on `wasm32-unknown-unknown`, which has no clock — the
    /// step NAMES and their order are still recorded, the timings are
    /// all `Duration::ZERO`.
    pub(crate) fn is_measured(&self) -> bool {
        clock::MEASURES
    }

    /// A human-readable table, slowest first, with the share of the run
    /// each step took. Steps below `min_share` are folded into one
    /// remainder line so the table stays readable at 140 entries.
    pub(crate) fn render_table(&self, min_share: f64) -> String {
        if self.steps.is_empty() {
            return "render-prep profile: no steps recorded".to_string();
        }
        if !self.is_measured() {
            return format!(
                "render-prep profile — {} steps ran, but this target has no clock \
                 (`wasm32-unknown-unknown`),\nso there is nothing to report. Run the \
                 profile on a native build.",
                self.steps.len(),
            );
        }
        let total = self.total().as_secs_f64();
        if total <= 0.0 {
            return "render-prep profile: every step measured as zero".to_string();
        }
        let mut ranked: Vec<(&'static str, Duration)> = self.steps.clone();
        ranked.sort_by(|a, b| b.1.cmp(&a.1));

        let mut out = format!(
            "render-prep profile — {} steps, {:.1} ms total for ONE pass over the tree.\n\
             A full render prepares the tree several times over (analysis views, the\n\
             DCE view, one per purpose handler, and the printer's own), so multiply.\n\n\
             {:>9}  {:>6}  {}\n",
            self.steps.len(),
            total * 1000.0,
            "ms",
            "share",
            "step",
        );
        let mut folded = Duration::ZERO;
        let mut folded_count = 0usize;
        for (name, d) in &ranked {
            let share = d.as_secs_f64() / total;
            if share < min_share {
                folded += *d;
                folded_count += 1;
                continue;
            }
            out.push_str(&format!(
                "{:>9.3}  {:>5.1}%  {}\n",
                d.as_secs_f64() * 1000.0,
                share * 100.0,
                name,
            ));
        }
        if folded_count > 0 {
            out.push_str(&format!(
                "{:>9.3}  {:>5.1}%  ({folded_count} steps below {:.1}%)\n",
                folded.as_secs_f64() * 1000.0,
                folded.as_secs_f64() / total * 100.0,
                min_share * 100.0,
            ));
        }
        out
    }
}

/// Records each step of one `prepare_for_render` call, and checks the
/// chain's declared ORDER as it goes.
///
/// Timing goes through [`clock`], which is a no-op on targets without a
/// clock — see its docs. Where there IS one it is unconditional: two
/// readings per step is ~40 ns against steps that walk the whole tree,
/// so gating it would buy noise and cost a reason to doubt the numbers.
///
/// The order check is `debug_assert`-only — it can only fail on an edit
/// to the chain, and that edit is made and tested in a debug build.
pub(crate) struct PrepRun {
    profile: PrepProfile,
    /// Passes that have already run, for [`MUST_RUN_AFTER`].
    done: std::collections::HashSet<&'static str>,
}

impl PrepRun {
    pub(crate) fn new() -> Self {
        Self {
            profile: PrepProfile::default(),
            done: std::collections::HashSet::new(),
        }
    }

    /// Run one step, recording what it cost under `name` and checking
    /// that everything `name` declares it must follow has already run.
    pub(crate) fn step<T>(&mut self, name: &'static str, f: impl FnOnce() -> T) -> T {
        #[cfg(debug_assertions)]
        if let Some((_, deps)) = MUST_RUN_AFTER.iter().find(|(p, _)| *p == name) {
            for dep in *deps {
                assert!(
                    self.done.contains(dep),
                    "render-prep order: `{name}` must run after `{dep}`, which has not run \
                     yet. Either the chain was reordered, or `{dep}` was removed — see \
                     `pass_order::MUST_RUN_AFTER` for why the dependency exists.",
                );
            }
        }
        self.done.insert(name);
        let started = clock::start();
        let out = f();
        self.profile.steps.push((name, clock::elapsed(started)));
        out
    }

    pub(crate) fn finish(self) -> PrepProfile {
        self.profile
    }
}

#[cfg(test)]
impl PrepProfile {
    /// The passes that ran, in order — what `order_matches_the_chain`
    /// compares against [`PREP_PASS_ORDER`].
    pub(super) fn pass_names(&self) -> Vec<&'static str> {
        self.steps.iter().map(|(n, _)| *n).collect()
    }
}
