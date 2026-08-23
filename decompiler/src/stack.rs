//! Stack budgets for the crate's recursive tree walks.
//!
//! [`stacker::maybe_grow`] takes a `(red zone, new segment)` pair: when
//! fewer than `red zone` bytes of the current stack remain, it allocates
//! another segment of `new segment` bytes and continues the recursion
//! there. Deeply-nested scripts routinely exceed a default thread stack,
//! so every walk over a `PseudoExpr` / MIR tree is wrapped in one.
//!
//! Only TWO budgets are actually in use, but they had been spelled out
//! at each site: 102 `const` declarations under 15 different names
//! (`PASS_RED_ZONE`, `LOWER_RED_ZONE`, `PRETTY_RED_ZONE_BYTES`, …) for
//! three distinct pairs, the third of which — a lone 64 KiB red zone in
//! `fix_combinator::pair_fix` — carried no reason and is folded into the
//! pass budget here (its walker is a plain `match`, so its frame is
//! nowhere near either red zone).
//!
//! Call [`grow_pass`] or [`grow_deep`] instead of `maybe_grow` directly,
//! so a budget change is one edit rather than fifty.

/// Headroom below which [`grow_pass`] takes a new segment.
const PASS_RED_ZONE: usize = 32 * 1024;
/// Segment size [`grow_pass`] allocates.
const PASS_SEGMENT: usize = 4 * 1024 * 1024;

/// Headroom below which [`grow_deep`] takes a new segment.
const DEEP_RED_ZONE: usize = 512 * 1024;
/// Segment size [`grow_deep`] allocates.
const DEEP_SEGMENT: usize = 16 * 1024 * 1024;

/// The budget for a single pass's walk: one render-prep / simplify /
/// naming pass recursing over the tree it was handed.
///
/// Frames are small (a `match` plus a few locals), so a 32 KiB red zone
/// leaves room for several more levels before the 4 MiB segment is taken.
pub(crate) fn grow_pass<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(PASS_RED_ZONE, PASS_SEGMENT, f)
}

/// The budget for the walks that carry a whole program in one descent —
/// MIR lowering / translation / validation, the pseudo folder, and the
/// pretty-printer, whose frames hold builders and arena documents rather
/// than a couple of locals.
///
/// The larger red zone is what makes those frames safe: 512 KiB of
/// headroom, and a 16 MiB segment so the growth itself is rare.
pub(crate) fn grow_deep<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(DEEP_RED_ZONE, DEEP_SEGMENT, f)
}
