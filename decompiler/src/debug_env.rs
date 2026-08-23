//! The crate's developer trace switches, in one place.
//!
//! Every entry here gates an `eprintln!` and nothing else: they change
//! what is printed to stderr, never what is decompiled. Options that
//! change the OUTPUT are [`DecompileOptions`] fields, not switches — see
//! `strip_all_traces` / `strip_plutustx_traces`, which used to live here
//! as `DEHOSK_STRIP_TRACES` / `DEHOSK_STRIP_PLUTUSTX_TRACES`.
//!
//! Two reasons this is a module and not a `std::env::var` at each site.
//! It is an INVENTORY — the set of switches was previously discoverable
//! only by grepping for `DEHOSK_` across 300 files. And each value is
//! read ONCE per process: the calls sit inside hot recursive walks, where
//! `env::var` allocates a `String` and scans the environment every time.
//!
//! Reading is `OnceLock`-cached, so a switch set after the first read is
//! not picked up — which is what you want anyway: these are set on the
//! command line before the run, and a value that could change mid-run
//! would make the trace it produces impossible to interpret.
//!
//! [`DecompileOptions`]: crate::decompile::DecompileOptions

use std::sync::OnceLock;

/// Declare one switch: a `pub(crate) fn` returning whether its variable
/// is set, cached after the first read.
macro_rules! switches {
    ($( $(#[$doc:meta])* $name:ident = $var:literal ),+ $(,)?) => {
        $(
            $(#[$doc])*
            ///
            #[doc = concat!("Set `", $var, "` to any value to enable.")]
            pub(crate) fn $name() -> bool {
                static CACHED: OnceLock<bool> = OnceLock::new();
                *CACHED.get_or_init(|| std::env::var_os($var).is_some())
            }
        )+

        /// Every switch and its variable, for a `--help`-style listing and
        /// so a test can assert the names stay unique.
        #[cfg(test)]
        pub(crate) const ALL: &[(&str, &str)] = &[$((stringify!($name), $var)),+];
    };
}

switches! {
    /// Report each VarKind-recovery dispatch and how the typed and legacy
    /// paths compared on it.
    varkind_recovery = "DEHOSK_VARKIND_RECOVERY_DEBUG",
    /// Report the VarKind-recovery sites where the typed path has no
    /// annotation to dispatch on.
    varkind_recovery_gaps = "DEHOSK_VARKIND_RECOVERY_GAP_DEBUG",
    /// Dump the MIR data-tag orientation probe.
    datatag_probe = "DEHOSK_DATATAG_PROBE",
    /// Dump the rec-fn self-reference probe.
    recfn_self_ref = "DEBUG_RECFN_SELF_REF",
    /// Dump the per-arm scalar-kind table the Cardano sum naming gates on.
    scalar_kind = "DEHOSK_SCALARKIND",
    /// Dump the inter-procedural param-slot provenance report.
    provenance = "DEHOSK_PROVENANCE",
    /// Dump the name-orphan audit trace.
    orphan_trace = "DEHOSK_ORPHAN_TRACE",
}

/// The single binder name the name-orphan audit should report on, if the
/// run was narrowed to one.
///
/// A value rather than a flag, so it is spelled out here instead of
/// declared by the macro above.
pub(crate) fn name_orphan_target() -> &'static str {
    static CACHED: OnceLock<String> = OnceLock::new();
    CACHED.get_or_init(|| std::env::var("DEHOSK_NAME_ORPHAN_TARGET").unwrap_or_default())
}

#[cfg(test)]
mod tests;
