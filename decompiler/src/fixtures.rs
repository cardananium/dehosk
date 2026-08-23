//! Locating the corpus inputs.
//!
//! The corpus — prepared scripts and captured mainnet executions — is
//! not distributed with the source, so nothing here may assume the
//! files are present. Every lookup returns an [`Option`]; [`None`]
//! means "this checkout does not have the corpus", not "the code is
//! broken", so callers skip rather than fail.
//!
//! Search order:
//!
//! 1. `$DEHOSK_FIXTURES/<relative>` when the variable is set;
//! 2. `$DEHOSK_OVERLAY/fixtures/<relative>` when the overlay root is set;
//! 3. `<crate>/fixtures/<relative>`, for a checkout that keeps them
//!    in-tree.

use std::path::PathBuf;

fn env_dir(name: &str) -> Option<PathBuf> {
    match std::env::var(name) {
        Ok(dir) if !dir.is_empty() => Some(PathBuf::from(dir)),
        _ => None,
    }
}

/// Overlay root: `$DEHOSK_OVERLAY`, else a workspace-local pointer file
pub(crate) fn overlay_root() -> Option<PathBuf> {
    if let Some(dir) = env_dir("DEHOSK_OVERLAY") {
        return Some(dir);
    }
    let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()?
        .to_path_buf();
    let text = std::fs::read_to_string(workspace.join(".dehosk-overlay")).ok()?;
    let line = text
        .lines()
        .map(str::trim)
        .find(|line| !line.is_empty() && !line.starts_with('#'))?;
    let path = PathBuf::from(line);
    Some(if path.is_absolute() {
        path
    } else {
        workspace.join(path)
    })
}

/// Directories searched for a corpus file, in order of precedence.
fn search_roots() -> Vec<PathBuf> {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut roots = Vec::new();

    if let Some(dir) = env_dir("DEHOSK_FIXTURES") {
        roots.push(dir);
    } else if let Some(root) = overlay_root() {
        roots.push(root.join("fixtures"));
    }
    roots.push(manifest_dir.join("fixtures"));
    roots
}

/// Resolve a corpus-relative path, or [`None`] when this checkout has no
/// copy of it.
pub(crate) fn fixture_path(relative: &str) -> Option<PathBuf> {
    search_roots()
        .into_iter()
        .map(|root| root.join(relative))
        .find(|candidate| candidate.is_file())
}

/// Resolve a corpus-relative directory, or [`None`] when this checkout
/// has no copy of it.
pub(crate) fn fixture_dir(relative: &str) -> Option<PathBuf> {
    search_roots()
        .into_iter()
        .map(|root| root.join(relative))
        .find(|candidate| candidate.is_dir())
}

/// Read a corpus file as trimmed text, or [`None`] when it is absent.
pub(crate) fn read_fixture(relative: &str) -> Option<String> {
    let path = fixture_path(relative)?;
    match std::fs::read_to_string(&path) {
        Ok(text) => Some(text.trim().to_string()),
        Err(err) => {
            // Present but unreadable is a real problem, unlike absence.
            panic!("failed to read corpus file {}: {err}", path.display());
        }
    }
}

/// Where the corpus would live if it were installed. Used by tools that
/// need to tell the user what to point `DEHOSK_FIXTURES` at.
pub(crate) fn default_fixture_root() -> PathBuf {
    search_roots()
        .into_iter()
        .next()
        .expect("search_roots always includes the in-tree fixtures dir")
}
