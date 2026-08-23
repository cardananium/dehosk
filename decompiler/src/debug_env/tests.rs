use super::*;

/// Two switches sharing a variable would make one of them silently
/// un-settable on its own.
#[test]
fn every_switch_has_its_own_variable() {
    let mut seen = std::collections::HashSet::new();
    for (name, var) in ALL {
        assert!(
            seen.insert(*var),
            "`{name}` reuses the variable `{var}` that another switch already claims",
        );
        assert!(
            var.starts_with("DEHOSK_") || var.starts_with("DEBUG_"),
            "`{name}` reads `{var}`, which is not namespaced to this crate",
        );
    }
}
