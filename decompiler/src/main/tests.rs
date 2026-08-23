use super::*;

#[test]
fn test_normalize_hex_text_allows_multiline_hex_dump() {
    let input = "46 01 00\n00 20 01 01";
    assert_eq!(normalize_hex_text(input).as_deref(), Some("46010000200101"));
}

#[test]
fn test_normalize_hex_text_rejects_invalid_characters() {
    assert_eq!(normalize_hex_text("46gg"), None);
    assert_eq!(normalize_hex_text("46xz"), None);
}

#[test]
fn test_normalize_hex_text_rejects_odd_length() {
    assert_eq!(normalize_hex_text("abc"), None);
}

#[test]
fn test_validate_blueprint_selection_rejects_conflicting_flags() {
    let result = validate_blueprint_selection(Some("spend"), true);
    assert!(result.is_err());
}

#[test]
fn test_validate_blueprint_selection_allows_non_conflicting_flags() {
    assert!(validate_blueprint_selection(Some("spend"), false).is_ok());
    assert!(validate_blueprint_selection(None, true).is_ok());
    assert!(validate_blueprint_selection(None, false).is_ok());
}

/// The catalogue's `cli_flag` entries and clap's argument list are
/// independent declarations; this test is the only tie between them.
///
/// Forward: every flag the catalogue claims must be a long flag clap
/// parses. Reverse: every clap long flag must back a catalogue option
/// or sit in `EXPECTED_UNLINKED`, so a new flag that belongs to no
/// option has to be listed there consciously.
#[test]
fn every_catalogue_cli_flag_is_a_real_clap_flag() {
    use clap::CommandFactory;
    use dehosk::decompile::options::{Exposure, ui_options};

    let command = Cli::command();
    let long_flags: std::collections::BTreeSet<String> = command
        .get_arguments()
        .filter_map(|arg| arg.get_long())
        .map(|name| format!("--{name}"))
        .collect();

    let mut linked = std::collections::BTreeSet::new();
    for entry in ui_options() {
        let Exposure::Ui { cli_flag, .. } = entry.exposure else {
            continue;
        };
        let Some(flag) = cli_flag else { continue };
        assert!(
            long_flags.contains(flag),
            "the catalogue says `{}` is driven by `{flag}`, but the CLI has no such flag; \
             clap knows {long_flags:?}",
            entry.path.join("."),
        );
        linked.insert(flag.to_string());
    }

    /// Long flags that deliberately correspond to no single option.
    const EXPECTED_UNLINKED: &[&str] = &[
        // Whole-config presets, not options.
        "--raw",
        "--no-types",
        "--no-optimize",
        // Feed fields the catalogue marks internal.
        "--oracle-arg",
        "--oracle-tx",
        // I/O and diagnostics, not decompilation options.
        "--output",
        "--verbose",
        "--debug-bundle",
        "--help",
        "--version",
    ];

    let unlinked: Vec<&String> = long_flags
        .iter()
        .filter(|flag| !linked.contains(*flag))
        .filter(|flag| !EXPECTED_UNLINKED.contains(&flag.as_str()))
        .collect();
    assert!(
        unlinked.is_empty(),
        "these CLI flags belong to no catalogue option and are not on the expected list: \
         {unlinked:?}",
    );
}
