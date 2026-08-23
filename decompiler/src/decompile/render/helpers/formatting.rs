//! String and byte-array literal formatting helpers used by `pretty.rs`.

/// Escape special characters in a string.
pub(in crate::decompile::render) fn escape_string(s: &str) -> String {
    s.chars()
        .flat_map(|c| match c {
            '\\' => vec!['\\', '\\'],
            '"' => vec!['\\', '"'],
            '\n' => vec!['\\', 'n'],
            '\r' => vec!['\\', 'r'],
            '\t' => vec!['\\', 't'],
            '\0' => vec!['\\', '0'],
            c => vec![c],
        })
        .collect()
}

/// Check if all bytes in a slice are printable ASCII (0x20..=0x7E).
/// Returns false for empty slices.
pub(in crate::decompile::render) fn is_printable_ascii(bytes: &[u8]) -> bool {
    !bytes.is_empty() && bytes.iter().all(|&b| (0x20..=0x7E).contains(&b))
}

/// Format a byte array as either a text literal `"..."` (if all
/// printable ASCII) or a hex literal `#"..."`.
///
/// No `@` prefix. In the Aiken-like surface this renders, `"TOKEN"` IS the
/// `ByteArray` literal and `@"TOKEN"` is a `String` — a different type, and
/// the one every trace and `fail` message in the output already uses.
/// Printing an asset name as `@"TOKEN"` therefore both mistyped it and made
/// it indistinguishable from diagnostic text; `Pair("TOKEN", #"4200…")`
/// reads the same and says the right thing.
pub(in crate::decompile::render) fn format_byte_array(bytes: &[u8]) -> String {
    if is_printable_ascii(bytes) {
        let s = std::str::from_utf8(bytes).unwrap();
        format!("\"{}\"", escape_string(s))
    } else {
        format!("#\"{}\"", hex::encode(bytes))
    }
}
