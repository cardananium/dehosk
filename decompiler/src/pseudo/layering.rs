//! The `pseudo` layer's one architectural rule, as a test.
//!
//! `pseudo` is the AST: nodes, folds, identifiers, the nameless form.
//! `decompile` is everything that transforms and renders one. The
//! dependency runs one way, and the test below is what keeps it that
//! way — the cycle it forbids had grown to 47 references across seven
//! files before anyone noticed, because nothing was checking.
//!
//! Two things had caused it:
//!
//! * `TypeHintId` was declared up in `decompile::blueprint_registry`
//!   even though the AST NODE carries it. It now lives in
//!   [`crate::pseudo::type_hint`].
//! * The pretty-printer lived here as `pseudo::pretty`, though it needs
//!   the render context, the solved-type table and `prepare_for_render`.
//!   It now lives at `crate::decompile::render`.
//!
//! What remains are three rustdoc links, which create no compile-time
//! dependency and are allowed by name below.

#[cfg(test)]
mod tests {
    use std::path::Path;

    /// Doc links may name the upper layer — they are prose, and pointing
    /// a reader at the registry that resolves a `TypeHintId` is useful.
    fn is_doc_link(line: &str) -> bool {
        let t = line.trim_start();
        t.starts_with("///") || t.starts_with("//!") || t.starts_with("//")
    }

    fn rs_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
        for entry in std::fs::read_dir(dir)
            .expect("pseudo/ is readable")
            .flatten()
        {
            let p = entry.path();
            if p.is_dir() {
                rs_files(&p, out);
            } else if p.extension().and_then(|e| e.to_str()) == Some("rs") {
                out.push(p);
            }
        }
    }

    /// No CODE in `pseudo` may name `crate::decompile`.
    #[test]
    fn pseudo_does_not_depend_on_decompile() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/pseudo");
        let mut files = Vec::new();
        rs_files(&root, &mut files);
        assert!(!files.is_empty(), "expected to find the pseudo sources");

        // The needle itself, spelled so this file is not its own hit.
        let needle: String = ["crate", "decompile"].join("::");
        let mut offenders = Vec::new();
        for f in &files {
            if f.file_name().and_then(|n| n.to_str()) == Some("layering.rs") {
                continue;
            }
            for (i, line) in std::fs::read_to_string(f)
                .expect("source is readable")
                .lines()
                .enumerate()
            {
                if line.contains(&needle) && !is_doc_link(line) {
                    let rel = f.strip_prefix(&root).unwrap_or(f).display();
                    offenders.push(format!("  {rel}:{}: {}", i + 1, line.trim()));
                }
            }
        }
        assert!(
            offenders.is_empty(),
            "`pseudo` is the layer BELOW `decompile` and must not reach up into it.\n\
             If the item is carried by an AST node, move it down (as `TypeHintId` was);\n\
             if the code is a render concern, move it up (as the printer was).\n{}",
            offenders.join("\n"),
        );
    }
}
