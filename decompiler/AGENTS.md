# dehosk — agent guide

Read [`ARCHITECTURE.md`](ARCHITECTURE.md) for the module map, [`OPTIONS.md`](OPTIONS.md) for flags, [`WHY_IT_WORKS.md`](WHY_IT_WORKS.md) for why inversions are sound, [`CONTRIBUTING.md`](CONTRIBUTING.md) for PRs.

## Commands

From this crate (`decompiler/`):

```bash
cargo build --release

# Library tests overflow the default stack without this.
RUST_MIN_STACK=33554432 cargo test -p dehosk --lib

# CLI — needs a hex script. A local corpus overlay (gitignored) is optional.
./target/release/dehosk hex "$(cat path/to/script.hex)" --script-version v3

# Batch tester: CSV of prepared scripts (`hash,...,bytes`). No corpus is published.
cargo run --release --bin test-decompiler -- --csv <scripts.csv> --limit 100 --verbose
```

`test-decompiler` flags that matter: `--limit N`, `--sample-size N`, `--script-id`, `--output DIR`, `--verbose`. `--debug-bundle` is a `dehosk` CLI flag, not this binary.

## Style

- Comments explain *why*, not *what*.
- No provenance prefixes (stage label, dated marker, review round, commit hash). Describe the code as it is.
- Prefer a new sibling module over growing `decompile/mod.rs`, `naming/`, or `late/normalize/`.
