# Contributing

Thanks for contributing to dehosk. Layout and commands: [`AGENTS.md`](AGENTS.md). Architecture: [`ARCHITECTURE.md`](ARCHITECTURE.md).

## Setup

```bash
cargo build --release
RUST_MIN_STACK=33554432 cargo test -p dehosk --lib
```

## Pull requests

- Keep the change scoped to one idea.
- Land a regression test with every behaviour fix, in the same PR.
- New public items in `src/lib.rs` should show up in `README.md` in the same PR.

## Commits

Short imperative messages, matching `git log --oneline`.

## Code

Comments explain *why*, not *what*. Prefer a new sibling module over growing `decompile/mod.rs`, `naming/`, or `late/normalize/`.
