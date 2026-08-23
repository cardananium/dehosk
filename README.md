# dehosk

UPLC decompiler — a library, a CLI, and a web app that turn on-chain
Plutus bytecode back into readable pseudocode.

## Build & test

```bash
# Core library
cargo build --workspace
RUST_MIN_STACK=33554432 cargo test --lib -p dehosk

# Web app (auto-builds the frontend via build.rs)
cargo build -p dehosk-web
PORT=3099 ./target/debug/dehosk-web
# → http://localhost:3099
```

## CLI

```bash
cargo run -p dehosk --bin dehosk -- --help
```

See `decompiler/OPTIONS.md` for the full decompiler option matrix.

## License and disclaimer

Licensed under the [Apache License 2.0](LICENSE). The software is
provided "AS IS", without warranty of any kind; the authors do not
control the purposes for which third parties use it and accept no
responsibility or liability for such use. See
[DISCLAIMER.md](DISCLAIMER.md).
