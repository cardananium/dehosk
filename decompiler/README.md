# dehosk

A decompiler that transforms UPLC (Untyped Plutus Core) bytecode into
human-readable pseudocode.

## Overview

This tool helps analyze compiled Cardano smart contracts by converting
their low-level UPLC representation back into a higher-level, more
readable format. The original source cannot be fully reconstructed
(some information is irreversibly lost during compilation), but the
output is much easier to understand than raw UPLC.

## Features

- **Pattern Recognition**: Recognizes common patterns like if-then-else, when/case expressions, and boolean operations
- **Type Inference**: Infers types from builtin usage and constructor patterns
- **Smart Naming**: Generates meaningful variable names based on usage context
- **Blueprint Support**: Extracts metadata from `plutus.json` for better decompilation
- **Multiple Input Formats**: Supports hex-encoded, CBOR, and Flat-encoded UPLC

## Installation

Build from source:

```bash
cd decompiler
cargo build --release
```

## Usage

### Decompile from hex

```bash
dehosk hex <hex_string>
```

### Decompile from file

```bash
dehosk file path/to/script.uplc
dehosk file path/to/script.cbor --format cbor
```

### Decompile from blueprint

```bash
# List available validators
dehosk blueprint plutus.json

# Decompile specific validator
dehosk blueprint plutus.json --validator "my_validator.spend"

# Decompile all validators
dehosk blueprint plutus.json --all
```

### Options

Quick reference for the most common flags — see [OPTIONS.md](OPTIONS.md)
for the rest (`--emit`, wrap shape, surface spelling, library).

- `--raw`: Disable pattern recognition (output raw translation)
- `--safe-mode`: Conservative decompilation (disables ambiguous rewrites)
- `--no-types`: Disable type inference
- `--no-optimize`: Skip the simplification pipeline (keep every let)
- `--script-version <v1|v2|v3>`: Plutus script version (enables Cardano-domain field naming)
- `--purpose <spend|mint|withdraw|certificate|vote>`: Force single-purpose interpretation
- `--split-purposes <auto|always|never>`: How to split multi-purpose validator bodies
- `--script-kind <auto|validator|plain>`: Render as validator block vs plain function
- `--applied-as <compile|runtime|N>`: How to interpret the outer Apply chain
- `--no-stub-adts`: Keep raw `Constr<N>` instead of synthesizing `pub type Unknown_S_<N>`
- `--no-prelude-constructors`: Render `True`/`False`/`Some`/`None`/`Void` as `Constr<N>`
- `--verbose`: Show verbose output
- `--output <file>` / `-o`: Write to file instead of stdout
- `--debug-bundle <path>`: Write JSON bundle with node provenance, bindings, rewrites, and source-map

### Debug Bundle

Use the bundle to build a debugger/UI on top of decompiled output:

```bash
dehosk hex <hex_string> --safe-mode --debug-bundle debug.json
```

For blueprints:

```bash
dehosk blueprint plutus.json --all --safe-mode --debug-bundle debug_dir
```

This exports:
- Stable node ids (`ExprId`)
- Binding graph (`BindingId`, binder/use relation)
- Explicit expression edges (`from_expr -> to_expr`, role-tagged)
- UPLC origin mapping (`uplc_uniq_id`)
- Ambiguity notes (`node_id`, alternatives, confidence)
- Rewrite journal (`pass`, `input_ids`, `output_ids`, `reason`)
- UPLC source map (`uplc_source_map`: `expr_id -> rendered_uplc_code` span)
- Decompiled code source map (`code_source_map`) populated from final pass snapshot (best-effort span matching)
- Pass snapshots with stable lineage ids (`stable_id`) for cross-pass debugger stepping

## Example Output

Given a simple validator like:

```
validator simple {
  spend(datum: Option<Int>, redeemer: Int, _ctx: Data) {
    when datum is {
      Some(x) -> x == redeemer
      None -> redeemer == 0
    }
  }
}
```

The decompiler produces output similar to:

```
fn(datum, redeemer, context) {
  when datum is {
    Some(x) -> x == redeemer
    None -> redeemer == 0
  }
}
```

## Limitations

### Cannot Be Recovered

- **Original variable/function names**: DeBruijn indices replace names during compilation
- **Comments and documentation**: Stripped during compilation
- **Type aliases**: Expanded and lost
- **Unused code**: Dead code elimination removes it
- **Module structure**: Flattened during compilation

### Partially Recoverable

- **Types**: Can be inferred from builtins and constructors, but not always accurately
- **Custom data types**: Can identify constructor structure, but not original names
- **Pattern matching**: Can recognize patterns, but variable bindings may differ

### Well Recovered

- **Control flow**: If-then-else, when/case expressions
- **Arithmetic and comparisons**: Mapped back to operators
- **List/ByteArray operations**: Recognized as stdlib calls
- **Boolean logic**: AND, OR, NOT patterns recognized
- **Cryptographic operations**: Hash functions, signature verification

## Architecture

UPLC bytes → parser (`uplc` crate) → MIR (mid-level IR with execution-aware
analysis) → PseudoExpr → simplify pipeline → pretty printer.

- [WHY_IT_WORKS.md](WHY_IT_WORKS.md) — why recovering readable code from
  erased bytecode is possible at all, the compiler idioms that make it
  tractable, and the discipline that keeps the output honest. Start here.
- [ARCHITECTURE.md](ARCHITECTURE.md) — what lives where, including MIR.

## Development

See [AGENTS.md](AGENTS.md) and [CONTRIBUTING.md](CONTRIBUTING.md).

```bash
cargo test -p dehosk --lib
```

## License and disclaimer

Apache-2.0. Provided "AS IS", without warranty of any kind; sections 7
and 8 of the license apply in full. The authors do not control the
purposes for which third parties use this software and accept no
responsibility for such use.
