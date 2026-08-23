# Options

CLI flags, the library `DecompileOptions` they map to, and the few
combinations that are not "just flip a bool". Per-pass leaves,
prose, and wire tags live in one place:
`dehosk::decompile::options` (or `GET /api/options`). This file does
not copy that list.

```bash
dehosk hex 5904ac...                # CBOR-wrapped or raw flat; auto-detected
dehosk file path/to/script.uplc     # --format auto|hex|cbor|flat  (`text` is unimplemented)
dehosk blueprint plutus.json [--validator NAME | --all]
```

`plutus.json` supplies constructor names so the output is not all
`Unknown_S_<N>` stubs. Flags below are global (any subcommand).

---

## I/O

| Flag | Effect |
| --- | --- |
| `-o`, `--output FILE` | stdout otherwise. `blueprint --all` concatenates into one file; a directory is only for `--debug-bundle`. |
| `-v`, `--verbose` | one status line on stderr. Pipeline telemetry is `--debug-bundle`, not this. |
| `--debug-bundle PATH` | JSON: pass snapshots, bindings, rewrite journal, source maps. Large. `blueprint --all` wants a directory. |

---

## How far the pipeline runs

`--raw` chooses **which** clusters run. `--emit` chooses **where** it
stops. They compose: `--raw --emit raw-pseudo` is a shallow MIR seed.

### `--emit <decompiled\|uplc\|uplc-canonical\|raw-pseudo\|post-pipeline\|polarity-report>`

Default `decompiled` — full pipeline, then render-prep (stubs, validator
wrap, prelude names). Other layers skip that dressing and are **not**
compilable surface:

- `uplc` / `uplc-canonical` — echo the input (readable spine vs the
  crate's nested `[[[f a] b] c]`). No decompilation.
- `raw-pseudo` — MIR → pseudo, before structural passes.
- `post-pipeline` — after those passes, before render-prep.
- `polarity-report` — church-bool convention (Cip vs InverseCip) plus
  why. Use when `True`/`False`/`!` look wrong (PlutusTx is often
  inverted). `--oracle-arg CBOR_HEX` (repeat per runtime arg) or
  `--oracle-tx BUNDLE.json` run the script to resolve the tag; the
  bundle wins if both are set. Other layers ignore the oracle.

### `--raw`

Shallow translation: little recovery, types, prelude naming, or polish.
Closer to UPLC (`Constr<N>`, `if_then_else`, `Constr.unpack`).
`--no-stub-adts` is redundant here — placeholders already stay.

### `--safe-mode`

Drops structural recovery, several polish stages, and some MIR
recoveries. Simplify and types still run. Default is also correct;
this is more literal when a recovery looks wrong.

### `--no-types`

No `: Type` on lets and helpers. Cardano field names
(`script_context.tx_info.signatories`) still appear — a `VarKind` pass
outside the type pipeline owns them. `TypePasses::all_off()` is the
library equivalent.

### `--no-optimize`

No β / single-use inline / dead-let / tail-chain collapse. Every `let`
the simplifier would have eaten survives. `SimplifyPasses::all_off()`.

---

## Script identity and wrap

### `--script-version <v1\|v2\|v3>`

Calling convention and TxInfo field schema.

Auto-detect: header `(1,1,_)` → V3; `(1,0,_)` is V1 or V2, refined by
V2/V3-only builtins, else **V2**. V1 vs V2 is the case to pin. The flag
is not checked against the builtin set (V1 + BLS will not warn).

V1/V2 spend: `datum, redeemer, ctx`. Other V1/V2: `redeemer, ctx`. V3:
one `ctx`; purpose lives in `script_info`.

### `--script-kind <auto\|validator\|plain>`

`auto` (default): V3 dispatch or lambda arity 1/2/3 →
`validator ... { ... }`, else `pub fn`. `plain` skips purpose diagnostics.

Purpose / split / `--applied-as` only apply to a validator wrap.

### `--purpose <spend\|mint\|withdraw\|certificate\|vote\|propose>`

Force one purpose. Needed when V1/V2 non-spend is mint vs withdraw vs
certificate, or V3 has no dispatch. Without it, that V1/V2 case is
`validator decompiled(redeemer, script_context)` plus a warning.

CLI refuses `--purpose` together with `--split-purposes always`. The
HTTP API accepts the pair and the explicit purpose wins (split dropped).

### `--split-purposes <auto\|always\|never>`

Requires the detector to see ≥2 purpose arms; the mode is what happens
after that. `auto` (default): split on V3 multi-purpose dispatch. V1/V2
multi-validator split is not implemented — `always` still flat-wraps
there and warns. `never`: one entry, even if dispatch was found.

### `--applied-as <compile\|auto\|runtime\|N>`

Outer `Apply` chain: compile-time params vs already-applied runtime
args (datum / redeemer / `script_context`).

| Value | Meaning |
| --- | --- |
| `compile` | CLI and web default. Every outer Apply is a compile-time param — deployed scripts. |
| `auto` | **Library** `DecompileOptions::default()`. Whole chain is runtime only when `applied + lambda_len == runtime_arity`; otherwise compile. |
| `runtime` | Last `runtime_arity_for(version, purpose)` Applies are runtime — evaluated debug snapshots. |
| `N` | Last N are runtime; the rest compile. `0` ≡ `compile`. |

When any outer Apply is labeled runtime, the decompiled header includes
an `// Info:` line with the count (all-runtime vs last-N split).

---

## Surface spelling

These only affect `--emit decompiled` (and the matching library
default). UPLC emit ignores them; raw-pseudo / post-pipeline print the
bare AST.

| Flag | Default | On |
| --- | --- | --- |
| `--no-stub-adts` | synthesize `pub type Unknown_S_<N>` | leave `Constr<tag>` (round-trips cleaner, not legal surface) |
| `--no-prelude-constructors` | name `True`/`Some`/`Void`/... | those become `Constr<N>`. Purpose anchors (`Spend`/`Mint`/...) stay named. Builtin `Pair(a,b)` is a different path and is untouched. |
| `--decode-church-to-native` | off | `fn(x) { x(a,b) }` → `Pair(a,b)`, church bools → `True`/`False` |
| `--expect-or-fail` | off | `when X is { P -> b; _ -> fail @"m" }` → `expect P = X or fail @"m"` (annotation; real `expect` has no `or fail`) |
| `--compilable-data-access` | off | `X.tag` / `List.head` / `xs[n]` → `builtin.un_constr_data` / `head_list` / nested `tail_list` |
| `--ordering-names` | off | three nullary arms → `Less`/`Equal`/`Greater`, only if `==`/`<` match those tags. Off because the shape also matches unrelated enums. |

---

## Library

```rust
use dehosk::{decompile, DecompileOptions, DecompileError, SimplifyPasses};

let text = decompile(hex, DecompileOptions::default())?;
let raw = decompile(hex, DecompileOptions::raw())?; // `--raw`
```

`ui_options()` / `GROUPS` / `curl .../api/options` are the field list.
Internal (no UI): `blueprint_hints`, `validator_meta`,
`use_varkind_recovery`, oracle inputs, `record_lineage_routes` — each
with a reason in the catalogue.

Group structs (`SimplifyPasses`, ...): `.all_on()` / `.all_off()`, or
flip leaves to bisect. `all_off()` is the user-facing group switch;
leaves are debug knobs. Shape-gated leaves do nothing on input that
lacks the pattern.

`opts.validate()?` before a custom leaf mix. Invalid combos are
`DecompileError::InvalidOptions`, not a mid-pipeline panic:

| Off | Must also turn off |
| --- | --- |
| `simplify_passes.simplify_fp_initial` | `inline_single_use` |
| `type_passes.solve_type_constraints` | `propagate_types` and `resolve_cardano_field_names` |
| `type_passes.propagate_types` | `resolve_cardano_field_names` |

Final type cleanup runs solve → propagate → Cardano names whenever
`type_passes.any_enabled()`. A partial `{ solve: true, propagate:
false }` validates and gates the **early** stage, then the cleanup
still runs all three. Use `TypePasses::all_off()` to actually drop
the type pipeline (`: Type` gone; Cardano names from `VarKind` remain).

`recover_let_bound_tag_dispatch` is a no-op seam (work moved to earlier
MIR passes). The toggle exists so tests can still name that pass id.

Other `DecompileError`s: `DecodeError` (bad hex/CBOR), `UnknownBuiltin`
(file a bug).
