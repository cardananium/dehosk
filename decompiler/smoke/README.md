# Smoke fixtures

The two programs the non-corpus tests decompile, and the sources they are
compiled from. Both were written for this repository. Neither is a
deployed contract, and neither should ever be replaced with bytes lifted
off the chain — real scripts belong in the shadow corpus under `dev/`,
which is not distributed with the source.

| source | constant | version | size |
| --- | --- | --- | --- |
| `vault_v2.uplc` | `MIR_V2_SMOKE_HEX` | Plutus Core 1.0.0 (PlutusV2) | 364 bytes |
| `vault_v3/validators/vault.ak` | `MIR_V3_SMOKE_HEX` | Plutus Core 1.1.0 (PlutusV3) | 743 bytes |

Both constants live in `src/decompile/tests/mod.rs`.

## What the programs do

The same toy vault, written twice. A datum carries an `owner` byte
string and an integer `total`; a redeemer picks one of three actions:

- `Transfer { amount, recipient }` — the amount must be positive, a tenth
  of it must fit in the budget, and the recipient must not be the owner's
  label (`owner ++ "VAULT"`);
- `Extend { extra, witnesses }` — the extra must be positive and the
  witness list must fold to a byte string that starts with the owner;
- `Close` — the amounts must sum to the recorded total.

Between them they exercise constructor dispatch, `Data` destructuring,
three self-recursive list folds (`Int`, `ByteArray`, count), record field
access and a handful of byte-string builtins, so the pipeline has enough
shape to be worth measuring. The V3 program additionally declares two
handlers (`spend` and `mint`), which is what drives the purpose dispatch
and the ScriptContext naming.

## Regenerating

`vault_v2.uplc` is textual UPLC and is turned into the constant by
parsing it, converting to de Bruijn indices and CBOR-encoding the result
— exactly what `mir_v2_smoke_hex_matches_its_checked_in_source` in
`src/decompile/tests/basic.rs` does on every run, so the constant cannot
drift away from the source without a test failure.

`vault_v3` is an Aiken project with no dependencies; `aiken build` inside
it writes `plutus.json`, whose `compiledCode` is the constant:

```sh
cd decompiler/smoke/vault_v3 && aiken build
python3 -c "import json;print(json.load(open('plutus.json'))['validators'][0]['compiledCode'])"
```

The three blueprint entries (`spend`, `mint`, `else`) share one
`compiledCode`: it is the whole multi-handler validator.
