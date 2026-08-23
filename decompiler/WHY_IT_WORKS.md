# Why it works

`ARCHITECTURE.md` says what lives where. This one answers a different question: **why is any of this possible at all?**

Every fragment is real output. The corpus is gitignored, so these are not reproducible from a published checkout. Conventions: deeply nested fragments are de-indented uniformly, `...` marks an elision, a `#` comment names the flag that produced a line, and a `|` column splits two runs shown side by side.

---

## 1. What compilation destroyed

| Was | Became |
| --- | --- |
| variable and function names | de Bruijn indices |
| types | nothing at all — UPLC is untyped |
| modules | one term |
| algebraic data types | lambdas, or a bare `constr` tag with a payload list |
| laziness | explicit `force` / `delay` |
| record fields | positions in a list, reached by `head`/`tail` chains |
| dead code, comments | removed |

Most of that is visible in the first ten lines of a real script:

```
(lam i_0
  (case
    (constr 0
      (force (builtin tailList))
      (force (builtin headList))
      (force (force (builtin sndPair)))
      (force (force (builtin fstPair)))
      (force (builtin ifThenElse))
    )
    (lam i_1
      (lam i_2
        (lam i_3
          (lam i_4
            (lam i_5
```

Names are `i_0`…`i_5`, no type appears, laziness is the explicit `force`. The `constr`/`case` pair is not data — it is a **builtin dictionary**, five primitives packed and destructured so the body can reach them positionally (§4.6).

None of that is recoverable by inverting a function: the mapping is not injective, and two different sources compile to the same term routinely.

## 2. Why recovery is nonetheless possible

> You are not inverting an arbitrary function. You are inverting **a compiler** — and a compiler is a systematic translator, not a creative one.

A code generator applies a fixed, small set of schemas, mechanically. Every schema leaves a fingerprint, and every fingerprint has an inverse. That moves the problem out of *program synthesis*, where it would be hopeless, into *pattern inversion under a known code generator* — ordinary engineering. Hence **69 small passes**, most knowing exactly one schema and how to undo it, the rest the supporting analyses (renaming, type solving, naming) the recognisers depend on.

Erasure removes *labels*, not *structure*. The shape survives intact, and the shape was produced by rules — so the labels can largely be re-derived from it. That is why type inference and Cardano-domain naming work as well as they do.

## 3. One script, four layers

One validator at every stage the pipeline exposes — 114 UPLC lines to 14. The layers are not a debugging afterthought; they are its actual staging (`--emit`).

**Layer 1 — UPLC as it lives on chain.** Past the dictionary, the bounds check at the centre:

```
(force
  (case
    (constr 0
      [(builtin lessThanInteger)
        (con integer
100)
        i_13]
      (delay (error))
      (delay
        (force
          (case
```

`case (constr 0 c a b) i_5`, where `i_5` is `ifThenElse`, is how a branch is spelled. Both arms are `delay`-wrapped so call-by-value does not run the untaken one. One arm is `(error)`.

**Layer 2 — raw pseudo:** control flow and binding structure recovered, idioms not yet inverted.

```
fn(v_0) {
  if_then_else(
    (
      let v_6 = Pair.second(Constr.unpack(v_0))
      let v_7 = v_6[1..]
      let v_8 = List.head(v_6[2..])
      let v_9 = List.head(v_6)
      if_then_else(
        1 == Pair.first(Constr.unpack(v_8)),
```

The dictionary is gone. What remains is compiler idiom: `Constr.unpack`, positional `[1..]` slices, `if_then_else` as a function rather than a branch, `delay`/`force` still visible.

**Layer 3 — post-pipeline:** idioms inverted, no domain knowledge applied.

```
fn decompiled(script_context) {
  let redeemer = script_context.redeemer
  expect Constr<1> = script_context.script_info
  let int = builtin.un_i_data(redeemer)
  expect int <= 100
  expect int >= 0
  int > 0
}
```

`Constr<1>` is a tag whose meaning is not yet known, there are no types, and it is a plain function rather than a validator. Everything to this point was derived from the term alone.

**Layer 4 — the finished read**, ledger schema applied:

```
// Info: V3 single-purpose: `spend` auto-detected from the script_info assertion on the entry spine.
validator decompiled {
  spend(script_context: ScriptContext) {
    let redeemer: Redeemer = script_context.redeemer
    expect Spending(_output_reference, _datum) = script_context.script_info
    let int: Int = builtin.un_i_data(redeemer)
    expect int <= 100
    expect int >= 0
    int > 0
  }
  else(_) {
    fail
  }
}
```

Note the polarity flip: UPLC tests `100 < v_13 -> fail`; the recovered form asserts the complement.

`--emit raw-pseudo` / `post-pipeline` stop the *pass* pipeline early, then still pretty-print. Pretty-print runs a slice of render-prep (shadow disambiguation), so those layers are a faithful AST view, not a photograph of the pass output. A few inversions live only between two passes and print nowhere — flagged below where it matters.

## 4. The recurring patterns

Every recogniser has three parts: **a shape** it matches, **a witness** that proves matching it *here* is safe, and **an inverse**. The witness does the real work — a shape match alone is a guess, and plenty of terms look like a Scott constructor without being one. Witnesses key on `VarId`, not on names, so shadowing cannot mint a false match. Pass order is a checked contract (`ARCHITECTURE.md`), not folklore.

Some inversions are **operationally faithful**. Others **restore the author's intent without being equivalent**; §4.3's church lists are the clearest case, and passes of that kind say so in their own source, because a reader who thinks the machine sees a list when it sees a closure will reason wrongly about cost.

### 4.1 Constructors and sums

**Data-tag `constr`** — the easy convention, because the tag is present. It is read off `unConstrData` + `fstPair`, never off UPLC's own `constr`:

```
[(builtin equalsInteger)
  (con integer
1)
  [i_5 [(builtin unConstrData) i_10]]]
```

Raw-pseudo renders it `1 == Pair.first(Constr.unpack(v_10))`. That assertion becomes `when x is { Constr<N> -> …; _ -> fail }`, then with a schema `expect Spending(…) = script_info`; without one, `m2_0.tag == 1`.

**If-chain of tag tests.** The same tag, tested as `if tag == 0 { … } else if tag == 1 { … } else { fail }`, is the Scott-less encoding of a sum. The inverse is a `when`. The dispatch spine in §4.7 is the domain instance; the same ladder appears on user ADTs.

**Scott encoding.** A constructor is a function taking one continuation per variant and calling its own; matching *is* applying:

```
(lam i_167
  (lam i_168 (delay (lam i_169 (lam i_170 [i_170 i_167 i_168]))))
)]
```

A cons cell. The **eliminator** side is the hard one: `v(k0, …, kN)` is indistinguishable by shape from any other call, so it lowers to a `when` only when the subject can be proven a Scott value of a specific type. Unproven stays raw — this is `isJust` on a Scott `Maybe`:

```
fn v_83(v_84) {
  v_84(fn(_) { True }, False)
}
```

**Church encoding.** Values are their own eliminators; a pair is destructured by *applying* it to a selector:

```
[(force i_19)
  (lam i_115
    (lam i_116 i_115)
  )]]]
...
[(force i_19)
  (lam i_117 (lam i_118 i_118))]]]
```

`λt.λf.t` renders `g.1st`; `λt.λf.f`, `g.2nd`. `(lam a (lam b a))` is also a boolean (§4.2) — position decides, not shape.

**`ChooseData` / `Data.case`.** Plutus V3's native case on a `Data` value is a builtin taking one handler per kind (Constr, Map, List, Int, ByteString, plus optional extensions). Shape: `chooseData(x, hConstr, hMap, …)`. Inverse: `when x is { Constr -> …; Map -> …; _ -> … }`. Repeated identity/sentinel handlers collapse to the wildcard. This is not Scott and not a user ADT — it is the runtime's own sum over `Data`.

**Stub ADTs.** When no blueprint type maps a constructor's `(parent_type, tag)`, the output would carry `Constr<N>`, which has no surface syntax; synthetic declarations are emitted at module top and the tags rewritten.

```
value == Constr<0>(#"00")            # --no-stub-adts
value == Unknown_E_1_0(#"00")        # default, plus:
pub type Unknown_E_1 { Unknown_E_1_0(Data) }
```

`Unknown_S_<ordinal>` groups by the scrutinee's canonical `VarId`; `Unknown_E_<arity>` is the expression-position fallback.

**Arity unification.** A stub constructor's field count is captured from whichever pattern is met first, often nullary. The real arity is whatever its widest destructuring site needs, so arity is unified across all sites rather than trusted from one:

```
expect Constr<0>(field_0, field_1) = x_31                              # --no-stub-adts
expect Constr<0>(field_0, field_1, field_2, field_3, field_4) = x_35
```

```
pub type Unknown_S_4 { Unknown_S_4_0(Data, Data, Data, Data, Data) }   # default
expect Unknown_S_4_0(field_0, field_1, _, _, _) = x_31
expect Unknown_S_4_0(field_0, field_1, field_2, field_3, field_4) = x_35
```

**Curry-split partial helpers.** The pack shape `fn(p_0, …, p_n) { p_n(p_0, …, p_{n-1}) }` arrives with a full signature but is almost always called at a consistent *partial* arity: the captured arguments are the payload, the remaining parameters the consumer interface. Splitting on the observed call arity recovers it. Witness: the continuation is the **last** parameter. If a middle one is invoked instead, residue stays — a schema whose witness did not fire:

```
// Scott-encoded tagged union: tag 1 of 3, fields (y_218, y_216).
// A matcher supplies 3 branch fns; this value invokes the 2nd.
fn(x_456, y_172, _, y_173, _) {
  y_173(x_456, y_172)
}(y_218,
  y_216)
```

**Constr-encoded list cons.** `Constr<1>(head, tail)` terminating in `Constr<0>` is a data-encoded list. An inline chain folds to `[a, b, c]`. When CSE hoists the tail to a `let`, the fold must not treat an unrelated arity-2 `Constr<0>` (a pair) as nil: only tag-1 arity-2 whose second field **provably** resolves to a list (`VarId` chase to a `List`, nil, or cons) becomes `[head, ..tail]`.

### 4.2 Booleans and Option

**CPS selectors.** `True` is `fn(x, _) { x }`, `False` is `fn(_, y) { y }` — a boolean *is* the choice it makes:

```
(delay (lam i_1295 (lam i_1296 i_1295)))
(delay (lam i_1297 (lam i_1298 i_1298)))]
```

```
fn church_true(t, _) {
  t
}
fn church_false(_, f) {
  f
}
```

Call sites over-apply them: `fn_3(x, y)(delay(a), delay(b))`. The witness is a call carrying **at least two `delay`-wrapped arguments**, because wrapping both arms is exactly how call-by-value UPLC stops the untaken one running. Nothing but a branch needs that. Closed church-bools can be *proven* on the CEK machine (reduce to a sentinel); that is a proof, not a heuristic.

**Polarity.** Most scripts use the CIP ABI (`True = Constr<1>`); a minority invert it. Getting this wrong crashes nothing — it silently swaps every two-arm boolean collapse, and the output reads perfectly while meaning the opposite. Two independent signals must agree: an inverse producer (`if c { Constr<0> } else { Constr<1> }`) and a tag-0 success oracle (§4.5). A tag-1 success oracle vetoes inverse-CIP. Ambiguity keeps the default. Signal (1) in the wild:

```
(lam i_406
  [(force (builtin ifThenElse))
    [(builtin equalsByteString) i_405 i_406]
    (constr 0)
    (constr 1)]
)
```

A related trap: simplify may collapse a *terminal* church-bool `when` with CIP polarity, then fold `if c { True } else { … }` to `!c || …`, inverting an inverse-CIP script. The witness is `church_false` (nullary `Constr<1>` behind a trace) sitting on the short-circuit RHS of `||` under a negated condition — church_false belongs on the cond-FALSE path. Inverse: drop the `!`.

**`if` to logical operator.** `if c { body } else { False }` becomes `c && body`; `if c { True } else { body }` becomes `c || body`. Exact short-circuit equivalences — but well-typed **only when `body: Bool`**, and the sibling branch being a `Bool` literal does not establish that.

```
if_then_else(
  v_13 < 10,
  v_13 == 7,
  False
)()
```

```
let f_int: Int = builtin.un_i_data(redeemer)
f_int < 10 && f_int == 7
```

**Bool as `Constr`.** After types prove `x: Bool`, `when x is { Constr<1> -> T; _ -> E }` is `if x { T } else { E }`. Before that proof it is a sum, and collapsing it would swap meaning under inverse-CIP.

**The `None`/`False` collision.** Both encode as a nullary `Constr _ []`, and under reversed ordering both take tag 0, so a decoder can turn `Option::None` into a `Bool(false)` literal. The error surfaces only later, when the value is matched as an `Option` and the output is type-incoherent. Re-labelling it requires a witness that the value really is an option. Here `Constr<1>` is a value and `None` a pattern, for identical shapes:

```
None ->
  when v_42 is {
    Some(_) -> Constr<1>
    None -> Constr<0>
  }
```

**Option in CPS.** PlutusTx Option is often a function of three continuations: some-payload, none, fail. Shape: `opt(kSome, kNone, fail)` with the last arm `fail` and the callee proven Option-like. Inverse: `when opt is { Some(x) -> kSome(x); None -> kNone }`. Without the Option witness this is just a call.

**V1/V2 success sentinel.** Those ABIs return `Bool`; V3 returns `Unit` and fails with `fail`. Compilers still emit tail-position `()` as “this branch succeeded”. Witness: `script_version` is V1/V2 and the node is tail in the validator-entry lambda. Inverse: `Void` → `True` in that position only — argument and nested-closure `Void` stay.

### 4.3 Lists

**Builtin `mkCons` chains.** `[a, b, c]` as nested `cons` of `iData` etc. folds to a list literal — operationally faithful:

```
[i_3                            ->    let list_partial =
  [(builtin iData) i_13]                [
  [i_3                                    builtin.i_data(redeemer_int),
    [(builtin iData)                      builtin.i_data(redeemer_int + 1),
      [(builtin addInteger)               builtin.i_data(redeemer_int + 2)
        i_13                            ]
        (con integer
1)]]
```

**Church list literals — the readability-only inversion.** `[a, b, c]` also lowers to `cons(a, cons(b, cons(c, nil)))` where `cons` is `fn(h, t, _, k) { k(h, t) }`, a church-pair pack with the nil arm dead:

```
(lam i_432 (lam i_433 (delay (lam i_434 [i_434 i_432 i_433]))))
(lam i_435 i_435)]
```

```
fn church_cons(x_98, y_26) {
  fn(_, y_27) { y_27(x_98, y_26) }
}
```

Witness: the helper's body matches the canonical shape and the chain is at least two deep. The value **is** a closure carrying head and tail, applied by consumers as `value(nil_arm, cons_arm)`. Rendering it as `[a, b, c]` reconstructs what the author wrote and buys readability at the cost of operational fidelity, deliberately. Unrecovered chains stay `church_cons(…)`.

**`chooseList`.** Logically three arguments. Direct, it is a `when` on `[]` / `[head, ..tail]`:

```
(force
  [(force (force (builtin chooseList)))
    i_380
    (delay i_378)
    (delay
      [i_379
        [(force (builtin headList)) i_380]
        [(force (builtin tailList)) i_380]]
    )]
```

```
fn helper_3(x_4, y_3, z: List<Data>) {
  when z is {
    [] -> x_4
    [head, ..tail] -> y_3(head, tail)
  }
}
```

Church-list builders apply the result to an identity continuation — a fourth argument. The three-argument MIR recogniser never fires, so these survive as raw `List.fold` that **read as fold computations when they are structural pattern matches**. Witness for the late inverse: the fourth argument is identity (`fn(x) { x }` or a `VarId` proven to be one). Then `List.fold(xs, nil, cons, id)` becomes `when xs is { [] -> nil; [_, ..] -> cons_body }`. If the *third* argument is a named helper rather than a lambda, the witness fails and residue stays — better than guessing.

Once that `when` is native, a rec-fn of the shape `[] -> []; [_, ..] -> [F(head), ..self(tail)]` is `list.map`. Same fingerprint, one level up.

**Church bytestring.** Two rec-helpers: map each byte to a 1-byte string and church-cons (`o5`), then fold with `<>` (`s5`). `s5(o5([180, 198, …]))` over a literal int list is a compile-time constant (typically a script hash). Inverse: `#"b4c6…"`. Witness: both helpers match the canonical bodies and the argument is a closed int list — not a runtime fold.

**Positional slices.** `head`/`tail` chains, rendered as `xs[1..]`-style slices before anything can be named.

### 4.4 Recursion

**Fixpoint combinators.** There is no recursion primitive; recursion arrives as a Z- or Y-style combinator applied to a self-passing lambda, and is unfolded back into a named recursive function.

```
(lam i_202
  [(lam i_203 [i_203 i_203])
    (lam i_204 [i_202 (lam i_205 [i_204 i_204 i_205])])]
)]
```

`Z = λf. (λx. x x) (λx. f (λv. x x v))`, verbatim. Applied to a three-argument self-passing lambda:

```
[i_0
  (lam i_151
    (lam i_152
      (lam i_153
        (force
          (force
            [(force (builtin ifThenElse))
              [(builtin equalsInteger) (con integer
0) i_153]
              (delay (delay i_152))
              (delay
                (delay
                  [i_151 i_153 [(builtin modInteger) i_152 i_153]]
```

```
rec fn b(y_7: Int, z_2: Int) {
  if z_2 == 0 {
    y_7
  } else {
    b(z_2, y_7 % z_2)
  }
}
```

A gcd loop; `i_151` is the self-reference and `b` is synthesised.

**Mutual recursion.** Two functions packed into a church pair and projected out — a U-combinator fixpoint with a knot binding, two injections, and a driver applied to the pair literal:

```
[(lam i_74
  [i_73
    (lam i_75
      [i_74 (lam i_76 (lam i_77 [i_76 i_75]))]
    )
    (lam i_78
      [i_74 (lam i_79 (lam i_80 [i_80 i_78]))]
    )]
)
  (lam i_81
    [(force [i_71 i_71 i_72]) [(force i_72) i_81]]
  )]
```

```
rec fn check_param_value(x_15, y_12) {
  rec fn check_param_list(x_32, values: List<Data>) {
    when x_32 is {
      [] ->
        if List.is_empty(values) {
          True
        } else {
          False
        }
      [v_71, ..v_72] ->
        check_param_value(v_71, values.head) && check_param_list(v_72,
          values[1..])
```

Two traps. The **arities are fabricated in flight**: the UPLC eliminates a 2-variant sum of true arities 0 and 2, then over-applies the result, so lowering absorbs the trailing argument as a binder per clause. At raw-pseudo the arms arrive as arity 1 and 3 — `Constr<0>(v_70)`, `Constr<1>(v_71, v_72, v_73)` — and the pass redistributes it back into the bodies, giving the true `[]` and `[v_71, ..v_72]` with the absorbed value promoted to `values: List<Data>`. That both `v_70` and `v_73` become `values` is the witness they were one value. Second, branch **polarity is preserved literally**, never tidied — tidying a branch order is precisely how a decompiler inverts meaning while looking like an improvement.

**Redundant inner recursion.** When a recursive function's body is itself a recursive function that never references its own name, the inner `rec` is noise and becomes a plain lambda.

### 4.5 Idioms that survive erasure

Places where the compiler preserved a fact about **intent**, not merely about behaviour.

**`expect` and the success oracle.** `expect P = X` desugars to `when X is { P -> continue; _ -> fail }`, and the failing arm survives. So a `when` with exactly one failing arm is evidence about which branch the *author* considered success — the polarity classifier's second signal. At its cleanest the compiler embedded the author's own source line as the label:

```
(delay
  (force
    [i_8
      (con
        string
"expect [input, ..] = inputs"
      )
      (delay
        (error)
      )]
```

```
expect [input, .._tail] = inputs_list                                          # default
expect [input, .._tail] = inputs_list or fail @"expect [input, ..] = inputs"   # --expect-or-fail
```

The message is incidental; the structural form is the oracle, and §3's silent `(delay (error))` serves equally.

**Three-way comparators.** A comparator's producer branches become a native `Ordering` only when **both** ends agree: the branch tags match the `Ordering` ABI exactly, *and* a consumer reads the result as a clean 3-way dispatch. Opt-in via `--ordering-names`, because `{(0,0),(1,0),(2,0)}` also matches any three-nullary-variant enum:

```
when variant_2 is {          ->   when variant_2 is {
  Unknown_S_2_0 -> ...              Less -> ...
  Unknown_S_2_1 -> ...              Equal -> ...
  Unknown_S_2_2 -> ...              Greater -> ...
```

Those arms select which of eight fields to project — a dispatch key. Whether they mean `Less`/`Equal`/`Greater` is what the term cannot say.

**Trace instrumentation.** PlutusTx wraps calls in a trace pair: `trace("entering fooBar", fn(_) { trace("exiting fooBar", body, _) }, _)`. Pure scaffolding — but deleting a call that might have effects must not be done on resemblance alone, so it is gated four ways: the curried 3-argument form (the 2-argument `trace` cannot match), the `"entering "` prefix that only this compiler emits, a single ignored parameter **whose `VarId` the body never free-references** — which is what makes dropping the third argument sound — and that third argument being exactly `Void` rather than any expression that might do something. The inner `exiting` trace is removed only when its identifier matches the outer `entering` one.

Ordinary `trace("PT1", delay(error))` is not that gate; it collapses to `fail @"PT1"`. Where the payload is a value the message is kept — the surface has `trace` too — and only the plumbing goes.

### 4.6 Call-shape noise

Artefacts that hide the schemas that have meaning.

**The builtin dictionary** (§1) is gone by raw-pseudo, and no pass is named for it. Where it dissolves is not attributable from the pass trace: on the fixture shown neither general resolver that could claim it emits at all — the immediately-applied-lambda one fires on none of the 23 fixtures, the `case`-over-`constr` one on a single fixture that is not this one. A schema that falls out of general rules needs no special case, and special cases are where decompilers rot.

**Force/delay residue.** Most surviving thunks only preserve evaluation order:

```
if_then_else(
  100 < v_13,
  fail,
  delay(force(if_then_else(
    v_13 < 0,
    fail,
    0 < v_13
  )))
)()
```

is, after the late cancels, `expect int <= 100` / `expect int >= 0` / `int > 0`.

**Eta expansion.** A lambda layer that changes nothing: `(lam i_192 [i_1 i_192])`, where `i_1` is `headList`. Raw-pseudo shows `fn v_17(v_18) { List.head(v_18) }`; by post-pipeline it and its call sites are gone, `v_17(Pair.second(Constr.unpack(v_191)))` having become `head.fields[0]`.

**Forced nullary constr.** A delayed constructor surfaces as `c1(Void)` — apply-to-unit to force the thunk. Same value as bare `c1`. Witness: the callee's `VarId` binds a nullary `Constr`. Inverse: drop the `(Void)`.

**Double unwraps.** A compile-time-applied parameter surfaces as a literal with the program's own `un_i_data`/`un_b_data` on top; `builtin.un_b_data(#"ab")` folds to `#"ab"`. The intermediate term prints nowhere, living only between beta-substitution and the fold. The two ends do:

```
fn(v_11) {
  let v_12 = builtin.un_b_data(v_11)
...
}(#"000102030405060708090a0b0c0d0e0f101112131415161718191a1b",
```

```
const x_3_bytes: ByteArray = #"000102030405060708090a0b0c0d0e0f101112131415161718191a1b"
```

**CSE over alpha-equivalent helpers.** Two let-bound helpers differing only in binder names are folded — but only for pure, value-shaped expressions. `Apply` and effectful nodes are excluded, because dropping a duplicate there removes an evaluation point. Helpers that capture different outer `VarId`s are not alpha-equivalent and stay apart.

### 4.7 Domain knowledge

Everything above is derived from the term alone. Naming needs an outside source.

**Fields.** A record field is a position reached by a `head`/`tail` chain; nothing in the term names it:

```
[(builtin unMapData)
  [i_2
    [i_1
      [i_1
        [i_1
...
                          [i_1
                            [i_4
                              [(builtin
                                unConstrData
                              )
                                [i_2
                                  i_7]]]]]]]]]]]]]]]]]]
```

Twelve tail steps and a head; nothing says `votes`. The same term against two schemas:

```
let field_0 = x.fields[0]                       |  let tx_info: TxInfo = script_context.tx_info
expect Unknown_S_1_1 = field_2                  |  expect Spending(_output_reference, _datum) = script_info
expect any(builtin.un_map_data(                 |  expect any(builtin.un_map_data(tx_info.votes))
  field_0.fields[12]))                          |
```

Names come from the ledger schema for the script version, or from a blueprint. Blueprint constructor names are arbitrary user-chosen strings rather than members of a closed known set, and the code keeps the two sources distinct — conflating them would let any string masquerade as domain knowledge.

**The dispatch spine.** A multi-purpose validator opens with a `when` over `script_info`, one arm per purpose, revealing which purposes exist and where each handler begins. In UPLC, a chain of tag tests:

```
[(builtin equalsInteger)
  (con integer
0)
  i_9]
...
[(builtin equalsInteger)
  (con integer
1)
  i_9]
...
(delay (error))
```

```
  when script_info is {              |  validator decompiled {
    Constr<0> -> ... == 42           |    mint(script_context: ScriptContext) {
    Constr<1> ->                     |      expect Minting(_policy_id) = script_info
      let f_int = ...                |      builtin.un_i_data(redeemer) == 42
      f_int > 0 && f_int < 100       |    }
    _ -> fail                        |    spend(script_context: ScriptContext) {
```

The trailing `_ -> fail` is the `(delay (error))` above — the same success oracle. Resolution order is explicit: blueprint metadata, then an explicit `--purpose`, then detected dispatch, then a flat rendering — with a warning, not a guess, for the ambiguous cases:

```
// Warning: V1/V2 non-spend purpose is ambiguous from bytecode; pass --purpose to specify (mint|withdraw|certificate)
```

**Version inference, and what a signal can prove.** Builtin presence proves a **lower bound** on the required protocol version. Absence proves **nothing**: a V3 script using no V3-only builtin is indistinguishable from a V1 script by that scan. The classifier is written to that asymmetry rather than the convenient reading of it:

```
// Info: Plutus version assumed V2: the (1, 0) UPLC header is shared by V1 and V2 and no V2-only builtins were found. Pass --script-version v1|v2 to pin it (affects context field naming).
```

## 5. How it stays honest

Readable output is easy to like and hard to check: a wrong rewrite often looks like an improvement.

A **name or type** can follow the solver — a bad label is visible. A rewrite that **changes meaning** is held to a witness in the term. Classification prefers the status quo when the signals disagree (§4.2's polarity is the example), so an unrecognised script is not made worse than before the classifier existed.

Witnesses have a direction. One counterexample is enough to *block* a rewrite; asserting one needs agreement at every site. Using an existential match as a universal proof is a common way a pass goes quietly wrong.

The rest is ordinary test hygiene, taken seriously because the output lies so well: pinned corpus hashes so a shared pass cannot drift unnoticed; guards that fail if they found nothing to check; parallel decompiles compared for determinism, and a second run for idempotence. Causes are measured against the defect they claim to explain — some plausible ones explained none, and were dropped.

## 6. Reading the output safely

The output is **pseudocode meant for reading**, not a source file that is guaranteed to compile. Non-source notation (`xs[1..]`, `Constr.unpack`, `.tag`) is deliberate when it reads better than a faithful spelling.

- `// Info:` and `// Warning:` are part of the output contract — judgement calls (auto-detected purpose, unresolved ambiguity). Read them first when the output looks surprising.
- Un-inverted residue is left visible: a five-parameter lambda applied to two arguments, a four-argument `List.fold`, a bare `church_cons` chain. Each is a schema whose witness did not fire. That is safer than a confident guess.
