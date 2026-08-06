import Blanc.WethLive

namespace Blanc

open Jaune

set_option maxRecDepth 8000

/-! # What WETH's `balanceOf(address)` call *costs*

`Blanc/WethLive.lean` proves that the call succeeds and what it returns, but
never states its gas as a *conjunct* of the run: the post-state's `gasLeft` is
pinned inside the construction (`G := g - 2241`) and never surfaces in either
`weth_balanceOf_runCompiled` or `weth_balanceOf_succeeds`. This module supplies
the theorem that says what the call costs, at two altitudes: `exec` (the
executed frame's gas is exactly `balanceOfGas`) and `Prog.RunCompiled`-in-
hypothesis (the shape a caller reasoning about an arbitrary run of this
contract states over).

**Message-call altitude, one entrypoint, one contract, one fixed selector,
exact under `Blanc/Compiled.lean`'s compiler-shape assumption** — the same four
limits `Blanc/FmintLive.lean:103-119` states for `fmint_totalSupply_succeeds`,
carried over unchanged; read that theorem's docstring for what a statement of
this shape does and does not claim.

**The schedule limit.** `balanceOfGas` is written in Jaune's gas *symbols*
(`gJumpdest`, `gBase`, `gVerylow`, `gHigh`, `gMemory`, `gasColdSload`) and never
in numerals — a repricing of any of those constants changes the number, not the
statement. But the *theorem* below is not schedule-parametric and cannot be
made so in this arc: `Jaune.Fork.ForkRules` (`Jaune/Fork.lean:161`) carries
`fork`, `blob`, `code`, `tx`, `block`, `modexp`, `op` and `precompiles` — no
opcode gas schedule. Every constant this module sums is a global `def` in
`Jaune/Machine.lean:500-537`, threaded nowhere through `ForkRules`. A
`ForkRules` argument here would be an unused parameter, which is exactly the
fake-parameter shape this arc's plan (`~/plans/gas-cost.md`, correction C1)
prohibits. `func_run`'s own `gasTacs` unfolds these symbols to numerals before
calling `omega`, so a repricing changes the *proof term* even though it does
not change the *statement* — never claim more than that. -/

/-- `Devm.gasLeft` through `Devm.withOutput`: the update touches `meta` only,
so the gas account is untouched.  Kept generic (over an arbitrary `devm`) so
that using it never forces the state it is applied to — the 22-step
construction below — to reduce. -/
lemma Devm.gasLeft_withOutput {devm : Devm} {out : Bytes} :
    (devm.withOutput out).gasLeft = devm.gasLeft := rfl

/-- `Devm.gasLeft` through the second projection of `Devm.memRead`: the read
only ever updates `memory`, so the gas account survives it.  The same shallow,
generic argument as `Devm.gasLeft_withOutput`. -/
lemma Devm.gasLeft_memRead_snd {devm : Devm} {i sz : Nat} :
    (devm.memRead i sz).2.gasLeft = devm.gasLeft := rfl

/-! ## A second entrypoint: `decimals()`

`balanceOf(address)` is the *expensive* end of the view genre — a storage read
dominates it, 2100 of its 2241. `decimals()` is the cheap end: it pushes a
constant, writes it to memory and returns it. No `SLOAD`, no calldata read, so
no cold-key premise and no quantification over an argument word.

It is chosen because it exercises **no instruction the walk has not already
run**, which makes it a clean measurement of what a second target in a known
genre costs (arc plan `~/plans/gas-cost.md`, gate G2). What differs is the
*path*: `decimals()` sits at index 5 of `wethFuncs`' ten, where `balanceOf()`
sits at index 6, so the two take different arms through the same four forks. -/

/-- The selector `decimals()` dispatches on. Local to this module for the
reason `Blanc/WethLive.lean` records for `boSel`: the tree carries no selector
abbreviations, and importing a module to reach a four-byte constant costs
seconds of elaboration. -/
abbrev dcSel : B256 := selector "decimals" []

/-- Every gas constant the `decimals()` derivation charges, in the order it
charges them: the program's entry `JUMPDEST`; `fsig`'s four instructions; four
dispatch forks, the first falling through and the last three taken by the
`.succ` arm; the leaf's `PUSH`/`EQ` and its taken arm; then `decimals`' own
body — one `PUSH1 0x12`, `mstoreAt 0`, and `returnMemoryRange 0 32`.

The fork *count* is `balanceOfGas`'s; the fork *arms* are not. `decimals()` is
entry 5 of ten and `balanceOf()` entry 6, and `DispatchTree.build` splits at
`⌈n/2⌉`, so the two paths agree only on the first fork: they part at the last,
where `balanceOf()` falls through and `decimals()` jumps. That one extra taken
arm is one extra `gJumpdest`, which is why this and `Blanc.Fmint.decimalsGas`
— the same `Func`, compiled from the same `Blanc.decimals` — differ by 1.

Below the dispatcher the whole difference from `balanceOfGas` is the body:
`gVerylow` for the constant push, where `balanceOf` pays `gVerylow + gVerylow +
gasColdSload` to fetch a slot. -/
def decimalsGas : Nat :=
  gJumpdest
    + (gBase + gVerylow + gVerylow + gVerylow)
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + gVerylow
    + (gBase + (gVerylow + gMemory))
    + (gVerylow + gBase)

/-- 139 gas, of which 123 is the dispatcher and 16 the body. Sixteen times
cheaper than `balanceOfGas`, and the ratio is the storage read. -/
theorem decimalsGas_eq : decimalsGas = 139 := by decide

/-- A `decimals()` call on `weth` has a gas-exact run; it costs exactly
`decimalsGas` and returns `0x12`.

Unlike `weth_balanceOf_runCompiled` this states the **gas as a conjunct of the
run**, which is what `Blanc/WethGas.lean` exists to supply and what the
predecessor's two witnesses left inside their constructions. Stating it here
rather than re-deriving the witness in a separate theorem is deliberate: the
re-derivation Step 1 of `~/plans/gas-cost.md` had to perform, because
`weth_balanceOf_runCompiled`'s existential does not expose which witness it
built, pays this module's dispatch keccak cost a second time. A target whose
walk is written *inside* this module pays it once. -/
theorem weth_decimals_runCompiled {sevm : Sevm} {pre : Devm}
    (h_sel : Sevm.selector sevm = dcSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : decimalsGas ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiled sevm pre weth post ∧
      post.gasLeft + decimalsGas = pre.gasLeft ∧
      Devm.output post = (0x12 : B256).toBytes := by
  rw [decimalsGas_eq] at h_gas
  set g := pre.gasLeft with hg
  refine
    ⟨_,
      Prog.runCompiled_intro (G := g - 1)
        (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
        (by simp only [gJumpdest]; omega)
        (by rw [h_stack, h_mem])
        (by
          func_run [dcSel, 0, 1, 1, 1, 1, 3]
          · exact Devm.extCost_empty_word
          · exact Func.runCompiled_ret_word (G := g - 139) (e := 0) rfl
              (Devm.extCost_word_word Mem.size_write_word)
              (by simp only [Devm.gasLeft_setMach]; omega)
              (Devm.memRead_word_fst (by simp only [Devm.memory_setMach]; rfl))),
      ?_, rfl⟩
  simp only [Devm.gasLeft_withOutput, Devm.gasLeft_memRead_snd, Devm.gasLeft_setMach,
    decimalsGas_eq]
  omega

/-- **`weth`'s `decimals()` call costs exactly `decimalsGas`.**

The exec-altitude exactness theorem, at the shape
`weth_balanceOf_gas_exact` states. No re-derivation is needed here: the walk
above already carries the gas conjunct, so this is `Prog.exec_of_runCompiled`
applied to it.

Same four limits as `weth_balanceOf_succeeds` — one entrypoint of one contract,
message-call altitude, one fixed selector, exact under `Blanc/Compiled.lean`'s
compiler-shape assumption — plus this module's schedule limit. -/
theorem weth_decimals_gas_exact {sevm : Sevm} {pre : Devm}
    (h_code : some sevm.code.toList = Prog.compile weth)
    (h_sel : Sevm.selector sevm = dcSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : decimalsGas ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      post.gasLeft + decimalsGas = pre.gasLeft ∧
      Devm.output post = (0x12 : B256).toBytes := by
  obtain ⟨post, h_run, h_gas_eq, h_out⟩ :=
    weth_decimals_runCompiled h_sel h_stack h_mem h_gas
  exact ⟨post, Prog.exec_of_runCompiled h_run h_code, h_gas_eq, h_out⟩

/-- **`weth`'s `decimals()` call succeeds**, and returns `0x12`.

The `weth_balanceOf_succeeds`-shaped statement for this target: the gas
conjunct dropped, so that a caller who only wants liveness and the return value
does not have to carry the cost equation. -/
theorem weth_decimals_succeeds {sevm : Sevm} {pre : Devm}
    (h_code : some sevm.code.toList = Prog.compile weth)
    (h_sel : Sevm.selector sevm = dcSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : decimalsGas ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      Devm.output post = (0x12 : B256).toBytes := by
  obtain ⟨post, h_exec, _, h_out⟩ :=
    weth_decimals_gas_exact h_code h_sel h_stack h_mem h_gas
  exact ⟨post, h_exec, h_out⟩

/-- **`weth`'s `decimals()` call costs exactly `decimalsGas`, from an arbitrary
`Prog.RunCompiled` witness.**

By determinism, exactly as `weth_balanceOf_gas_of_runCompiled`; see that
theorem's docstring for why this is not an inversion. -/
theorem weth_decimals_gas_of_runCompiled {sevm : Sevm} {pre post : Devm}
    (h_code : some sevm.code.toList = Prog.compile weth)
    (h_sel : Sevm.selector sevm = dcSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : decimalsGas ≤ pre.gasLeft)
    (h_run : Prog.RunCompiled sevm pre weth post) :
    pre.gasLeft = post.gasLeft + decimalsGas := by
  obtain ⟨post', h_exec', h_gas_eq, _⟩ :=
    weth_decimals_gas_exact h_code h_sel h_stack h_mem h_gas
  have h_exec : exec ⟨0, sevm, pre⟩ = .ok post :=
    Prog.exec_of_runCompiled h_run h_code
  rw [h_exec] at h_exec'
  injection h_exec' with h_eq
  subst h_eq
  omega

/-- **`weth`'s `balanceOf(address)` call costs exactly `balanceOfGas`.**

The exactness theorem at the `exec` altitude. `exec` is a *function*, so its
post-state is unique; the proof re-derives `weth_balanceOf_runCompiled`'s
witness rather than reusing that theorem's existential, because the existential
does not expose which witness it constructed. The re-derivation calls
`func_run` exactly once — the same walk, not a new one — and the extra conjunct
falls out of a projection through the construction: `Func.runCompiled_ret_word`
ends in `(_.memRead i sz).2.withOutput out`, `Devm.memRead` is
`⟨val, devm.withMemory mem⟩`, and neither `withMemory` nor `withOutput` touches
the `mach.gasLeft` field they leave untouched, so the post-state's `gasLeft` is
`pre.gasLeft - 2241` **by `rfl`**, without forcing the memory write to reduce.

Same four limits as `weth_balanceOf_succeeds`; see that theorem's docstring. -/
theorem weth_balanceOf_gas_exact {sevm : Sevm} {pre : Devm}
    (h_code : some sevm.code.toList = Prog.compile weth)
    (h_sel : Sevm.selector sevm = boSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, Sevm.dataWord sevm 4⟩ : Adr × B256)
      ∉ pre.accessedStorageKeys)
    (h_gas : balanceOfGas ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      post.gasLeft + balanceOfGas = pre.gasLeft ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget (Sevm.dataWord sevm 4)).toBytes := by
  rw [balanceOfGas_eq] at h_gas
  set g := pre.gasLeft with hg
  refine
    ⟨_,
      Prog.exec_of_runCompiled
        (Prog.runCompiled_intro (G := g - 1)
          (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
          (by simp only [gJumpdest]; omega)
          (by rw [h_stack, h_mem])
          (by
            func_run [boSel, 0, 1, 1, 0, 1, 3]
            · exact Devm.extCost_empty_word
            · exact Func.runCompiled_ret_word (G := g - 2241) (e := 0) rfl
                (Devm.extCost_word_word Mem.size_write_word)
                (by simp only [Devm.gasLeft_setMach]; omega)
                (Devm.memRead_word_fst (by simp only [Devm.memory_setMach]; rfl))))
        h_code,
      ?_, rfl⟩
  simp only [Devm.gasLeft_withOutput, Devm.gasLeft_memRead_snd, Devm.gasLeft_setMach,
    balanceOfGas_eq]
  omega

/-- **`weth`'s `balanceOf(address)` call costs exactly `balanceOfGas`, from an
arbitrary `Prog.RunCompiled` witness.**

The shape `~/plans/gas-cost-proposal.md` names: the run sits in *hypothesis*
position rather than being constructed. Not by inversion — there is no
`Func.RunCompiled` inversion walk in this repository, and building one is out
of this arc's budget (correction C2) — but by **determinism**: `exec` is a
function, so `weth_balanceOf_gas_exact`'s constructed post-state and this
theorem's hypothesised one both come from `exec ⟨0, sevm, pre⟩`, hence are
equal, and the gas equation transports across `injection`. -/
theorem weth_balanceOf_gas_of_runCompiled {sevm : Sevm} {pre post : Devm}
    (h_code : some sevm.code.toList = Prog.compile weth)
    (h_sel : Sevm.selector sevm = boSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, Sevm.dataWord sevm 4⟩ : Adr × B256)
      ∉ pre.accessedStorageKeys)
    (h_gas : balanceOfGas ≤ pre.gasLeft)
    (h_run : Prog.RunCompiled sevm pre weth post) :
    pre.gasLeft = post.gasLeft + balanceOfGas := by
  obtain ⟨post', h_exec', h_gas_eq, _⟩ :=
    weth_balanceOf_gas_exact h_code h_sel h_stack h_mem h_cold h_gas
  have h_exec : exec ⟨0, sevm, pre⟩ = .ok post :=
    Prog.exec_of_runCompiled h_run h_code
  rw [h_exec] at h_exec'
  injection h_exec' with h_eq
  subst h_eq
  omega

/-! ## Dropping the coldness assumption

Every statement above assumes the storage key `balanceOf(address)` reads is
**cold**. That is the expensive case, and it is the one a fresh top-level frame
is in — but it is an assumption about the caller's *state*, not about the call,
and a statement that only holds under it cannot answer "what does this cost?"
without a footnote.

This section removes it. The warm case is a **separate walk against a separate
forward lemma pair** (`Rinst.runCore_sload_warm_eq_ok`,
`Ninst.runCompiled_sload_warm`), not the cold one with a parameter: the two
charge different constants *and* end in different accessed-key sets, so one
statement covering both would carry an `if` into every gas equation between the
`SLOAD` and the `RETURN`. `Rinst.runCore_sload_cold_eq_ok`'s docstring recorded
that refusal before this arc existed and this arc keeps it.

**The `if` goes exactly one level up, into the cost function** — `wethGas`
below — where it is written once and eliminated once, by `by_cases` in
`weth_balanceOf_gas_exact_wethGas`. That theorem is the point of the section:
it prices `balanceOf(address)` with **no coldness premise at all**. -/

/-- `balanceOfGas` with the storage read warm: the same path, the same charges
in the same order, `gasWarmAccess` where the cold derivation pays
`gasColdSload`. Nothing else moves — a warm `SLOAD` is the same instruction on
the same stack, and the accessed-key set it ends in is the one it started in.

Written out rather than derived from `balanceOfGas` so that it is, like every
cost definition in this arc, an *independently authored* sum against the fee
schedule and the compiled `Func` (`~/plans/gas-cost.md`, D1). The check that
the authoring is right is `balanceOfGasWarm_eq` below. -/
def balanceOfGasWarm : Nat :=
  gJumpdest
    + (gBase + gVerylow + gVerylow + gVerylow)
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gasWarmAccess)
    + (gBase + (gVerylow + gMemory))
    + (gVerylow + gBase)

/-- 241 gas against `balanceOfGas`' 2241 — the storage read is **93 % of a cold
`balanceOf`, and 41 % of a warm one**. The 2000-gas gap is
`gasColdSload - gasWarmAccess` and nothing else. -/
theorem balanceOfGasWarm_eq : balanceOfGasWarm = 241 := by decide

/-- A `balanceOf(address)` call on `weth` whose key is **already warm** has a
gas-exact run; it costs exactly `balanceOfGasWarm` and returns the slot.

The same walk as the cold derivation — same hint list, same twenty-two steps,
same tree — differing only where `func_run` meets the `SLOAD`: the frame
carries `∈` rather than `∉`, so the tactic selects `Ninst.runCompiled_sload_warm`,
subtracts `gasWarmAccess`, and leaves the base state unmoved. -/
theorem weth_balanceOf_warm_runCompiled {sevm : Sevm} {pre : Devm}
    (h_sel : Sevm.selector sevm = boSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_warm : (⟨sevm.currentTarget, Sevm.dataWord sevm 4⟩ : Adr × B256)
      ∈ pre.accessedStorageKeys)
    (h_gas : balanceOfGasWarm ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiled sevm pre weth post ∧
      post.gasLeft + balanceOfGasWarm = pre.gasLeft ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget (Sevm.dataWord sevm 4)).toBytes := by
  rw [balanceOfGasWarm_eq] at h_gas
  set g := pre.gasLeft with hg
  refine
    ⟨_,
      Prog.runCompiled_intro (G := g - 1)
        (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
        (by simp only [gJumpdest]; omega)
        (by rw [h_stack, h_mem])
        (by
          func_run [boSel, 0, 1, 1, 0, 1, 3]
          · exact Devm.extCost_empty_word
          · exact Func.runCompiled_ret_word (G := g - 241) (e := 0) rfl
              (Devm.extCost_word_word Mem.size_write_word)
              (by simp only [Devm.gasLeft_setMach]; omega)
              (Devm.memRead_word_fst (by simp only [Devm.memory_setMach]; rfl))),
      ?_, rfl⟩
  simp only [Devm.gasLeft_withOutput, Devm.gasLeft_memRead_snd, Devm.gasLeft_setMach,
    balanceOfGasWarm_eq]
  omega

/-- **`weth`'s `balanceOf(address)` call on a warm key costs exactly
`balanceOfGasWarm`.** The exec altitude, from the walk above by
`Prog.exec_of_runCompiled`. Same four limits as `weth_balanceOf_gas_exact`. -/
theorem weth_balanceOf_warm_gas_exact {sevm : Sevm} {pre : Devm}
    (h_code : some sevm.code.toList = Prog.compile weth)
    (h_sel : Sevm.selector sevm = boSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_warm : (⟨sevm.currentTarget, Sevm.dataWord sevm 4⟩ : Adr × B256)
      ∈ pre.accessedStorageKeys)
    (h_gas : balanceOfGasWarm ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      post.gasLeft + balanceOfGasWarm = pre.gasLeft ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget (Sevm.dataWord sevm 4)).toBytes := by
  obtain ⟨post, h_run, h_gas_eq, h_out⟩ :=
    weth_balanceOf_warm_runCompiled h_sel h_stack h_mem h_warm h_gas
  exact ⟨post, Prog.exec_of_runCompiled h_run h_code, h_gas_eq, h_out⟩

/-! ## The closed form

Two constants are two constants. What a caller — and what
`~/plans/fork-repricing-proposal.md` — actually wants is **one function**:
given a selector, what does a call to it cost? That is `wethGas`.

### Why `Option Nat`

`wethGas` is *partial on purpose*. WETH has ten entrypoints and this arc prices
two; a total `B256 → Nat` returning `0` elsewhere would read as "`transfer()`
is free", which is false, and which is the kind of sentence that gets quoted
back at a project. `none` says the only true thing: **this arc has not priced
that selector.** It is not a claim that the selector reverts, and it is not a
claim that no closed form exists — `transfer()`'s exists and needs `SSTORE`
and `LOG` forward rules that Blanc does not yet have.

### Why the `…With` form

`wethGasWith` abstracts the six fee-schedule constants this contract's priced
paths charge, and `wethGas` instantiates them at Jaune's. The bridge is `rfl`.
A repricing is then a different application of the *same* function, which is
exactly the object a fork-repricing analysis consumes: the coefficient vector.

**Be precise about what that does and does not buy**, because the temptation to
overstate it is the reason this is written down. The *statement* is
schedule-symbolic. The *theorems* below are not, and cannot be made so in this
arc: `Jaune.Fork.ForkRules` carries no opcode gas schedule (see this module's
header), and `func_run`'s `gasTacs` unfolds `gVerylow`/`gasColdSload`/… to
numerals before calling `omega`, so a repricing changes every proof term here
even though it changes no statement. `wethGasWith` supports an *informed
calculation* of what a repricing would cost. It does not carry a theorem
across one. -/

/-- `decimalsGas` with the fee schedule abstracted. `cold` is absent because
`decimals()` reads no storage — an unused parameter would be exactly the
fake-parameter shape this arc refuses. -/
def decimalsGasWith (jd base vl hi mem : Nat) : Nat :=
  jd
    + (base + vl + vl + vl)
    + (vl + vl + vl + (vl + hi))
    + (vl + vl + vl + (vl + hi + jd))
    + (vl + vl + vl + (vl + hi + jd))
    + (vl + vl + vl + (vl + hi + jd))
    + (vl + vl + (vl + hi + jd))
    + vl
    + (base + (vl + mem))
    + (vl + base)

/-- `balanceOfGas` with the fee schedule abstracted. `sload` appears exactly
once, at the `SLOAD`. It is the constant the warm/cold split makes vary, which
is why it was a parameter here before the split existed and is what
`wethGasWith` now instantiates two ways: `balanceOfGas` is this at
`gasColdSload` and `balanceOfGasWarm` is this at `gasWarmAccess`, both by
`rfl`. -/
def balanceOfGasWith (jd base vl hi mem sload : Nat) : Nat :=
  jd
    + (base + vl + vl + vl)
    + (vl + vl + vl + (vl + hi))
    + (vl + vl + vl + (vl + hi + jd))
    + (vl + vl + vl + (vl + hi + jd))
    + (vl + vl + vl + (vl + hi))
    + (vl + vl + (vl + hi + jd))
    + (vl + vl + sload)
    + (base + (vl + mem))
    + (vl + base)

/-- **What a call to `weth` costs, by selector and by pre-state, under an
arbitrary fee schedule.** `none` where this arc has not priced the selector;
see the section header for why that is not `0`.

### Why the `Sevm` and `Devm` arguments

**Because `balanceOf(address)` earns them.** A cost function whose state
argument was ignored everywhere would be exactly the unused-parameter shape
this arc refuses on `ForkRules` (see this module's header) — a signature that
looks state-dependent and is not. It is not one: `balanceOf`'s storage read
costs `cold` or `warm` according to whether `⟨target, key⟩` is already in
`pre.accessedStorageKeys`, and `sevm` is what says *which* key, since the key
is the call's own calldata word.

`decimals()` ignores both arguments, and that is correct rather than
embarrassing: it reads no storage, so its cost genuinely is a function of the
selector alone. The arguments are earned by the function as a whole, once,
and `decimals()` is priced through the same function so that a caller has one
thing to call and not two.

### Where the `if` lives, and why here

`Rinst.runCore_sload_cold_eq_ok`'s docstring refused a combined warm/cold
forward lemma, because such a lemma would carry an `if` through every gas
equation downstream of the `SLOAD`. This is the level that `if` belongs at:
written **once**, in the cost function, and eliminated **once**, by the
`by_cases` in `weth_balanceOf_gas_exact_wethGas`. Between those two points the
two cases are two ordinary walks against two ordinary lemmas. -/
def wethGasWith (jd base vl hi mem cold warm : Nat) :
    B256 → Sevm → Devm → Option Nat := fun sel sevm pre =>
  if sel = boSel then
    some (balanceOfGasWith jd base vl hi mem
      (if (⟨sevm.currentTarget, Sevm.dataWord sevm 4⟩ : Adr × B256)
          ∈ pre.accessedStorageKeys then warm else cold))
  else if sel = dcSel then some (decimalsGasWith jd base vl hi mem)
  else none

/-- **What a call to `weth` costs, by selector and pre-state, under Jaune's fee
schedule.** Message-call altitude; these two selectors only; exact under
`Blanc/Compiled.lean`'s compiler-shape assumption. -/
def wethGas : B256 → Sevm → Devm → Option Nat :=
  wethGasWith gJumpdest gBase gVerylow gHigh gMemory gasColdSload gasWarmAccess

/-- The schedule-symbolic bridge, definitional. -/
theorem wethGas_eq_with :
    wethGas = wethGasWith gJumpdest gBase gVerylow gHigh gMemory gasColdSload
      gasWarmAccess := rfl

/-- The two entrypoints are distinct, which is what makes `wethGasWith`'s
second branch reachable. Proved once here rather than at each use: deciding it
forces both `String.keccak` calls behind the selectors. -/
theorem dcSel_ne_boSel : dcSel ≠ boSel := by decide

/-- `wethGas` at `balanceOf(address)`, with the state dependence exposed: the
cost is `balanceOfGasWarm` or `balanceOfGas` according to the pre-state's
accessed-key set. **This is the arc's combined cold/warm statement of the cost
itself**; `weth_balanceOf_gas_exact_wethGas` is the combined statement of the
run. -/
@[simp] theorem wethGas_boSel {sevm : Sevm} {pre : Devm} :
    wethGas boSel sevm pre =
      some (if (⟨sevm.currentTarget, Sevm.dataWord sevm 4⟩ : Adr × B256)
              ∈ pre.accessedStorageKeys then balanceOfGasWarm else balanceOfGas) := by
  by_cases h : (⟨sevm.currentTarget, Sevm.dataWord sevm 4⟩ : Adr × B256)
      ∈ pre.accessedStorageKeys
  · rw [if_pos h]
    simp only [wethGas, wethGasWith, if_pos h]
    rfl
  · rw [if_neg h]
    simp only [wethGas, wethGasWith, if_neg h]
    rfl

/-- `wethGas` at `balanceOf(address)` on a cold key — the value every statement
before this arc's Step 3 assumed. -/
theorem wethGas_boSel_cold {sevm : Sevm} {pre : Devm}
    (h_cold : (⟨sevm.currentTarget, Sevm.dataWord sevm 4⟩ : Adr × B256)
      ∉ pre.accessedStorageKeys) :
    wethGas boSel sevm pre = some balanceOfGas := by
  rw [wethGas_boSel, if_neg h_cold]

/-- `wethGas` at `balanceOf(address)` on a warm key. -/
theorem wethGas_boSel_warm {sevm : Sevm} {pre : Devm}
    (h_warm : (⟨sevm.currentTarget, Sevm.dataWord sevm 4⟩ : Adr × B256)
      ∈ pre.accessedStorageKeys) :
    wethGas boSel sevm pre = some balanceOfGasWarm := by
  rw [wethGas_boSel, if_pos h_warm]

/-- `wethGas` at `decimals()`, for every state: it reads no storage. -/
@[simp] theorem wethGas_dcSel {sevm : Sevm} {pre : Devm} :
    wethGas dcSel sevm pre = some decimalsGas := by
  simp only [wethGas, wethGasWith, if_neg dcSel_ne_boSel]
  rfl

/-- **`balanceOf(address)` costs exactly what `wethGas` says it does — with no
assumption about the storage key.**

`weth_balanceOf_gas_exact` restated so that the number is not written down
beside the theorem but *produced by the cost function*: `cost` is whatever
`wethGas` returns for the selector **and pre-state** this frame carries, and
the conclusion is that the frame's gas drops by exactly that. The gas
precondition is stated through `wethGas` too, so the function is load-bearing
on both sides.

**This is the arc's combined cold/warm theorem for this target**, and the
premise list is where to see it: `h_cold` is *gone*. Every earlier statement
about `balanceOf(address)`'s cost held only for a frame whose key had not been
touched. This one holds for every frame. The `by_cases` below is the single
place the `if` that `wethGasWith` writes is eliminated.

Same remaining limits as `weth_balanceOf_gas_exact` — message-call altitude,
one entrypoint of one contract, one fixed selector, exact under
`Blanc/Compiled.lean`'s compiler-shape assumption, and Jaune's current fee
schedule. -/
theorem weth_balanceOf_gas_exact_wethGas {sevm : Sevm} {pre : Devm} {cost : Nat}
    (h_code : some sevm.code.toList = Prog.compile weth)
    (h_sel : Sevm.selector sevm = boSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cost : wethGas (Sevm.selector sevm) sevm pre = some cost)
    (h_gas : cost ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      post.gasLeft + cost = pre.gasLeft ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget (Sevm.dataWord sevm 4)).toBytes := by
  rw [h_sel, wethGas_boSel] at h_cost
  by_cases h : (⟨sevm.currentTarget, Sevm.dataWord sevm 4⟩ : Adr × B256)
      ∈ pre.accessedStorageKeys
  · rw [if_pos h] at h_cost
    injection h_cost with h_cost
    subst h_cost
    exact weth_balanceOf_warm_gas_exact h_code h_sel h_stack h_mem h h_gas
  · rw [if_neg h] at h_cost
    injection h_cost with h_cost
    subst h_cost
    exact weth_balanceOf_gas_exact h_code h_sel h_stack h_mem h h_gas

/-- **`decimals()` costs exactly what `wethGas` says it does.** The same
restatement as `weth_balanceOf_gas_exact_wethGas`, on the second target. The
two new arguments are supplied and ignored, which is what "reads no storage"
looks like at this altitude. -/
theorem weth_decimals_gas_exact_wethGas {sevm : Sevm} {pre : Devm} {cost : Nat}
    (h_code : some sevm.code.toList = Prog.compile weth)
    (h_sel : Sevm.selector sevm = dcSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cost : wethGas (Sevm.selector sevm) sevm pre = some cost)
    (h_gas : cost ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      post.gasLeft + cost = pre.gasLeft ∧
      Devm.output post = (0x12 : B256).toBytes := by
  rw [h_sel, wethGas_dcSel] at h_cost
  injection h_cost with h_cost
  subst h_cost
  exact weth_decimals_gas_exact h_code h_sel h_stack h_mem h_gas

/-- **`balanceOf(address)` costs what `wethGas` says, from an arbitrary
`Prog.RunCompiled` witness, with no assumption about the storage key.**

The hypothesis-position altitude restated through the widened cost function, so
that `wethGas` is load-bearing at *both* altitudes rather than only where the
run is constructed. This is the shape a caller reasoning about an arbitrary run
of this contract states over, and it is the one in which the cost function is
most useful: the caller supplies a selector and a pre-state, `wethGas` supplies
the number.

By determinism off the combined exec-altitude theorem, so the warm/cold split
is eliminated once for both altitudes rather than twice. -/
theorem weth_balanceOf_gas_of_runCompiled_wethGas {sevm : Sevm} {pre post : Devm}
    {cost : Nat}
    (h_code : some sevm.code.toList = Prog.compile weth)
    (h_sel : Sevm.selector sevm = boSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cost : wethGas (Sevm.selector sevm) sevm pre = some cost)
    (h_gas : cost ≤ pre.gasLeft)
    (h_run : Prog.RunCompiled sevm pre weth post) :
    pre.gasLeft = post.gasLeft + cost := by
  obtain ⟨post', h_exec', h_gas_eq, _⟩ :=
    weth_balanceOf_gas_exact_wethGas h_code h_sel h_stack h_mem h_cost h_gas
  have h_exec : exec ⟨0, sevm, pre⟩ = .ok post :=
    Prog.exec_of_runCompiled h_run h_code
  rw [h_exec] at h_exec'
  injection h_exec' with h_eq
  subst h_eq
  omega

/-- **`decimals()` costs what `wethGas` says, from an arbitrary
`Prog.RunCompiled` witness.** The same restatement, on the second target. -/
theorem weth_decimals_gas_of_runCompiled_wethGas {sevm : Sevm} {pre post : Devm}
    {cost : Nat}
    (h_code : some sevm.code.toList = Prog.compile weth)
    (h_sel : Sevm.selector sevm = dcSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cost : wethGas (Sevm.selector sevm) sevm pre = some cost)
    (h_gas : cost ≤ pre.gasLeft)
    (h_run : Prog.RunCompiled sevm pre weth post) :
    pre.gasLeft = post.gasLeft + cost := by
  rw [h_sel, wethGas_dcSel] at h_cost
  injection h_cost with h_cost
  subst h_cost
  exact weth_decimals_gas_of_runCompiled h_code h_sel h_stack h_mem h_gas h_run

/-! ## The bound: no state can make these calls dearer

`wethGas` says what a call costs *in a given state*. The question a security
reader asks is the other one: **is there a state that makes it cost more?**

For these two selectors the answer is no, and `wethGas_le_max` is the proof.
The maximum is not a new derivation — it is `wethGas` with the storage read
pinned cold, which is the only place the pre-state enters at all.

**Say what this does not cover, every time it is quoted.** It is these two
selectors, not the contract: `transfer()`, `withdraw(uint256)` and the rest are
`none` in `wethGas` and are not bounded here by anything. It is message-call
altitude. It is Jaune's current fee schedule. And it is a bound on *this
frame's* gas, which for a call-free entrypoint is the whole cost and for an
entrypoint that calls out would not be. -/

/-- **The cold branch of `wethGasWith`, per selector** — the most a priced
`weth` entrypoint can cost under an arbitrary fee schedule, provided `cold` is
the dearer of the two storage charges (which `wethGasMax` instantiates it to
be). -/
def wethGasMaxWith (jd base vl hi mem cold : Nat) : B256 → Option Nat := fun sel =>
  if sel = boSel then some (balanceOfGasWith jd base vl hi mem cold)
  else if sel = dcSel then some (decimalsGasWith jd base vl hi mem)
  else none

/-- **The most a priced `weth` entrypoint can cost**, under Jaune's fee
schedule. -/
def wethGasMax : B256 → Option Nat :=
  wethGasMaxWith gJumpdest gBase gVerylow gHigh gMemory gasColdSload

/-- The schedule-symbolic bridge for the bound, definitional. -/
theorem wethGasMax_eq_with :
    wethGasMax = wethGasMaxWith gJumpdest gBase gVerylow gHigh gMemory
      gasColdSload := rfl

/-- **No calldata and no accessed-key state can make a priced `weth` entrypoint
cost more than `wethGasMax`.**

The DoS-freedom statement, quantified over *every* selector, `Sevm` and `Devm`:
whenever `wethGas` prices a call at all, `wethGasMax` prices it too, and the
actual cost is at most the bound. Nothing about the frame is fixed — not the
calldata, not the accessed-key set, not the storage contents.

Stated as "`wethGas` priced it, therefore `wethGasMax` priced it and the first
is at most the second" rather than as `wethGas … ≤ wethGasMax …`, because there
is no order on `Option Nat` in this repository and inventing one to state a
four-line lemma would put a definition between the reader and the claim. The
content is the same and the `∃` is discharged by `rfl` in both live branches.

**Read with the section header's limits**: these selectors, this fee schedule,
message-call altitude, this compiler. -/
theorem wethGas_le_max {sel : B256} {sevm : Sevm} {pre : Devm} {cost : Nat}
    (h_cost : wethGas sel sevm pre = some cost) :
    ∃ bound, wethGasMax sel = some bound ∧ cost ≤ bound := by
  simp only [wethGas, wethGasWith] at h_cost
  simp only [wethGasMax, wethGasMaxWith]
  by_cases hb : sel = boSel
  · subst hb
    rw [if_pos rfl] at h_cost ⊢
    refine ⟨_, rfl, ?_⟩
    injection h_cost with h_cost
    subst h_cost
    split <;> decide
  · rw [if_neg hb] at h_cost ⊢
    by_cases hd : sel = dcSel
    · subst hd
      rw [if_pos rfl] at h_cost ⊢
      refine ⟨_, rfl, ?_⟩
      injection h_cost with h_cost
      subst h_cost
      exact Nat.le_refl _
    · rw [if_neg hd] at h_cost
      exact absurd h_cost (by simp)

end Blanc
