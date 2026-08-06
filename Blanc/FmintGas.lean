import Blanc.FmintLive

namespace Blanc
namespace Fmint

open Jaune

set_option maxRecDepth 8000

/-! # What fmint's `totalSupply()` call *costs*

`Blanc/FmintLive.lean` proves that the call succeeds and what it returns, but
never states its gas as a *conjunct* of the run — see `Blanc/WethGas.lean`'s
module docstring, which this mirrors exactly, for the full rationale. This
module supplies the same two theorems for fmint's `totalSupply()`.

**Message-call altitude, one entrypoint, one contract, one fixed selector,
exact under `Blanc/Compiled.lean`'s compiler-shape assumption**, plus the
schedule limit `Blanc/WethGas.lean` states: `totalSupplyGas` is written in
Jaune's gas symbols and never in numerals, but the *theorem* is not
schedule-parametric — `Jaune.Fork.ForkRules` carries no opcode gas schedule
(arc plan `~/plans/gas-cost.md`, correction C1). A repricing changes the
number and the proof term, never the statement. -/

/-- `Devm.gasLeft` through `Devm.withOutput`, local to this module. Fmint stays
a sibling of weth (Blanc's `README.md`, *contracts are siblings*), so this
cannot import `Blanc.Devm.gasLeft_withOutput` from `Blanc/WethGas.lean`; the
fact is two lines and generic, so the duplication costs nothing. Same shallow,
generic argument as `Blanc/WethGas.lean`'s copy: the update touches `meta`
only, so using it never forces the state it is applied to — the 21-step
construction below — to reduce. -/
lemma Devm.gasLeft_withOutput {devm : Devm} {out : Bytes} :
    (devm.withOutput out).gasLeft = devm.gasLeft := rfl

/-- `Devm.gasLeft` through the second projection of `Devm.memRead`, local to
this module for the reason `Devm.gasLeft_withOutput` above records. -/
lemma Devm.gasLeft_memRead_snd {devm : Devm} {i sz : Nat} :
    (devm.memRead i sz).2.gasLeft = devm.gasLeft := rfl

/-! ## A second entrypoint: `decimals()`

The same target `Blanc/WethGas.lean` adds, on the other contract — and it is
the *same compiled `Func`*, `Blanc.decimals`, since `decimals()` is one of the
fourteen definitions Blanc's `README.md` rule hoisted into `Blanc/CommonCore.lean`
for both contracts to share.

That is exactly what makes the pair worth having. Identical body, different
dispatcher: `decimals()` is entry 4 of `fmintFuncs`' twelve where it is entry 5
of `wethFuncs`' ten, so the two walks take **different arms through different
trees** and the resulting figures differ — 138 here against 139 there. The
difference is not the entrypoint. It is where the contract's author put it in
the selector table. -/

/-- The selector `decimals()` dispatches on. Local to this module for the
reason `Blanc/FmintLive.lean` records for `tsSel`. -/
abbrev dcSel : B256 := selector "decimals" []

/-- Every gas constant the `decimals()` derivation charges, in the order it
charges them: the program's entry `JUMPDEST`; `fsig`'s four instructions; four
dispatch forks, the first and third taken by the `.succ` arm and the second and
fourth falling through; the leaf's `PUSH`/`EQ` and its taken arm; then
`decimals`' own body — one `PUSH1 0x12`, `mstoreAt 0`, and
`returnMemoryRange 0 32`.

One fork deeper than `totalSupplyGas`, which walks three: twelve entries put
`totalSupply()` at a depth-3 leaf and `decimals()` at a depth-4 one. Two of the
four forks are taken here where two of `Blanc.decimalsGas`' four fall through,
and that one-arm difference is the whole 138-versus-139 gap between the two
contracts' `decimals()`. The bodies are identical because the `Func` is. -/
def decimalsGas : Nat :=
  gJumpdest
    + (gBase + gVerylow + gVerylow + gVerylow)
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + (gVerylow + gVerylow + gVerylow + (gVerylow + gHigh))
    + (gVerylow + gVerylow + (gVerylow + gHigh + gJumpdest))
    + gVerylow
    + (gBase + (gVerylow + gMemory))
    + (gVerylow + gBase)

/-- 138 gas, of which 122 is the dispatcher and 16 the body — one `gJumpdest`
under WETH's `decimals()`, which takes one more fork arm. -/
theorem decimalsGas_eq : decimalsGas = 138 := by decide

/-- A `decimals()` call on `fmint` has a gas-exact run; it costs exactly
`decimalsGas` and returns `0x12`.

The gas is a **conjunct of the run**, for the reason
`Blanc.weth_decimals_runCompiled`'s docstring gives: a walk written inside this
module pays the dispatch tree's keccak cost once, where re-deriving a witness
whose existential hides it pays twice. -/
theorem decimals_runCompiled {sevm : Sevm} {pre : Devm}
    (h_sel : Sevm.selector sevm = dcSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : decimalsGas ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiled sevm pre fmint post ∧
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
          func_run [dcSel, 1, 0, 1, 0, 1, 3]
          · exact Devm.extCost_empty_word
          · exact Func.runCompiled_ret_word (G := g - 138) (e := 0) rfl
              (Devm.extCost_word_word Mem.size_write_word)
              (by simp only [Devm.gasLeft_setMach]; omega)
              (Devm.memRead_word_fst (by simp only [Devm.memory_setMach]; rfl))),
      ?_, rfl⟩
  simp only [Devm.gasLeft_withOutput, Devm.gasLeft_memRead_snd, Devm.gasLeft_setMach,
    decimalsGas_eq]
  omega

/-- **`fmint`'s `decimals()` call costs exactly `decimalsGas`.**

The exec-altitude exactness theorem; the walk above already carries the gas
conjunct, so this is `Prog.exec_of_runCompiled` applied to it. Same four limits
as `fmint_totalSupply_succeeds`, plus this module's schedule limit. -/
theorem decimals_gas_exact {sevm : Sevm} {pre : Devm}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = dcSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : decimalsGas ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      post.gasLeft + decimalsGas = pre.gasLeft ∧
      Devm.output post = (0x12 : B256).toBytes := by
  obtain ⟨post, h_run, h_gas_eq, h_out⟩ :=
    decimals_runCompiled h_sel h_stack h_mem h_gas
  exact ⟨post, Prog.exec_of_runCompiled h_run h_code, h_gas_eq, h_out⟩

/-- **`fmint`'s `decimals()` call succeeds**, and returns `0x12`. The
`fmint_totalSupply_succeeds`-shaped statement for this target, with the gas
conjunct dropped. -/
theorem fmint_decimals_succeeds {sevm : Sevm} {pre : Devm}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = dcSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : decimalsGas ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      Devm.output post = (0x12 : B256).toBytes := by
  obtain ⟨post, h_exec, _, h_out⟩ :=
    decimals_gas_exact h_code h_sel h_stack h_mem h_gas
  exact ⟨post, h_exec, h_out⟩

/-- **`fmint`'s `decimals()` call costs exactly `decimalsGas`, from an
arbitrary `Prog.RunCompiled` witness.** By determinism; see
`Blanc.weth_balanceOf_gas_of_runCompiled`. -/
theorem decimals_gas_of_runCompiled {sevm : Sevm} {pre post : Devm}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = dcSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : decimalsGas ≤ pre.gasLeft)
    (h_run : Prog.RunCompiled sevm pre fmint post) :
    pre.gasLeft = post.gasLeft + decimalsGas := by
  obtain ⟨post', h_exec', h_gas_eq, _⟩ :=
    decimals_gas_exact h_code h_sel h_stack h_mem h_gas
  have h_exec : exec ⟨0, sevm, pre⟩ = .ok post :=
    Prog.exec_of_runCompiled h_run h_code
  rw [h_exec] at h_exec'
  injection h_exec' with h_eq
  subst h_eq
  omega

/-- **`fmint`'s `totalSupply()` call costs exactly `totalSupplyGas`.**

The exactness theorem at the `exec` altitude, by the same route as
`weth_balanceOf_gas_exact`: `exec` is a function, so the re-derived witness's
`gasLeft` is a projection through the construction, closed by
`Blanc.Devm.gasLeft_withOutput`, `Blanc.Devm.gasLeft_memRead_snd` and the
existing `Devm.gasLeft_setMach` rather than by a blind `rfl` on the 21-step
construction. -/
theorem totalSupply_gas_exact {sevm : Sevm} {pre : Devm}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = tsSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, supplySlot⟩ : Adr × B256)
      ∉ pre.accessedStorageKeys)
    (h_gas : totalSupplyGas ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      post.gasLeft + totalSupplyGas = pre.gasLeft ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget supplySlot).toBytes := by
  rw [totalSupplyGas_eq] at h_gas
  set g := pre.gasLeft with hg
  refine
    ⟨_,
      Prog.exec_of_runCompiled
        (Prog.runCompiled_intro (G := g - 1)
          (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
          (by simp only [gJumpdest]; omega)
          (by rw [h_stack, h_mem])
          (by
            func_run [tsSel, 1, 1, 0, 1, supplySlot, 3]
            · exact Devm.extCost_empty_word
            · exact Func.runCompiled_ret_word (G := g - 2218) (e := 0) rfl
                (Devm.extCost_word_word Mem.size_write_word)
                (by simp only [Devm.gasLeft_setMach]; omega)
                (Devm.memRead_word_fst (by simp only [Devm.memory_setMach]; rfl))))
        h_code,
      ?_, rfl⟩
  simp only [Devm.gasLeft_withOutput, Devm.gasLeft_memRead_snd, Devm.gasLeft_setMach,
    totalSupplyGas_eq]
  omega

/-- **`fmint`'s `totalSupply()` call costs exactly `totalSupplyGas`, from an
arbitrary `Prog.RunCompiled` witness.**

The hypothesis-position shape, by determinism rather than inversion — same
route as `weth_balanceOf_gas_of_runCompiled`; see that theorem's docstring. -/
theorem totalSupply_gas_of_runCompiled {sevm : Sevm} {pre post : Devm}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = tsSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, supplySlot⟩ : Adr × B256)
      ∉ pre.accessedStorageKeys)
    (h_gas : totalSupplyGas ≤ pre.gasLeft)
    (h_run : Prog.RunCompiled sevm pre fmint post) :
    pre.gasLeft = post.gasLeft + totalSupplyGas := by
  obtain ⟨post', h_exec', h_gas_eq, _⟩ :=
    totalSupply_gas_exact h_code h_sel h_stack h_mem h_cold h_gas
  have h_exec : exec ⟨0, sevm, pre⟩ = .ok post :=
    Prog.exec_of_runCompiled h_run h_code
  rw [h_exec] at h_exec'
  injection h_exec' with h_eq
  subst h_eq
  omega

/-! ## The closed form

fmint's half of what `Blanc/WethGas.lean`'s *The closed form* section
describes. Read that section for the two design points — why the result is
`Option Nat` rather than a total function with a junk default, and what the
`…With` form does and does not buy — because both apply here verbatim and
neither is restated.

These definitions are **not** shared with WETH's, and must not become so.
Blanc's `README.md` rule (*Module hierarchy: contracts are siblings*) is that a
contract module never imports another contract's; a `Gas` layer parameterised
over both contracts would be exactly that import. The duplication is also not
accidental in the way it looks: `decimalsGasWith`'s *body* here is
character-identical to WETH's only because the two dispatch paths happen to
have the same fork count and the same body, and they part on which arms are
taken — which is why the instantiated figures are 138 and 139. -/

/-- `decimalsGas` with the fee schedule abstracted. No `cold` parameter:
`decimals()` reads no storage, and an unused parameter is the fake-parameter
shape this arc refuses. -/
def decimalsGasWith (jd base vl hi mem : Nat) : Nat :=
  jd
    + (base + vl + vl + vl)
    + (vl + vl + vl + (vl + hi + jd))
    + (vl + vl + vl + (vl + hi))
    + (vl + vl + vl + (vl + hi + jd))
    + (vl + vl + vl + (vl + hi))
    + (vl + vl + (vl + hi + jd))
    + vl
    + (base + (vl + mem))
    + (vl + base)

/-- `totalSupplyGas` with the fee schedule abstracted. `cold` appears exactly
once, at the `SLOAD`. -/
def totalSupplyGasWith (jd base vl hi mem cold : Nat) : Nat :=
  jd
    + (base + vl + vl + vl)
    + (vl + vl + vl + (vl + hi + jd))
    + (vl + vl + vl + (vl + hi + jd))
    + (vl + vl + vl + (vl + hi))
    + (vl + vl + (vl + hi + jd))
    + (base + vl + cold)
    + (base + (vl + mem))
    + (vl + base)

/-- **What a call to `fmint` costs, by selector, under an arbitrary fee
schedule.** `none` where this arc has not priced the selector — which here
includes `flashLoan`, and for that one the `none` is *permanent*: a flash
loan's cost includes the borrower's callback, which is unbounded, so no closed
form exists at all. See `~/plans/gas-cost.md` §1. -/
def fmintGasWith (jd base vl hi mem cold : Nat) : B256 → Option Nat := fun sel =>
  if sel = tsSel then some (totalSupplyGasWith jd base vl hi mem cold)
  else if sel = dcSel then some (decimalsGasWith jd base vl hi mem)
  else none

/-- **What a call to `fmint` costs, by selector, under Jaune's fee schedule.**
Message-call altitude; these two selectors only; exact under
`Blanc/Compiled.lean`'s compiler-shape assumption. -/
def fmintGas : B256 → Option Nat :=
  fmintGasWith gJumpdest gBase gVerylow gHigh gMemory gasColdSload

/-- The schedule-symbolic bridge, definitional. -/
theorem fmintGas_eq_with :
    fmintGas = fmintGasWith gJumpdest gBase gVerylow gHigh gMemory gasColdSload := rfl

/-- The two priced entrypoints are distinct, which is what makes
`fmintGasWith`'s second branch reachable. Proved once: deciding it forces both
`String.keccak` calls behind the selectors. -/
theorem dcSel_ne_tsSel : dcSel ≠ tsSel := by decide

@[simp] theorem fmintGas_tsSel : fmintGas tsSel = some totalSupplyGas := by
  simp only [fmintGas, fmintGasWith]
  rfl

@[simp] theorem fmintGas_dcSel : fmintGas dcSel = some decimalsGas := by
  simp only [fmintGas, fmintGasWith, if_neg dcSel_ne_tsSel]
  rfl

/-- **`totalSupply()` costs exactly what `fmintGas` says it does.**

`totalSupply_gas_exact` restated so that the number is produced by the cost
function rather than written beside the theorem; see
`Blanc.weth_balanceOf_gas_exact_wethGas` for the shape and why both the
precondition and the conclusion go through the function. -/
theorem totalSupply_gas_exact_fmintGas {sevm : Sevm} {pre : Devm} {cost : Nat}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = tsSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, supplySlot⟩ : Adr × B256)
      ∉ pre.accessedStorageKeys)
    (h_cost : fmintGas (Sevm.selector sevm) = some cost)
    (h_gas : cost ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      post.gasLeft + cost = pre.gasLeft ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget supplySlot).toBytes := by
  rw [h_sel, fmintGas_tsSel] at h_cost
  injection h_cost with h_cost
  subst h_cost
  exact totalSupply_gas_exact h_code h_sel h_stack h_mem h_cold h_gas

/-- **`decimals()` costs exactly what `fmintGas` says it does.** The same
restatement, on the second target. -/
theorem decimals_gas_exact_fmintGas {sevm : Sevm} {pre : Devm} {cost : Nat}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = dcSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cost : fmintGas (Sevm.selector sevm) = some cost)
    (h_gas : cost ≤ pre.gasLeft) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧
      post.gasLeft + cost = pre.gasLeft ∧
      Devm.output post = (0x12 : B256).toBytes := by
  rw [h_sel, fmintGas_dcSel] at h_cost
  injection h_cost with h_cost
  subst h_cost
  exact decimals_gas_exact h_code h_sel h_stack h_mem h_gas

/-- **`totalSupply()` costs what `fmintGas` says, from an arbitrary
`Prog.RunCompiled` witness.** The hypothesis-position altitude restated through
the cost function; see `Blanc.weth_balanceOf_gas_of_runCompiled_wethGas` for why
both altitudes get one. -/
theorem totalSupply_gas_of_runCompiled_fmintGas {sevm : Sevm} {pre post : Devm}
    {cost : Nat}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = tsSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, supplySlot⟩ : Adr × B256)
      ∉ pre.accessedStorageKeys)
    (h_cost : fmintGas (Sevm.selector sevm) = some cost)
    (h_gas : cost ≤ pre.gasLeft)
    (h_run : Prog.RunCompiled sevm pre fmint post) :
    pre.gasLeft = post.gasLeft + cost := by
  rw [h_sel, fmintGas_tsSel] at h_cost
  injection h_cost with h_cost
  subst h_cost
  exact totalSupply_gas_of_runCompiled h_code h_sel h_stack h_mem h_cold h_gas h_run

/-- **`decimals()` costs what `fmintGas` says, from an arbitrary
`Prog.RunCompiled` witness.** The same restatement, on the second target. -/
theorem decimals_gas_of_runCompiled_fmintGas {sevm : Sevm} {pre post : Devm}
    {cost : Nat}
    (h_code : some sevm.code.toList = Prog.compile fmint)
    (h_sel : Sevm.selector sevm = dcSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cost : fmintGas (Sevm.selector sevm) = some cost)
    (h_gas : cost ≤ pre.gasLeft)
    (h_run : Prog.RunCompiled sevm pre fmint post) :
    pre.gasLeft = post.gasLeft + cost := by
  rw [h_sel, fmintGas_dcSel] at h_cost
  injection h_cost with h_cost
  subst h_cost
  exact decimals_gas_of_runCompiled h_code h_sel h_stack h_mem h_gas h_run

end Fmint
end Blanc
