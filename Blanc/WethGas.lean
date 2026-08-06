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

end Blanc
