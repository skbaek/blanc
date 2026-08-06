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

end Fmint
end Blanc
