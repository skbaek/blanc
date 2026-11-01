import Blanc.Forward

namespace Blanc

open Jaune

/-! # The shared `balanceOf(address)` body, walked once

`Blanc.balanceOf` (`arg 0`, `SLOAD`, `mstoreAt 0`, `returnMemoryRange 0 32`) is
the body behind WETH9's and fmint's `balanceOf` entries.  A walk that reaches
it through a dispatcher needed `maxRecDepth` 604-613 in the WETH9 walks, for the
body tail alone.

These two lemmas walk the body once, for every function table `fs` (the body
is call-free, so its post-state does not depend on the table), and a caller
walks its dispatcher to the body entry and closes the rest with one `exact`.
The walk drops the cold `SLOAD` successor's dead inner `setMach` before it
continues; without that collapse the remaining four nodes alone exceed the
default recursion depth.  The cold and warm forms differ only at the `SLOAD`: 2119 and 119 gas
(the cold read's `gasColdSload` against `gasWarmAccess`). -/

/-- The `SLOAD` successor's inner `setMach` is dead once the outer one lands;
dropping it before the walk continues keeps the cold body under the default
recursion depth. -/
private theorem addAccessedStorageKey_setMach_setMach {base : Devm} {target : Adr}
    {key : B256} {mach mach' : Mach} :
    (addAccessedStorageKey (base.setMach mach) target key).setMach mach' =
      (addAccessedStorageKey base target key).setMach mach' := rfl

/-- The cold-key `balanceOf` body: 2119 gas, returning the slot keyed by the
first argument word. -/
theorem Func.balanceOf_runCompiled_cold {sevm : Sevm} {base : Devm}
    {g : Nat} (hfork : CoveredFork sevm.benvStat.fork)
    (h_cold : (⟨sevm.currentTarget, Sevm.dataWord sevm (32 * 0 + 4)⟩ : Adr × B256)
      ∉ base.accessedStorageKeys)
    (h_gas : 2119 ≤ g) :
    ∃ post, (∀ fs, Func.RunCompiled fs sevm (base.setMach ⟨[], Mem.empty, g, base.stateGas⟩)
        balanceOf post) ∧
      post.gasLeft = g - 2119 ∧
      Devm.output post =
        (base.getStorVal sevm.currentTarget (Sevm.dataWord sevm (32 * 0 + 4))).toBytes := by
  have h_stateGas : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  exact
    ⟨_,
      fun _ => (by
        func_run (3)
        simp only [Devm.getStorVal_setMach, addAccessedStorageKey_setMach_setMach]
        func_run [3]
        · exact Devm.extCost_empty_word
        · exact Func.runCompiled_return_word (G := g - 2119) (e := 0) rfl
            (Devm.extCost_word_word Mem.size_write_word)
            (by simp only [Devm.gasLeft_setMach]; omega)
            (Devm.memRead_word_fst (by simp only [Devm.memory_setMach]; rfl))),
      (by simp only [Devm.withOutput_gasLeft, Devm.memRead_gasLeft, Devm.gasLeft_setMach]),
      rfl⟩

/-- The warm-key `balanceOf` body: 119 gas, the key already in the frame's
accessed set. -/
theorem Func.balanceOf_runCompiled_warm {sevm : Sevm} {base : Devm}
    {g : Nat} (hfork : CoveredFork sevm.benvStat.fork)
    (h_warm : (⟨sevm.currentTarget, Sevm.dataWord sevm (32 * 0 + 4)⟩ : Adr × B256)
      ∈ base.accessedStorageKeys)
    (h_gas : 119 ≤ g) :
    ∃ post, (∀ fs, Func.RunCompiled fs sevm (base.setMach ⟨[], Mem.empty, g, base.stateGas⟩)
        balanceOf post) ∧
      post.gasLeft = g - 119 ∧
      Devm.output post =
        (base.getStorVal sevm.currentTarget (Sevm.dataWord sevm (32 * 0 + 4))).toBytes := by
  have h_stateGas : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  exact
    ⟨_,
      fun _ => (by
        func_run [3]
        · exact Devm.extCost_empty_word
        · exact Func.runCompiled_return_word (G := g - 119) (e := 0) rfl
            (Devm.extCost_word_word Mem.size_write_word)
            (by simp only [Devm.gasLeft_setMach]; omega)
            (Devm.memRead_word_fst (by simp only [Devm.memory_setMach]; rfl))),
      (by simp only [Devm.withOutput_gasLeft, Devm.memRead_gasLeft, Devm.gasLeft_setMach]),
      rfl⟩

end Blanc
