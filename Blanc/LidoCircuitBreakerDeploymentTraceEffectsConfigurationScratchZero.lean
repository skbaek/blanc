-- LidoCircuitBreakerDeploymentTraceEffectsConfigurationScratchZero.lean : pause scratch zero certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsConfigurationScratchValue

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

private theorem officialConstructorPatchedMemory_write_pause_zero :
    officialConstructorPatchedMemory.write
        officialConstructorEventScratch (0 : B256).toBytes =
      officialConstructorPauseZeroMemory := by
  rfl

theorem officialConstructorPauseScratchZero_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPauseZeroMemory, G + 15⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPatchedMemory, G + 27⟩)
      (pushB256 0 :::
        storeByteOffset officialConstructorEventScratch +++ rest) post := by
  apply constructorZeroMstorePrefix_runCompiled
      (offset := officialConstructorEventScratch) (storeExt := 4)
      (memory' := officialConstructorPauseZeroMemory)
      (Gafter := G + 15)
  · rw [officialConstructorEventScratch_eq]
    decide
  · omega
  · intro S G'
    exact Devm.extCost_of_size officialConstructorPatchedMemory_size (by
      rw [officialConstructorEventScratch_eq]
      decide +kernel)
  · exact officialConstructorPatchedMemory_write_pause_zero
  · exact hrest

end LidoCircuitBreaker

end Blanc
