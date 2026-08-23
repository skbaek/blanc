-- LidoCircuitBreakerDeploymentTraceEffectsInitializedLog.lean : initialized event certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsInitializedLogOpcode

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

theorem officialConstructorInitializedLogLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPatchedMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchedMemory, G + 2163⟩)
      (officialConstructorInitializedPrefix +++ rest) post := by
  have hvalue : Bytes.toB256
      ((officialConstructorPatchedMemory.read 0 32).1) =
        officialParams.admin := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorPatchedMemory_read_argument ⟨0, by decide⟩
  have hmemory : (officialConstructorPatchedMemory.read 0 32).2 =
      officialConstructorPatchedMemory := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [officialConstructorPatchedMemory_size]
    · rw [officialConstructorPatchedMemory_size]
      decide
  have hlog := officialConstructorInitializedLogOpcode_runCompiled
    hstatic hrest
  unfold officialConstructorInitializedPrefix
  apply constructorArgumentLog2Prefix_runCompiled
      (i := ⟨0, by decide⟩)
      (eventTopic := circuitBreakerInitializedEvent)
      (indexedTopic := officialParams.admin)
      (indexPushCost := 2) (loadCost := 3) (eventPushCost := 3)
      (Gafter := G + 2149)
  · omega
  · decide
  · intro S G'
    change gVerylow +
      (base.setMach ⟨S, officialConstructorPatchedMemory, G'⟩).extCost
        [⟨0, 32⟩] = 3
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorPatchedMemory_size
      (by decide +kernel)
  · exact hvalue
  · exact hmemory
  · simpa only [gVerylow] using pushCost_of_ne_zero
      (w := circuitBreakerInitializedEvent) (by decide +kernel)
  · exact hlog

end LidoCircuitBreaker

end Blanc
