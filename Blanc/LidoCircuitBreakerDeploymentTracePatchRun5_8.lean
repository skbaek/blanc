-- LidoCircuitBreakerDeploymentTracePatchRun5_8.lean : constructor patches five through eight.
--
-- The middle four concrete patch states and their gas-exact reverse walk.

import Blanc.LidoCircuitBreakerDeploymentTracePatchRun1_4

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

def officialConstructorPatchMemory5 : Mem :=
  officialConstructorPatchMemory4.write 441
    officialParams.minPauseDuration.toBytes

def officialConstructorPatchMemory6 : Mem :=
  officialConstructorPatchMemory5.write 937
    officialParams.minPauseDuration.toBytes

def officialConstructorPatchMemory7 : Mem :=
  officialConstructorPatchMemory6.write 482
    officialParams.maxPauseDuration.toBytes

def officialConstructorPatchMemory8 : Mem :=
  officialConstructorPatchMemory7.write 2185
    officialParams.maxPauseDuration.toBytes
private def officialConstructorPatchInvariant5 :
    ConstructorPatchInvariant officialConstructorPatchMemory5 :=
  officialConstructorPatchInvariant4.write 441
    officialParams.minPauseDuration (by decide) (by decide)

private def officialConstructorPatchInvariant6 :
    ConstructorPatchInvariant officialConstructorPatchMemory6 :=
  officialConstructorPatchInvariant5.write 937
    officialParams.minPauseDuration (by decide) (by decide)

private def officialConstructorPatchInvariant7 :
    ConstructorPatchInvariant officialConstructorPatchMemory7 :=
  officialConstructorPatchInvariant6.write 482
    officialParams.maxPauseDuration (by decide) (by decide)

def officialConstructorPatchInvariant8 :
    ConstructorPatchInvariant officialConstructorPatchMemory8 :=
  officialConstructorPatchInvariant7.write 2185
    officialParams.maxPauseDuration (by decide) (by decide)

theorem officialConstructorPatchLine5_8_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory8, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory4, G + 48⟩)
      (loadArgumentIndex 1 +++ storeByteOffset 441 +++
        loadArgumentIndex 1 +++ storeByteOffset 937 +++
        loadArgumentIndex 2 +++ storeByteOffset 482 +++
        loadArgumentIndex 2 +++ storeByteOffset 2185 +++ rest) post := by
  have h8 := officialConstructorPatchInvariant7.runCompiled_write
    (i := ⟨2, by decide⟩) (offset := 2185) (pushGas := 3)
    (G := G) (value := officialParams.maxPauseDuration)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory8] using hrest)
  have h7 := officialConstructorPatchInvariant6.runCompiled_write
    (i := ⟨2, by decide⟩) (offset := 482) (pushGas := 3)
    (G := G + 12) (value := officialParams.maxPauseDuration)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory7] using h8)
  have h6 := officialConstructorPatchInvariant5.runCompiled_write
    (i := ⟨1, by decide⟩) (offset := 937) (pushGas := 3)
    (G := G + 24) (value := officialParams.minPauseDuration)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory6] using h7)
  have h5 := officialConstructorPatchInvariant4.runCompiled_write
    (i := ⟨1, by decide⟩) (offset := 441) (pushGas := 3)
    (G := G + 36) (value := officialParams.minPauseDuration)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory5] using h6)
  exact h5

end LidoCircuitBreaker

end Blanc
