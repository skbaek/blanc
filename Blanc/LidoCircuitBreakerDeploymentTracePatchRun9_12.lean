-- LidoCircuitBreakerDeploymentTracePatchRun9_12.lean : constructor patches nine through twelve.
--
-- The final four concrete patch states and their gas-exact reverse walk.

import Blanc.LidoCircuitBreakerDeploymentTracePatchRun5_8

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

def officialConstructorPatchMemory9 : Mem :=
  officialConstructorPatchMemory8.write 732
    officialParams.minHeartbeatInterval.toBytes

def officialConstructorPatchMemory10 : Mem :=
  officialConstructorPatchMemory9.write 1361
    officialParams.minHeartbeatInterval.toBytes

def officialConstructorPatchMemory11 : Mem :=
  officialConstructorPatchMemory10.write 896
    officialParams.maxHeartbeatInterval.toBytes

def officialConstructorPatchMemory12 : Mem :=
  officialConstructorPatchMemory11.write 1402
    officialParams.maxHeartbeatInterval.toBytes
private def officialConstructorPatchInvariant9 :
    ConstructorPatchInvariant officialConstructorPatchMemory9 :=
  officialConstructorPatchInvariant8.write 732
    officialParams.minHeartbeatInterval (by decide) (by decide)

private def officialConstructorPatchInvariant10 :
    ConstructorPatchInvariant officialConstructorPatchMemory10 :=
  officialConstructorPatchInvariant9.write 1361
    officialParams.minHeartbeatInterval (by decide) (by decide)

private def officialConstructorPatchInvariant11 :
    ConstructorPatchInvariant officialConstructorPatchMemory11 :=
  officialConstructorPatchInvariant10.write 896
    officialParams.maxHeartbeatInterval (by decide) (by decide)

def officialConstructorPatchInvariant12 :
    ConstructorPatchInvariant officialConstructorPatchMemory12 :=
  officialConstructorPatchInvariant11.write 1402
    officialParams.maxHeartbeatInterval (by decide) (by decide)

/-- Memory after the constructor's twelve source-ordered immutable writes. -/
def officialConstructorPatchedMemory : Mem :=
  officialConstructorPatchMemory12

def officialConstructorPatchedImage : Bytes :=
  officialConstructorPatchInvariant12.image

theorem officialConstructorPatchLine9_12_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory12, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory8, G + 48⟩)
      (loadArgumentIndex 3 +++ storeByteOffset 732 +++
        loadArgumentIndex 3 +++ storeByteOffset 1361 +++
        loadArgumentIndex 4 +++ storeByteOffset 896 +++
        loadArgumentIndex 4 +++ storeByteOffset 1402 +++ rest) post := by
  have h12 := officialConstructorPatchInvariant11.runCompiled_write
    (i := ⟨4, by decide⟩) (offset := 1402) (pushGas := 3)
    (G := G) (value := officialParams.maxHeartbeatInterval)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory12] using hrest)
  have h11 := officialConstructorPatchInvariant10.runCompiled_write
    (i := ⟨4, by decide⟩) (offset := 896) (pushGas := 3)
    (G := G + 12) (value := officialParams.maxHeartbeatInterval)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory11] using h12)
  have h10 := officialConstructorPatchInvariant9.runCompiled_write
    (i := ⟨3, by decide⟩) (offset := 1361) (pushGas := 3)
    (G := G + 24) (value := officialParams.minHeartbeatInterval)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory10] using h11)
  have h9 := officialConstructorPatchInvariant8.runCompiled_write
    (i := ⟨3, by decide⟩) (offset := 732) (pushGas := 3)
    (G := G + 36) (value := officialParams.minHeartbeatInterval)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory9] using h10)
  exact h9

end LidoCircuitBreaker

end Blanc
