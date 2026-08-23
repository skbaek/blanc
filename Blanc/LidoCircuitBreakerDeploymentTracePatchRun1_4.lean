-- LidoCircuitBreakerDeploymentTracePatchRun1_4.lean : constructor patches one through four.
--
-- The first four concrete patch states and their gas-exact reverse walk.

import Blanc.LidoCircuitBreakerDeploymentTracePatchCore

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

def officialConstructorPatchMemory1 : Mem :=
  officialConstructorCopiedMemory.write 398 officialParams.admin.toBytes

def officialConstructorPatchMemory2 : Mem :=
  officialConstructorPatchMemory1.write 1318 officialParams.admin.toBytes

def officialConstructorPatchMemory3 : Mem :=
  officialConstructorPatchMemory2.write 2057 officialParams.admin.toBytes

def officialConstructorPatchMemory4 : Mem :=
  officialConstructorPatchMemory3.write 2144 officialParams.admin.toBytes
private def officialConstructorPatchInvariant1 :
    ConstructorPatchInvariant officialConstructorPatchMemory1 :=
  officialConstructorCopiedMemory_invariant.write 398 officialParams.admin
    (by decide) (by decide)

private def officialConstructorPatchInvariant2 :
    ConstructorPatchInvariant officialConstructorPatchMemory2 :=
  officialConstructorPatchInvariant1.write 1318 officialParams.admin
    (by decide) (by decide)

private def officialConstructorPatchInvariant3 :
    ConstructorPatchInvariant officialConstructorPatchMemory3 :=
  officialConstructorPatchInvariant2.write 2057 officialParams.admin
    (by decide) (by decide)

def officialConstructorPatchInvariant4 :
    ConstructorPatchInvariant officialConstructorPatchMemory4 :=
  officialConstructorPatchInvariant3.write 2144 officialParams.admin
    (by decide) (by decide)

theorem officialConstructorPatchLine1_4_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory4, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorCopiedMemory, G + 44⟩)
      (loadArgumentIndex 0 +++ storeByteOffset 398 +++
        loadArgumentIndex 0 +++ storeByteOffset 1318 +++
        loadArgumentIndex 0 +++ storeByteOffset 2057 +++
        loadArgumentIndex 0 +++ storeByteOffset 2144 +++ rest) post := by
  have h4 := officialConstructorPatchInvariant3.runCompiled_write
    (i := ⟨0, by decide⟩) (offset := 2144) (pushGas := 2)
    (G := G) (value := officialParams.admin)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory4] using hrest)
  have h3 := officialConstructorPatchInvariant2.runCompiled_write
    (i := ⟨0, by decide⟩) (offset := 2057) (pushGas := 2)
    (G := G + 11) (value := officialParams.admin)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory3] using h4)
  have h2 := officialConstructorPatchInvariant1.runCompiled_write
    (i := ⟨0, by decide⟩) (offset := 1318) (pushGas := 2)
    (G := G + 22) (value := officialParams.admin)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory2] using h3)
  have h1 := officialConstructorCopiedMemory_invariant.runCompiled_write
    (i := ⟨0, by decide⟩) (offset := 398) (pushGas := 2)
    (G := G + 33) (value := officialParams.admin)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory1] using h2)
  exact h1

end LidoCircuitBreaker

end Blanc
