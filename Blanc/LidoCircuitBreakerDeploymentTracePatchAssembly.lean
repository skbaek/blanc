-- LidoCircuitBreakerDeploymentTracePatchAssembly.lean : complete constructor patch execution.
--
-- The compiled four-write groups are composed with CODECOPY into the public patch-walk theorem.

import Blanc.LidoCircuitBreakerDeploymentTracePatchEquivalence

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

private def officialConstructorPatchLine : Line :=
  loadArgumentIndex 0 ++ storeByteOffset 398 ++
  loadArgumentIndex 0 ++ storeByteOffset 1318 ++
  loadArgumentIndex 0 ++ storeByteOffset 2057 ++
  loadArgumentIndex 0 ++ storeByteOffset 2144 ++
  loadArgumentIndex 1 ++ storeByteOffset 441 ++
  loadArgumentIndex 1 ++ storeByteOffset 937 ++
  loadArgumentIndex 2 ++ storeByteOffset 482 ++
  loadArgumentIndex 2 ++ storeByteOffset 2185 ++
  loadArgumentIndex 3 ++ storeByteOffset 732 ++
  loadArgumentIndex 3 ++ storeByteOffset 1361 ++
  loadArgumentIndex 4 ++ storeByteOffset 896 ++
  loadArgumentIndex 4 ++ storeByteOffset 1402

private theorem patchRuntimeLine_official_eq :
    patchRuntimeLine constructorRuntimeBase =
      officialConstructorPatchLine := by
  rcases constructor_immutable_word_offsets_exact with
    ⟨hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat⟩
  simp only [patchRuntimeLine, patchFieldLine, immutableParameters,
    List.flatMap_cons, List.flatMap_nil, hadmin, hminPause, hmaxPause,
    hminHeartbeat, hmaxHeartbeat, patchArgumentIndex,
    officialConstructorPatchLine, constructorRuntimeBase,
    constructorArgumentBytes, List.append_nil,
    List.append_assoc]
private theorem officialConstructorPatchLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchedMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorCopiedMemory, G + 140⟩)
      (officialConstructorPatchLine +++ rest) post := by
  have hrest12 : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory12, G⟩)
      rest post := by
    rw [officialConstructorPatchMemory12_eq_patched]
    exact hrest
  have h9 := officialConstructorPatchLine9_12_runCompiled hrest12
  have h5 := officialConstructorPatchLine5_8_runCompiled (G := G + 48) h9
  have h1 := officialConstructorPatchLine1_4_runCompiled (G := G + 96) h5
  simpa only [officialConstructorPatchLine, prepend_append] using h1

theorem officialConstructorCopyPatch_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hcode : sevm.code.toList = officialFullCreateInput)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchedMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[(224 : B256), (616 : B256), (4282 : B256)],
          officialConstructorDecodedMemory, G + 985⟩)
      (codecopy ::: patchRuntimeLine constructorRuntimeBase +++ rest) post := by
  have hpatch := officialConstructorPatchLine_runCompiled hrest
  refine Func.RunCompiled.next
    (devm' := base.setMach
      ⟨[], officialConstructorCopiedMemory, G + 140⟩) ?_ ?_
  · have hstep := Ninst.runCompiled_codecopy_of
      (sevm := sevm)
      (devm := base.setMach
        ⟨[(224 : B256), (616 : B256), (4282 : B256)],
          officialConstructorDecodedMemory, G + 985⟩)
      (di := (224 : B256)) (si := (616 : B256)) (sz := (4282 : B256))
      (s := []) (c := 845) (G := G + 140)
      (M := officialConstructorCopiedMemory)
      (by simp only [Devm.stack_setMach])
      (by
        simp only [show (224 : B256).toNat = 224 by decide,
          show (4282 : B256).toNat = 4282 by decide]
        exact Devm.extCost_add_of_size
          (a := gVerylow + gasCopy * ceilDiv 4282 32)
          officialConstructorDecodedMemory_size (by decide))
      (by
        simp only [Devm.memory_setMach,
          show (224 : B256).toNat = 224 by decide,
          show (616 : B256).toNat = 616 by decide,
          show (4282 : B256).toNat = 4282 by decide]
        rw [officialFullCreateInput_slice_runtimeTemplate hcode]
        rfl)
      (by simp only [Devm.gasLeft_setMach])
    simpa only [Devm.setMach_setMach] using hstep
  · rw [patchRuntimeLine_official_eq]
    exact hpatch

end LidoCircuitBreaker

end Blanc
