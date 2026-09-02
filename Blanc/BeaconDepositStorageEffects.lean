import Blanc.BeaconDepositInsert
import Blanc.BeaconDepositWriteSites
import Blanc.ForwardStorageEffects

/-!
# Beacon deposit exact retained storage effects

Selected-path effect certificates for the two successful runtime stores.
These proofs retain successful no-op SSTOREs and therefore state chronology,
not merely the final storage delta.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

private theorem sha64_success_suffix_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {K : Nat}
    {stack : List B256} {success : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hge : (Nat.toB256 base.returnData.length <? (32 : B256)) = 0)
    (tail : Func.StorageEffectRun fs sevm
      (base.setMach ⟨stack, base.memory, K⟩) success ex effects)
    (hroom : stack.length < 1019) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨1 :: stack, base.memory, K + 37⟩)
      (Ninst.iszero :::
        (.call bubbleRevertSlot) <?>
        (returnDataShorterThan 32 +++
          ((.call emptyRevertSlot) <?> success))) ex effects := by
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_unary
      (sevm := sevm)
      (devm := base.setMach
        ⟨1 :: stack, base.memory, K + 37⟩)
      (r := .iszero) (f := (B256.eqCheck · 0))
      (cost := gVerylow) (x := 1) (v := 0) (s := stack)
      (G := K + 34)
      (by rintro ⟨⟩) rfl rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.zero
    (by simp only [Devm.stack_setMach, List.length_cons]; omega)
    (Devm.popBurnBy_setMach (s := stack) (G := K + 21)
      (by simp only [Devm.stack_setMach])
      (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh]))
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  change Func.StorageEffectRun fs sevm _
    (Ninst.pushB256 32 ::: Ninst.returndatasize ::: Ninst.lt :::
      ((.call emptyRevertSlot) <?> success)) ex effects
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (w := 32) (c := gVerylow)
      (G := K + 18)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushItem
      (sevm := sevm)
      (devm := base.setMach
        ⟨32 :: stack, base.memory, K + 18⟩)
      (r := .returndatasize)
      (x := Nat.toB256 base.returnData.length)
      (cost := gBase) (G := K + 16)
      (by rintro ⟨⟩) rfl
      (by simp only [Devm.gasLeft_setMach, gBase])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary
      (sevm := sevm)
      (devm := base.setMach
        ⟨Nat.toB256 base.returnData.length :: 32 :: stack,
          base.memory, K + 16⟩)
      (r := .lt) (f := B256.ltCheck)
      (cost := gVerylow)
      (x := Nat.toB256 base.returnData.length) (y := 32)
      (v := 0) (s := stack) (G := K + 13)
      (by rintro ⟨⟩) rfl rfl hge
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.zero
    (by simp only [Devm.stack_setMach, List.length_cons]; omega)
    (Devm.popBurnBy_setMach (s := stack) (G := K)
      (by simp only [Devm.stack_setMach])
      (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh]))
  simpa only [Devm.setMach_setMach, Devm.memory_setMach] using tail

/-- The successful fixed-width SHA-256 wrapper is storage-effect neutral and
threads the exact effects of its continuation.  The `STATICCALL` step keeps
its explicit childless witness. -/
theorem sha64_success_prefix_storageEffectRun_ext
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {inputWord outputWord : B256} {stack : List B256}
    {success : Func} {K ext : Nat}
    {effects : List (Adr × B256 × B256)}
    (hext : base.extCost
      [⟨(inputWord * 32).toNat, 64⟩,
        ⟨(outputWord * 32).toNat, 32⟩] = ext)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 221 + ext < 2 ^ 256)
    (hroom : stack.length < 1019) :
    ∃ callPost,
      callPost.stack = 1 :: stack ∧
      callPost.memory = (base.memory.extends
        [⟨(inputWord * 32).toNat, 64⟩,
          ⟨(outputWord * 32).toNat, 32⟩]).write
        (outputWord * 32).toNat
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes ∧
      callPost.gasLeft = K + 37 ∧
      callPost.returnData =
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes ∧
      (∀ a, Devm.getStor callPost a = Devm.getStor base a) ∧
      (∀ a, callPost.getCode a = base.getCode a) ∧
      callPost.accessedAddresses = base.accessedAddresses ∧
      callPost.accessedStorageKeys = base.accessedStorageKeys ∧
      callPost.logs = base.logs ∧
      callPost.output = base.output ∧
      callPost.error = base.error ∧
      (∃ stmid,
        base.state.subBal sevm.currentTarget 0 = some stmid ∧
        callPost.state = stmid.addBal 2 0) ∧
      ∀ {ex : Execution},
        Func.StorageEffectRun fs sevm
          (callPost.setMach ⟨stack, callPost.memory, K⟩)
          success ex effects →
        Func.StorageEffectRun fs sevm
          (base.setMach
            ⟨stack, base.memory,
              K + sha64SuccessCost inputWord outputWord + ext⟩)
          (sha64 inputWord outputWord success) ex effects := by
  let callPre := base.setMach
    ⟨Nat.toB256 (K + 221 + ext) :: (2 : B256) ::
      (inputWord * 32) :: (64 : B256) ::
      (outputWord * 32) :: (32 : B256) :: stack,
      base.memory, K + 221 + ext⟩
  obtain ⟨callPost, hstat, hstack, hmemory, hgas, hreturn,
      hstorage, hcode, haddresses, hkeys,
      hlogs, houtput, herror, stmid, hsub, hstate⟩ :=
    Ninst.childlessRunCompiled_staticcall_sha256_64_warm_ext
      (sevm := sevm) (devm := callPre)
      (iiw := inputWord * 32) (oiw := outputWord * 32)
      (s := stack) (G := K + 221 + ext) (ext := ext)
      (by simp only [callPre, Devm.stack_setMach])
      (by simp only [callPre, Devm.gasLeft_setMach])
      (by simpa only [callPre, Devm.extCost, Devm.memory_setMach] using hext)
      (by simpa only [callPre, Devm.getCode_setMach] using hnodeleg)
      (by
        change (2 : Adr) ∈ base.accessedAddresses
        exact hwarm)
      hpre hdepth (by omega) hbound (by omega)
  have hgas' : callPost.gasLeft = K + 37 := by omega
  have hmemory' :
      callPost.memory = (base.memory.extends
        [⟨(inputWord * 32).toNat, 64⟩,
          ⟨(outputWord * 32).toNat, 32⟩]).write
        (outputWord * 32).toNat
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes := by
    simpa only [callPre, Devm.memory_setMach] using hmemory
  have hreturn' :
      callPost.returnData =
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes := by
    simpa only [callPre, Devm.memory_setMach] using hreturn
  have hstorage' : ∀ a,
      Devm.getStor callPost a = Devm.getStor base a := by
    intro a
    calc
      Devm.getStor callPost a = Devm.getStor callPre a := hstorage a
      _ = Devm.getStor base a := by rfl
  have hcode' : ∀ a, callPost.getCode a = base.getCode a := by
    intro a
    calc
      callPost.getCode a = callPre.getCode a := hcode a
      _ = base.getCode a := by rfl
  have haddresses' :
      callPost.accessedAddresses = base.accessedAddresses := by
    calc
      callPost.accessedAddresses = callPre.accessedAddresses := haddresses
      _ = base.accessedAddresses := by rfl
  have hkeys' :
      callPost.accessedStorageKeys = base.accessedStorageKeys := by
    calc
      callPost.accessedStorageKeys = callPre.accessedStorageKeys := hkeys
      _ = base.accessedStorageKeys := by rfl
  have hlogs' : callPost.logs = base.logs := by
    calc
      callPost.logs = callPre.logs := hlogs
      _ = base.logs := by rfl
  have houtput' : callPost.output = base.output := by
    calc
      callPost.output = callPre.output := houtput
      _ = base.output := by rfl
  have herror' : callPost.error = base.error := by
    calc
      callPost.error = callPre.error := herror
      _ = base.error := by rfl
  have hsub' : base.state.subBal sevm.currentTarget 0 = some stmid := by
    change base.state.subBal sevm.currentTarget 0 = some stmid at hsub
    exact hsub
  refine ⟨callPost, hstack, hmemory', hgas', hreturn',
    hstorage', hcode', haddresses', hkeys',
    hlogs', houtput', herror', ⟨stmid, hsub', hstate⟩, ?_⟩
  intro ex tail
  have hge :
      (Nat.toB256 callPost.returnData.length <? (32 : B256)) = 0 := by
    rw [hreturn', B256.length_toBytes]
    decide +kernel
  have suffix : Func.StorageEffectRun fs sevm
      (callPost.setMach ⟨1 :: stack, callPost.memory, K + 37⟩)
      (Ninst.iszero :::
        (.call bubbleRevertSlot) <?>
        (returnDataShorterThan 32 +++
          ((.call emptyRevertSlot) <?> success))) ex effects :=
    sha64_success_suffix_storageEffectRun hge tail hroom
  let c32 := pushCost ((32 : B256).toBytes.sig)
  let cout := pushCost ((outputWord * 32).toBytes.sig)
  let c64 := pushCost ((64 : B256).toBytes.sig)
  let cin := pushCost ((inputWord * 32).toBytes.sig)
  let c2 := pushCost ((2 : B256).toBytes.sig)
  simp only [sha64, pushList, List.map, prepend]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_pushB256
      (sevm := sevm)
      (devm := base.setMach
        ⟨stack, base.memory,
          K + sha64SuccessCost inputWord outputWord + ext⟩)
      (w := (32 : B256)) (c := c32)
      (G := K + (cout + c64 + cin + c2 + 223) + ext)
      rfl
      (by
        simp only [Devm.gasLeft_setMach, sha64SuccessCost,
          c32, cout, c64, cin, c2]
        omega)
      (by simp only [Devm.stack_setMach]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_pushB256
      (w := outputWord * 32) (c := cout)
      (G := K + (c64 + cin + c2 + 223) + ext) rfl
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_pushB256
      (w := (64 : B256)) (c := c64)
      (G := K + (cin + c2 + 223) + ext) rfl
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_pushB256
      (w := inputWord * 32) (c := cin)
      (G := K + (c2 + 223) + ext) rfl
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_pushB256
      (w := (2 : B256)) (c := c2) (G := K + 223 + ext) rfl
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_gas
      (G := K + 221 + ext)
      (by simp only [Devm.gasLeft_setMach, gBase]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next hstat
  have hpost : callPost.setMach
      ⟨1 :: stack, callPost.memory, K + 37⟩ = callPost := by
    apply Devm.ext
    · apply Mach.ext
      · exact hstack.symm
      · rfl
      · exact hgas'.symm
    · rfl
    · rfl
  rw [hpost] at suffix
  simpa only [callPre, Devm.stack_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach] using suffix

/-- Covered-memory compatibility form of
`sha64_success_prefix_storageEffectRun_ext`. -/
theorem sha64_success_prefix_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {inputWord outputWord : B256} {stack : List B256}
    {success : Func} {K : Nat}
    {effects : List (Adr × B256 × B256)}
    (hcovered : memExtsSize base.memory.size
      [⟨(inputWord * 32).toNat, 64⟩,
        ⟨(outputWord * 32).toNat, 32⟩] = base.memory.size)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 221 < 2 ^ 256)
    (hroom : stack.length < 1019) :
    ∃ callPost,
      callPost.stack = 1 :: stack ∧
      callPost.memory = base.memory.write (outputWord * 32).toNat
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes ∧
      callPost.gasLeft = K + 37 ∧
      callPost.returnData =
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes ∧
      (∀ a, Devm.getStor callPost a = Devm.getStor base a) ∧
      (∀ a, callPost.getCode a = base.getCode a) ∧
      callPost.accessedAddresses = base.accessedAddresses ∧
      callPost.accessedStorageKeys = base.accessedStorageKeys ∧
      callPost.logs = base.logs ∧
      callPost.output = base.output ∧
      callPost.error = base.error ∧
      (∃ stmid,
        base.state.subBal sevm.currentTarget 0 = some stmid ∧
        callPost.state = stmid.addBal 2 0) ∧
      ∀ {ex : Execution},
        Func.StorageEffectRun fs sevm
          (callPost.setMach ⟨stack, callPost.memory, K⟩)
          success ex effects →
        Func.StorageEffectRun fs sevm
          (base.setMach
            ⟨stack, base.memory,
              K + sha64SuccessCost inputWord outputWord⟩)
          (sha64 inputWord outputWord success) ex effects := by
  have hext : base.extCost
      [⟨(inputWord * 32).toNat, 64⟩,
        ⟨(outputWord * 32).toNat, 32⟩] = 0 := by
    simp only [Devm.extCost, hcovered]
    omega
  simpa only [Nat.add_zero, Mem.extends_covered hcovered] using
    (sha64_success_prefix_storageEffectRun_ext
      (ext := 0) (effects := effects) hext hnodeleg hwarm hpre hdepth
      (by simpa using hbound) hroom)

/-- Shift the insertion size, increment its height, and re-enter the loop
without adding a retained storage effect. -/
theorem insertionContinuation_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount size node height : B256}
    {K : Nat} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hmem : InsertionMemoryCarrier memory oldCount size node)
    (hloop : fs[insertionLoopSlot]? = some insertionLoop)
    (tail : Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[height + 1], memory.write 608 (size >>> 1).toBytes, K⟩)
      insertionLoop ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[height], memory, K + 36⟩)
      insertionContinuation ex effects := by
  have hoff : (shiftedSizeWord * 32).toNat = 608 := by
    decide +kernel
  have hpushOff :
      pushCost (shiftedSizeWord * 32).toBytes.sig = gVerylow := by
    decide +kernel
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hsize : 640 ≤ memory.size := by
    rw [hmem.size_eq]
    omega
  have hread : Bytes.toB256 (memory.read 608 32).1 = size :=
    hmem.readShiftedSize
  unfold insertionContinuation loadWord mstoreAt
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256
      (w := shiftedSizeWord * 32) (c := gVerylow) (G := K + 33)
      hpushOff
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hmload :=
    Ninst.runCompiled_mload_of
      (sevm := sevm)
      (devm := base.setMach
        ⟨(shiftedSizeWord * 32) :: [height], memory, K + 33⟩)
      (i := shiftedSizeWord * 32) (v := size) (s := [height])
      (c := gVerylow) (G := K + 30) (M := memory) rfl
      (by
        rw [Devm.extCost_zero_of_le hmod (by rw [hoff]; omega)]
        omega)
      (by
        rw [Devm.memory_setMach, hoff]
        exact hread)
      (by
        rw [Devm.memory_setMach, hoff,
          Mem.read_snd_eq_self (memExtSize_of_le hmod (by omega))])
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega)
  apply Func.StorageEffectRun.next_effectNeutral hmload
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256
      (w := (1 : B256)) (c := gVerylow) (G := K + 27)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary
      (r := .shr) (f := fun x y => y >>> x.toNat)
      (cost := gVerylow) (G := K + 24)
      (x := (1 : B256)) (y := size) (v := size >>> 1)
      (s := [height])
      (by rintro ⟨⟩) rfl rfl
      (by simp only [show (1 : B256).toNat = 1 by decide +kernel])
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256
      (w := shiftedSizeWord * 32) (c := gVerylow) (G := K + 21)
      hpushOff
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_mstore_of
      (i := shiftedSizeWord * 32) (v := size >>> 1)
      (s := [height]) (G := K + 18) (e := 0) rfl
      (Devm.extCost_zero_of_le hmod (by rw [hoff]; omega))
      (by simp only [Devm.gasLeft_setMach, gVerylow]) rfl)
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, hoff]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256
      (w := (1 : B256)) (c := gVerylow) (G := K + 15)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary
      (r := .add) (f := (· + ·))
      (cost := gVerylow) (G := K + 12)
      (x := (1 : B256)) (y := height) (v := height + 1)
      (s := [])
      (by rintro ⟨⟩) rfl rfl
      (B256.add_comm (xs := (1 : B256)) (ys := height))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.call hloop
    (by simp only [Devm.stack_setMach, List.length_cons,
      List.length_nil]; omega)
    (Devm.burnBy_setMach_gas (G := K)
      (by simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]))
  simpa only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach] using tail

/-- Run the childless SHA-256 wrapper and the insertion continuation while
threading the recursive loop's retained storage chronology unchanged. -/
theorem insertionShaTail_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {oldCount size left right height : B256} {K : Nat}
    {effects : List (Adr × B256 × B256)}
    (pair : InsertionPairMemoryCarrier
      base.memory oldCount size left right)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 269 < 2 ^ 256)
    (hinsertionContinuation :
      fs[insertionContinuationSlot]? = some insertionContinuation)
    (hinsertionLoop : fs[insertionLoopSlot]? = some insertionLoop) :
    ∃ callPost,
      callPost.stack = 1 :: [height] ∧
      callPost.memory = base.memory.write 640
        (hashPair Bytes.sha256 left right).toBytes ∧
      Nonempty (InsertionMemoryCarrier callPost.memory oldCount size
        (hashPair Bytes.sha256 left right)) ∧
      callPost.gasLeft = K + 85 ∧
      callPost.returnData = (hashPair Bytes.sha256 left right).toBytes ∧
      (∀ a, Devm.getStor callPost a = Devm.getStor base a) ∧
      (∀ a, callPost.getCode a = base.getCode a) ∧
      callPost.accessedAddresses = base.accessedAddresses ∧
      callPost.accessedStorageKeys = base.accessedStorageKeys ∧
      callPost.logs = base.logs ∧
      callPost.output = base.output ∧
      callPost.error = base.error ∧
      ∀ {ex : Execution},
        Func.StorageEffectRun fs sevm
          (callPost.setMach
            ⟨[height + 1],
              callPost.memory.write 608 (size >>> 1).toBytes, K⟩)
          insertionLoop ex effects →
        Func.StorageEffectRun fs sevm
          (base.setMach ⟨[height], base.memory, K + 285⟩)
          (sha64 0 nodeWord (.call insertionContinuationSlot)) ex effects := by
  have hzero : ((0 : B256) * 32).toNat = 0 := by
    decide +kernel
  have hnode : (nodeWord * 32).toNat = 640 := by
    decide +kernel
  have hcovered : memExtsSize base.memory.size
      [⟨((0 : B256) * 32).toNat, 64⟩,
        ⟨(nodeWord * 32).toNat, 32⟩] = base.memory.size := by
    rw [hzero, hnode, pair.size_eq]
    decide +kernel
  obtain ⟨callPost, hstack, hmemory, hgas, hreturn,
      hstorage, hcode, haddresses, hkeys,
      hlogs, houtput, herror, _htransfer, lift⟩ :=
    sha64_success_prefix_storageEffectRun
      (fs := fs) (sevm := sevm) (base := base)
      (inputWord := 0) (outputWord := nodeWord)
      (stack := [height]) (success := .call insertionContinuationSlot)
      (K := K + 48) (effects := effects)
      hcovered hnodeleg hwarm hpre hdepth (by omega)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hmemory' :
      callPost.memory = base.memory.write 640
        (hashPair Bytes.sha256 left right).toBytes := by
    simpa only [hzero, hnode, pair.shaInput, hashPair] using hmemory
  have hreturn' :
      callPost.returnData = (hashPair Bytes.sha256 left right).toBytes := by
    simpa only [hzero, pair.shaInput, hashPair] using hreturn
  have hgas' : callPost.gasLeft = K + 85 := by
    omega
  have hcarrierBase := pair.finishHash
  have hcarrier : InsertionMemoryCarrier callPost.memory oldCount size
      (hashPair Bytes.sha256 left right) := by
    rw [hmemory']
    exact hcarrierBase
  refine ⟨callPost, hstack, hmemory', ⟨hcarrier⟩, hgas', hreturn',
    hstorage, hcode, haddresses, hkeys,
    hlogs, houtput, herror, ?_⟩
  intro ex tail
  have hinsertion : Func.StorageEffectRun fs sevm
      (callPost.setMach
        ⟨[height], callPost.memory, K + 36⟩)
      insertionContinuation ex effects :=
    insertionContinuation_storageEffectRun
      hcarrier hinsertionLoop tail
  have hsuccess : Func.StorageEffectRun fs sevm
      (callPost.setMach
        ⟨[height], callPost.memory, K + 48⟩)
      (.call insertionContinuationSlot) ex effects := by
    apply Func.StorageEffectRun.call hinsertionContinuation
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)
      (Devm.burnBy_setMach_gas (G := K + 36)
        (by simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]))
    simpa only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach] using hinsertion
  have whole := lift hsuccess
  simpa only [sha64SuccessCost_zero_node] using whole

/-- The first-live insertion leaf contributes exactly its selected branch
write and no other retained storage effect. -/
theorem insertionLive_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {K : Nat}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hsentry : gCallStipend <
      K + 2 + sstoreCost sevm base (branchBase + height) node)
    (hstatic : sevm.isStatic = false) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[height], memory,
          K + 20 + sstoreCost sevm base (branchBase + height) node⟩)
      insertionLive
      (.ok ((afterSstore sevm base (branchBase + height) node).setMach
        ⟨[], memory, K⟩))
      [(sevm.currentTarget, branchBase + height, node)] := by
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hnodeRead : Bytes.toB256 (memory.read 640 32).1 = node :=
    hmem.readNode
  have hnodeMem : (memory.read 640 32).2 = memory := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · exact hmod
    · rw [hmem.size_eq]
      omega
  simp only [insertionLive, loadWord, prepend,
    show (nodeWord * 32 : B256) = 640 by decide +kernel]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_dup (n := 0) (w := height)
      (G := K + 17 + sstoreCost sevm base (branchBase + height) node)
      rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_pushB256 (w := branchBase) (c := 3)
      (G := K + 14 + sstoreCost sevm base (branchBase + height) node)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_binary (r := .add) (f := (· + ·))
      (cost := gVerylow) (x := branchBase) (y := height)
      (v := branchBase + height) (s := [height])
      (G := K + 11 + sstoreCost sevm base (branchBase + height) node)
      (by rintro ⟨⟩) rfl rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [List.length_cons, List.length_nil]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_pushB256 (w := 640) (c := 3)
      (G := K + 8 + sstoreCost sevm base (branchBase + height) node)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hmload :=
    Ninst.runCompiled_mload_of
      (sevm := sevm)
      (devm := base.setMach
        ⟨[640, branchBase + height, height], memory,
          K + 8 + sstoreCost sevm base (branchBase + height) node⟩)
      (i := 640) (v := node) (s := (branchBase + height) :: [height])
      (c := 3)
      (G := K + 5 + sstoreCost sevm base (branchBase + height) node)
      (M := memory) rfl
      (by
        rw [Devm.extCost_zero_of_le hmod (by
          rw [hmem.size_eq]
          decide +kernel)]
        decide)
      hnodeRead hnodeMem
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [List.length_cons, List.length_nil]; omega)
  apply Func.StorageEffectRun.next_of_not_exec
    hmload
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_swap (n := 0)
      (S := (branchBase + height) :: node :: [height])
      (G := K + 2 + sstoreCost sevm base (branchBase + height) node)
      rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_sstore_selected_setMach
      (base := base) (key := branchBase + height) (value := node)
      (stack := [height]) (memory := memory) (G := K + 2)
      hsentry hstatic)
    (by rintro operation ⟨⟩)
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_pop (G := K) rfl
      (by simp only [Devm.gasLeft_setMach, gBase]))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  exact Func.StorageEffectRun.last rfl

private theorem insertionLoopBit_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hroom : stack.length < 1022)
    (hinner : Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨((1 : B256) &&& shiftedSize) :: height :: stack, memory, K⟩)
      (insertionLive <?> insertionDead) ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨height :: stack, memory, K + 12⟩)
      insertionLoop ex effects := by
  have hoff : (shiftedSizeWord * 32).toNat = 608 := by
    decide +kernel
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hread : Bytes.toB256 (memory.read 608 32).1 = shiftedSize :=
    hmem.readShiftedSize
  have hreadMem : (memory.read 608 32).2 = memory := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · exact hmod
    · rw [hmem.size_eq]
      omega
  simp only [insertionLoop, loadWord, prepend]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_pushB256
      (w := shiftedSizeWord * 32) (c := 3) (G := K + 9)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_mload_of
      (i := shiftedSizeWord * 32) (v := shiftedSize)
      (s := height :: stack) (c := 3) (G := K + 6) (M := memory)
      rfl
      (by
        rw [Devm.extCost_zero_of_le hmod (by
          rw [hoff, hmem.size_eq]
          omega)]
        decide)
      (by
        rw [Devm.memory_setMach, hoff]
        exact hread)
      (by
        rw [Devm.memory_setMach, hoff]
        exact hreadMem)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [List.length_cons]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_pushB256 (w := 1) (c := 3) (G := K + 3)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_binary (r := .and) (f := B256.and)
      (cost := gVerylow) (x := 1) (y := shiftedSize)
      (v := (1 : B256) &&& shiftedSize) (s := height :: stack)
      (G := K)
      (by rintro ⟨⟩) rfl rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons]; omega))
    (by rintro operation ⟨⟩)
  simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hinner

private theorem insertionStageLoadedLeft_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height left : B256}
    {stack : List B256} {K : Nat} {rest : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hroom : stack.length < 1022)
    (tail : Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨height :: stack,
          (memory.write 0 left.toBytes).write 32 node.toBytes, K⟩)
      rest ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨left :: height :: stack, memory, K + 17⟩)
      (mstoreAt 0 +++ loadWord nodeWord +++ mstoreAt 1 +++ rest)
      ex effects := by
  let M1 := memory.write 0 left.toBytes
  have hmem1 : InsertionMemoryCarrier M1 oldCount shiftedSize node := by
    dsimp only [M1]
    exact hmem.writeBeforeRegisters 0 left.toBytes
      (by rw [B256.length_toBytes]; omega)
      (by rw [B256.length_toBytes]; omega)
  have hsize32 : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hnodeRead : Bytes.toB256 (M1.read 640 32).1 = node :=
    hmem1.readNode
  have hnodeMem : (M1.read 640 32).2 = M1 := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [hmem1.size_eq]
    · rw [hmem1.size_eq]
      omega
  simp only [loadWord, mstoreAt, prepend,
    show (0 * 32 : B256) = 0 by decide +kernel,
    show (nodeWord * 32 : B256) = 640 by decide +kernel,
    show (1 * 32 : B256) = 32 by decide +kernel]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (w := 0) (c := 2) (G := K + 15)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_mstore_of
      (i := 0) (v := left) (s := height :: stack)
      (G := K + 12) (e := 0) rfl
      (Devm.extCost_zero_of_le hsize32 (by
        rw [hmem.size_eq]
        decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow]) rfl)
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  change Func.StorageEffectRun fs sevm
    (base.setMach ⟨height :: stack, M1, K + 12⟩) _ ex effects
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (w := 640) (c := 3) (G := K + 9)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hmload :=
    Ninst.runCompiled_mload_of
      (sevm := sevm)
      (devm := base.setMach
        ⟨640 :: height :: stack, M1, K + 9⟩)
      (i := 640) (v := node) (s := height :: stack)
      (c := 3) (G := K + 6) (M := M1) rfl
      (by
        have hext :
            (base.setMach
              ⟨(640 : B256) :: height :: stack, M1, K + 9⟩).extCost
                [⟨(640 : B256).toNat, 32⟩] = 0 := by
          apply Devm.extCost_zero_of_le
          · rw [hmem1.size_eq]
          · rw [hmem1.size_eq]
            decide +kernel
        rw [hext]
        decide)
      hnodeRead hnodeMem
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [List.length_cons]; omega)
  apply Func.StorageEffectRun.next_effectNeutral hmload
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (w := 32) (c := 3) (G := K + 3)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_mstore_of
      (i := 32) (v := node) (s := height :: stack)
      (G := K) (e := 0) rfl
      (Devm.extCost_zero_of_le
        (by rw [hmem1.size_eq])
        (by rw [hmem1.size_eq]; decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow]) rfl)
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simpa only [Devm.setMach_setMach, Devm.memory_setMach, M1,
    show (32 : B256).toNat = 32 by decide +kernel] using tail

private theorem insertionDeadLoad_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {height left : B256} {stack : List B256}
    {K : Nat} {rest : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hval : base.getStorVal sevm.currentTarget
      (branchBase + height) = left)
    (hroom : stack.length < 1022)
    (tail : Func.StorageEffectRun fs sevm
      ((afterSload sevm base (branchBase + height)).setMach
        ⟨left :: height :: stack, memory, K + 17⟩)
      rest ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨height :: stack, memory,
          K + 26 + sloadCost sevm base (branchBase + height)⟩)
      (Ninst.dup 0 ::: Ninst.pushB256 branchBase :::
        Ninst.add ::: Ninst.sload ::: rest)
      ex effects := by
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_dup (n := 0) (w := height)
      (G := K + 23 + sloadCost sevm base (branchBase + height)) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (w := branchBase) (c := 3)
      (G := K + 20 + sloadCost sevm base (branchBase + height))
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary (r := .add) (f := (· + ·))
      (cost := gVerylow) (x := branchBase) (y := height)
      (v := branchBase + height) (s := height :: stack)
      (G := K + 17 + sloadCost sevm base (branchBase + height))
      (by rintro ⟨⟩) rfl rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [List.length_cons]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_sload_selected hval
      (by simp only [List.length_cons]; omega))
    (by rintro ⟨⟩)
    (by rintro operation ⟨⟩)
  exact tail

private theorem insertionDeadStage_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height left : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hval : base.getStorVal sevm.currentTarget
      (branchBase + height) = left)
    (hroom : stack.length < 1022)
    (tail : Func.StorageEffectRun fs sevm
      ((afterSload sevm base (branchBase + height)).setMach
        ⟨height :: stack,
          (memory.write 0 left.toBytes).write 32 node.toBytes, K⟩)
      (sha64 0 nodeWord (.call insertionContinuationSlot)) ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨height :: stack, memory,
          K + 26 + sloadCost sevm base (branchBase + height)⟩)
      insertionDead ex effects := by
  apply insertionDeadLoad_storageEffectRun hval hroom
  apply insertionStageLoadedLeft_storageEffectRun hmem hroom
  exact tail

private theorem insertionLoopDead_dispatch_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hbit : ((1 : B256) &&& shiftedSize) = 0)
    (hroom : stack.length < 1022)
    (arm : Func.StorageEffectRun fs sevm
      (base.setMach ⟨height :: stack, memory, K⟩)
      insertionDead ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨height :: stack, memory, K + 25⟩)
      insertionLoop ex effects := by
  apply insertionLoopBit_storageEffectRun hmem hroom
  apply Func.StorageEffectRun.zero
    (by simp only [Devm.stack_setMach, List.length_cons]; omega)
    (Devm.popBurnBy_setMach (s := height :: stack) (G := K)
      (by simp only [Devm.stack_setMach, hbit])
      (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh]))
  simpa only [Devm.setMach_setMach, Devm.memory_setMach] using arm

/-- One selected dead insertion iteration contributes no storage effect and
preserves the exact chronology of its recursive SHA/loop tail. -/
theorem insertionLoopDead_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height left : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hbit : ((1 : B256) &&& shiftedSize) = 0)
    (hval : base.getStorVal sevm.currentTarget
      (branchBase + height) = left)
    (hroom : stack.length < 1022)
    (tail : Func.StorageEffectRun fs sevm
      ((afterSload sevm base (branchBase + height)).setMach
        ⟨height :: stack,
          (memory.write 0 left.toBytes).write 32 node.toBytes, K⟩)
      (sha64 0 nodeWord (.call insertionContinuationSlot)) ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨height :: stack, memory,
          K + 51 + sloadCost sevm base (branchBase + height)⟩)
      insertionLoop ex effects := by
  let C := sloadCost sevm base (branchBase + height)
  have arm : Func.StorageEffectRun fs sevm
      (base.setMach ⟨height :: stack, memory, K + 26 + C⟩)
      insertionDead ex effects :=
    insertionDeadStage_storageEffectRun hmem hval hroom tail
  have dispatch := insertionLoopDead_dispatch_storageEffectRun
    (K := K + 26 + C) hmem hbit hroom arm
  have hgas : K + 26 + C + 25 = K + 51 + C := by omega
  rw [hgas] at dispatch
  simpa only [C] using dispatch

/-- Select the live insertion arm without changing its exact retained storage
effects. -/
theorem insertionLoopLive_dispatch_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hbit : ((1 : B256) &&& shiftedSize) ≠ 0)
    (hroom : stack.length < 1022)
    (harm : Func.StorageEffectRun fs sevm
      (base.setMach ⟨height :: stack, memory, K⟩)
      insertionLive ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨height :: stack, memory, K + 26⟩)
      insertionLoop ex effects := by
  apply insertionLoopBit_storageEffectRun hmem hroom
  apply Func.StorageEffectRun.succ hbit
    (by simp only [Devm.stack_setMach, List.length_cons]; omega)
    (Devm.popBurnBy_setMach
      (s := height :: stack) (G := K)
      (by simp only [Devm.stack_setMach])
      (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest]))
  simpa only [Devm.setMach_setMach, Devm.memory_setMach] using harm

/-- A first-live insertion loop retains exactly its selected branch-slot
write. -/
theorem insertionLoopLive_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {K : Nat}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hbit : ((1 : B256) &&& shiftedSize) ≠ 0)
    (hsentry : gCallStipend <
      K + 2 + sstoreCost sevm base (branchBase + height) node)
    (hstatic : sevm.isStatic = false) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[height], memory,
          K + 46 + sstoreCost sevm base (branchBase + height) node⟩)
      insertionLoop
      (.ok ((afterSstore sevm base (branchBase + height) node).setMach
        ⟨[], memory, K⟩))
      [(sevm.currentTarget, branchBase + height, node)] := by
  let C := sstoreCost sevm base (branchBase + height) node
  have harm : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[height], memory, K + 20 + C⟩)
      insertionLive
      (.ok ((afterSstore sevm base (branchBase + height) node).setMach
        ⟨[], memory, K⟩))
      [(sevm.currentTarget, branchBase + height, node)] :=
    insertionLive_storageEffectRun hmem hsentry hstatic
  have hdispatch :=
    insertionLoopLive_dispatch_storageEffectRun
      (K := K + 20 + C) hmem hbit
      (by simp only [List.length_nil]; omega) harm
  have hgas : K + 20 + C + 26 = K + 46 + C := by omega
  rw [hgas] at hdispatch
  simpa only [C] using hdispatch

/-- Increment and retain the deposit-count write before the exact effects of
the selected insertion-loop tail. -/
theorem commitDeposit_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount node : B256}
    {K : Nat} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hmem : InsertionStartMemoryCarrier memory oldCount node)
    (hsentry : gCallStipend <
      K + 14 + sstoreCost sevm base depositCountSlot (oldCount + 1))
    (hstatic : sevm.isStatic = false)
    (hloop : fs[insertionLoopSlot]? = some insertionLoop)
    (htail : Func.StorageEffectRun fs sevm
      ((afterSstore sevm base depositCountSlot (oldCount + 1)).setMach
        ⟨[0], memory.write 608 (oldCount + 1).toBytes, K⟩)
      insertionLoop ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[], memory,
          K + 38 +
            sstoreCost sevm base depositCountSlot (oldCount + 1)⟩)
      commitDeposit ex
      ((sevm.currentTarget, depositCountSlot, oldCount + 1) :: effects) := by
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have holdRead : Bytes.toB256 (memory.read 576 32).1 = oldCount :=
    hmem.readOldCount
  have holdMem : (memory.read 576 32).2 = memory := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · exact hmod
    · rw [hmem.size_eq]
      omega
  simp only [commitDeposit, loadWord, mstoreAt, prepend,
    show (oldCountWord * 32 : B256) = 576 by decide +kernel,
    show (shiftedSizeWord * 32 : B256) = 608 by decide +kernel]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_pushB256 (w := 576) (c := 3)
      (G := K + 35 +
        sstoreCost sevm base depositCountSlot (oldCount + 1))
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_nil]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  have hmload :=
    Ninst.runCompiled_mload_of
      (sevm := sevm)
      (devm := base.setMach
        ⟨[576], memory,
          K + 35 +
            sstoreCost sevm base depositCountSlot (oldCount + 1)⟩)
      (i := 576) (v := oldCount) (s := []) (c := 3)
      (G := K + 32 +
        sstoreCost sevm base depositCountSlot (oldCount + 1))
      (M := memory) rfl
      (by
        rw [Devm.extCost_zero_of_le hmod (by
          rw [hmem.size_eq]
          decide +kernel)]
        decide)
      holdRead holdMem
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [List.length_nil]; omega)
  apply Func.StorageEffectRun.next_of_not_exec hmload
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_pushB256 (w := 1) (c := 3)
      (G := K + 29 +
        sstoreCost sevm base depositCountSlot (oldCount + 1))
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_binary (r := .add) (f := (· + ·))
      (cost := gVerylow) (x := 1) (y := oldCount)
      (v := oldCount + 1) (s := [])
      (G := K + 26 +
        sstoreCost sevm base depositCountSlot (oldCount + 1))
      (by rintro ⟨⟩) rfl rfl
      (B256.add_comm (xs := (1 : B256)) (ys := oldCount))
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [List.length_nil]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_dup (n := 0) (w := oldCount + 1)
      (G := K + 23 +
        sstoreCost sevm base depositCountSlot (oldCount + 1))
      rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_pushB256 (w := 608) (c := 3)
      (G := K + 20 +
        sstoreCost sevm base depositCountSlot (oldCount + 1))
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_mstore_of
      (i := 608) (v := oldCount + 1) (s := [oldCount + 1])
      (G := K + 17 +
        sstoreCost sevm base depositCountSlot (oldCount + 1))
      (e := 0) rfl
      (Devm.extCost_zero_of_le hmod (by
        rw [hmem.size_eq]
        decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      rfl)
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach,
    show (608 : B256).toNat = 608 by decide +kernel]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_pushB256 (w := depositCountSlot) (c := 3)
      (G := K + 14 +
        sstoreCost sevm base depositCountSlot (oldCount + 1))
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_sstore_selected_setMach
      (base := base) (key := depositCountSlot) (value := oldCount + 1)
      (stack := [])
      (memory := memory.write 608 (oldCount + 1).toBytes)
      (G := K + 14) hsentry hstatic)
    (by rintro operation ⟨⟩)
  apply Func.StorageEffectRun.next_of_not_exec
    (Ninst.runCompiled_pushB256 (w := 0) (c := 2) (G := K + 12)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega))
    (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.call hloop
    (by simp only [Devm.stack_setMach, List.length_cons,
      List.length_nil]; omega)
    (Devm.burnBy_setMach_gas
      (G := K)
      (by simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest]))
  simpa only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach] using htail

end Blanc.BeaconDeposit
