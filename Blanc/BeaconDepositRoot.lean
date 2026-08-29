import Blanc.BeaconDepositRootMemory

/-!
# Beacon deposit root-fold compiled carriers

The executable root fold shifts its count register, advances its height, and
feeds a staged 64-byte pair through the warm SHA-256 precompile on every
iteration.  These carriers isolate the common 285-gas hash/continuation tail
from the live and dead staging arms.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Ninst

/-- Shift word 19, increment the loop height, and re-enter `rootLoop` in
exactly 36 gas. -/
theorem rootContinuation_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {height size : B256} {K : Nat} {ex : Execution}
    (hmod : memory.size % 32 = 0)
    (hsize : 640 ≤ memory.size)
    (hread : Bytes.toB256 (memory.read 608 32).1 = size)
    (hloop : fs[rootLoopSlot]? = some rootLoop)
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[height + 1], memory.write 608 (size >>> 1).toBytes, K⟩)
      rootLoop ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[height], memory, K + 36⟩)
      rootContinuation ex := by
  have hoff : (shiftedSizeWord * 32).toNat = 608 := by
    decide +kernel
  have hpushOff :
      pushCost (shiftedSizeWord * 32).toBytes.sig = gVerylow := by
    decide +kernel
  unfold rootContinuation loadWord mstoreAt
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := shiftedSizeWord * 32) (c := gVerylow) (G := K + 33)
      hpushOff
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mload_of
      (i := shiftedSizeWord * 32) (v := size) (s := [height])
      (c := gVerylow) (G := K + 30) (M := memory)
      rfl
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
      (by simp only [List.length_cons, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := (1 : B256)) (c := gVerylow) (G := K + 27)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary
      (r := .shr) (f := fun x y => y >>> x.toNat)
      (cost := gVerylow) (G := K + 24)
      (x := (1 : B256)) (y := size) (v := size >>> 1)
      (s := [height])
      (by rintro ⟨⟩) rfl rfl
      (by simp only [show (1 : B256).toNat = 1 by decide +kernel])
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := shiftedSizeWord * 32) (c := gVerylow) (G := K + 21)
      hpushOff
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mstore_of
      (i := shiftedSizeWord * 32) (v := size >>> 1)
      (s := [height]) (G := K + 18) (e := 0)
      rfl
      (Devm.extCost_zero_of_le hmod (by rw [hoff]; omega))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      rfl) ?_
  simp only [Devm.setMach_setMach, hoff]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := (1 : B256)) (c := gVerylow) (G := K + 15)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary
      (r := .add) (f := (· + ·))
      (cost := gVerylow) (G := K + 12)
      (x := (1 : B256)) (y := height) (v := height + 1)
      (s := [])
      (by rintro ⟨⟩) rfl rfl
      (B256.add_comm (xs := (1 : B256)) (ys := height))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_call' (G := K) hloop
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest])
    (by
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using htail)

/-- Run the shared SHA-256 and continuation tail from a staged pair.

The continuation hypothesis begins at the next `rootLoop` entry.  The exposed
memory carrier records the digest in word 20 before word 19 is shifted.
-/
theorem rootShaTail_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {oldCount size left right height : B256} {K : Nat}
    (pair : RootPairMemoryCarrier
      base.memory oldCount size left right)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 269 < 2 ^ 256)
    (hrootContinuation :
      fs[rootContinuationSlot]? = some rootContinuation)
    (hrootLoop : fs[rootLoopSlot]? = some rootLoop) :
    ∃ callPost,
      callPost.stack = 1 :: [height] ∧
      callPost.memory = base.memory.write 640
        (Bytes.sha256 (left.toBytes ++ right.toBytes)).toBytes ∧
      Nonempty (RootMemoryCarrier callPost.memory oldCount size
        (Bytes.sha256 (left.toBytes ++ right.toBytes))) ∧
      callPost.gasLeft = K + 85 ∧
      callPost.returnData =
        (Bytes.sha256 (left.toBytes ++ right.toBytes)).toBytes ∧
      (∀ a, Devm.getStor callPost a = Devm.getStor base a) ∧
      callPost.logs = base.logs ∧
      callPost.output = base.output ∧
      callPost.error = base.error ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (callPost.setMach
            ⟨[height + 1],
              callPost.memory.write 608 (size >>> 1).toBytes, K⟩)
          rootLoop ex →
        Func.RunCompiledTo fs sevm
          (base.setMach ⟨[height], base.memory, K + 285⟩)
          (sha64 0 nodeWord (.call rootContinuationSlot)) ex := by
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
      hstorage, hlogs, houtput, herror, hlift⟩ :=
    sha64_success_prefix_runCompiledTo
      (fs := fs) (sevm := sevm) (base := base)
      (inputWord := 0) (outputWord := nodeWord)
      (stack := [height]) (success := .call rootContinuationSlot)
      (K := K + 48)
      hcovered hnodeleg hwarm hpre hdepth (by omega)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hmemory' :
      callPost.memory = base.memory.write 640
        (Bytes.sha256 (left.toBytes ++ right.toBytes)).toBytes := by
    simpa only [hzero, hnode, pair.shaInput] using hmemory
  have hreturn' :
      callPost.returnData =
        (Bytes.sha256 (left.toBytes ++ right.toBytes)).toBytes := by
    simpa only [hzero, pair.shaInput] using hreturn
  have hgas' : callPost.gasLeft = K + 85 := by
    omega
  have hcarrierBase := pair.finishHash
  have hcarrier : RootMemoryCarrier callPost.memory oldCount size
      (Bytes.sha256 (left.toBytes ++ right.toBytes)) := by
    rw [hmemory']
    exact hcarrierBase
  refine ⟨callPost, hstack, hmemory', ⟨hcarrier⟩, hgas', hreturn',
    hstorage, hlogs, houtput, herror, ?_⟩
  intro ex htail
  have hcallMod : callPost.memory.size % 32 = 0 := by
    rw [hcarrier.size_eq]
  have hcallSize : 640 ≤ callPost.memory.size := by
    rw [hcarrier.size_eq]
    omega
  have hcallRead :
      Bytes.toB256 (callPost.memory.read 608 32).1 = size := by
    rw [hcarrier.read_shiftedSize, B256.toB256_toBytes]
  have hroot : Func.RunCompiledTo fs sevm
      (callPost.setMach
        ⟨[height], callPost.memory, K + 36⟩)
      rootContinuation ex :=
    rootContinuation_runCompiledTo
      hcallMod hcallSize hcallRead hrootLoop htail
  have hsuccess : Func.RunCompiledTo fs sevm
      (callPost.setMach
        ⟨[height], callPost.memory, K + 48⟩)
      (.call rootContinuationSlot) ex := by
    exact Func.runCompiledTo_call' (G := K + 36) hrootContinuation
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)
      (by simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest])
      (by
        simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using hroot)
  have hwhole := hlift hsuccess
  simpa only [sha64SuccessCost_zero_node] using hwhole

end Blanc.BeaconDeposit
