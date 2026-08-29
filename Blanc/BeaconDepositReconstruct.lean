import Blanc.BeaconDepositReconstructMemory

/-!
# Beacon deposit reconstruction compiled carriers

The seven-hash deposit-data reconstruction alternates direct SHA-256 windows
with pairs staged in memory words `0` and `1`.  This module first isolates the
exact-cost `MLOAD`/`MSTORE` fragment used by every staged word.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Ninst

/-- Exact cost of loading one memory word and storing it at another word. -/
def reconstructLoadStoreCost (sourceWord targetWord : B256) : Nat :=
  pushCost ((sourceWord * 32).toBytes.sig) + 3 +
    pushCost ((targetWord * 32).toBytes.sig) + 3

/-- Execute one covered-memory `loadWord`/`mstoreAt` staging fragment. -/
theorem reconstructLoadStore_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {sourceWord targetWord value : B256}
    {stack : List B256} {K : Nat} {rest : Func} {ex : Execution}
    (hmod : memory.size % 32 = 0)
    (hsourceFit : (sourceWord * 32).toNat + 32 <= memory.size)
    (htargetFit : (targetWord * 32).toNat + 32 <= memory.size)
    (hread : Bytes.toB256
      (memory.read (sourceWord * 32).toNat 32).1 = value)
    (hroom : stack.length < 1023)
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack,
          memory.write (targetWord * 32).toNat value.toBytes, K⟩)
      rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack, memory,
          K + reconstructLoadStoreCost sourceWord targetWord⟩)
      (loadWord sourceWord +++ mstoreAt targetWord +++ rest) ex := by
  let csource := pushCost ((sourceWord * 32).toBytes.sig)
  let ctarget := pushCost ((targetWord * 32).toBytes.sig)
  have hreadMemory :
      (memory.read (sourceWord * 32).toNat 32).2 = memory := by
    apply Mem.read_snd_eq_self
    exact memExtSize_of_le hmod hsourceFit
  simp only [loadWord, mstoreAt, prepend]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := sourceWord * 32) (c := csource)
      (G := K + 3 + ctarget + 3)
      rfl
      (by
        simp only [Devm.gasLeft_setMach, reconstructLoadStoreCost,
          csource, ctarget]
        omega)
      (by simp only [Devm.stack_setMach]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mload_of
      (i := sourceWord * 32) (v := value) (s := stack)
      (c := 3) (G := K + ctarget + 3) (M := memory)
      rfl
      (by
        have hext :
            (base.setMach
              ⟨(sourceWord * 32) :: stack, memory,
                K + 3 + ctarget + 3⟩).extCost
              [⟨(sourceWord * 32).toNat, 32⟩] = 0 :=
          Devm.extCost_zero_of_le hmod hsourceFit
        rw [hext]
        decide)
      hread hreadMemory
      (by
        simp only [Devm.gasLeft_setMach]
        omega)
      (by omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := targetWord * 32) (c := ctarget) (G := K + 3)
      rfl
      (by
        simp only [Devm.gasLeft_setMach]
        omega)
      (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mstore_of
      (i := targetWord * 32) (v := value) (s := stack)
      (G := K) (e := 0)
      rfl
      (Devm.extCost_zero_of_le hmod htargetFit)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      rfl) ?_
  simpa only [Devm.setMach_setMach, Devm.memory_setMach] using htail

@[simp] theorem reconstructLoadStoreCost_node_zero :
    reconstructLoadStoreCost nodeWord 0 = 11 := by
  decide +kernel

@[simp] theorem reconstructLoadStoreCost_intermediate_zero :
    reconstructLoadStoreCost intermediateWord 0 = 11 := by
  decide +kernel

@[simp] theorem reconstructLoadStoreCost_intermediate_one :
    reconstructLoadStoreCost intermediateWord 1 = 12 := by
  decide +kernel

@[simp] theorem reconstructLoadStoreCost_second_one :
    reconstructLoadStoreCost secondIntermediateWord 1 = 12 := by
  decide +kernel

end Blanc.BeaconDeposit
