import Blanc.BeaconDepositInsertBridge

/-! # Beacon deposit successful root and capacity guards -/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Ninst

/-- The successful suffix after deposit-data reconstruction: check the supplied
root, check the tree-capacity bound, then commit the deposit. -/
def depositSuccessGuards : Func :=
  let checkCap :=
    pushB256 (Nat.toB256 (2 ^ 32 - 1)) :::
    loadWord oldCountWord +++ lt ::: iszero :::
    ((.call treeFullErrorSlot) <?> commitDeposit)
  loadWord nodeWord +++ arg 3 +++ eq ::: iszero :::
  ((.call rootMismatchErrorSlot) <?> checkCap)

/-- When both post-reconstruction guards hold, their compiled path reaches the
commit program without changing memory or world state and consumes exactly
59 gas. -/
theorem depositSuccessGuards_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount node : B256}
    {G : Nat} {ex : Execution}
    (hmem : InsertionStartMemoryCarrier memory oldCount node)
    (hroot : Sevm.argWord sevm 3 = node)
    (hcap : oldCount < Nat.toB256 (2 ^ 32 - 1))
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, G⟩) commitDeposit ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, G + 59⟩)
      depositSuccessGuards ex := by
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hnodeCovered : 640 + 32 ≤ memory.size := by
    rw [hmem.size_eq]
    omega
  have holdCovered : 576 + 32 ≤ memory.size := by
    rw [hmem.size_eq]
    omega
  have hnodeRead : Bytes.toB256 (memory.read 640 32).1 = node :=
    hmem.readNode
  have hnodeMem : (memory.read 640 32).2 = memory := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le hmod hnodeCovered)]
  have holdRead : Bytes.toB256 (memory.read 576 32).1 = oldCount :=
    hmem.readOldCount
  have holdMem : (memory.read 576 32).2 = memory := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le hmod holdCovered)]
  unfold depositSuccessGuards
  func_run (13) [3, 1, 0, 3, 1, 0]
  case h_cost =>
    simp only [show (nodeWord * 32 : B256).toNat = 640 by decide +kernel]
    rw [Devm.extCost_zero_of_le hmod hnodeCovered]
    norm_num [gVerylow]
  case h_val =>
    change Sevm.argWord sevm 3 =? (memory.read 640 32).1.toB256 = 1
    rw [hroot, hnodeRead]
    simp [B256.eqCheck]
  case h_cost =>
    rw [show (nodeWord * 32 : B256).toNat = 640 by decide +kernel,
      hnodeMem,
      show (oldCountWord * 32 : B256).toNat = 576 by decide +kernel]
    rw [Devm.extCost_zero_of_le hmod holdCovered]
    norm_num [gVerylow]
  case h_val =>
    rw [show (nodeWord * 32 : B256).toNat = 640 by decide +kernel,
      hnodeMem,
      show (oldCountWord * 32 : B256).toNat = 576 by decide +kernel,
      holdRead]
    rw [B256.ltCheck, if_pos hcap]
  case h_arm =>
    rw [show (nodeWord * 32 : B256).toNat = 640 by decide +kernel,
      hnodeMem,
      show (oldCountWord * 32 : B256).toNat = 576 by decide +kernel,
      holdMem]
    simpa only [Nat.add_sub_cancel] using htail

end Blanc.BeaconDeposit
