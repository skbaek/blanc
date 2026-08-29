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

/-- Reconstruct the deposit-data node from the decoded deposit arguments and
run both post-reconstruction guards.  The reconstructed node is exactly the
model's `depositDataNode`, and the composed path reaches `commitDeposit` after
exactly `1779 + 59 = 1838` gas. -/
theorem reconstructDepositDataNode_successGuards_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {pubkey withdrawalCredentials signature amountLE : Bytes}
    {oldCount amount : B256} {G : Nat}
    (source : ReconstructSourceMemoryCarrier base.memory
      (pubkey ++ zeros 16) (signature.take 64) (signature.drop 64)
      withdrawalCredentials (amountLE ++ zeros 24) oldCount amount 704)
    (hwithdrawal : withdrawalCredentials.length = 32)
    (hamount : amountLE.length = 8)
    (hsignature : signature.length = 96)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : (G + 59) + 1762 < 2 ^ 256)
    (hroot : Sevm.argWord sevm 3 =
      depositDataNode Bytes.sha256 pubkey withdrawalCredentials signature
        amountLE)
    (hcap : oldCount < Nat.toB256 (2 ^ 32 - 1)) :
    ∃ finalPost,
      Nonempty (InsertionStartMemoryCarrier finalPost.memory oldCount
        (depositDataNode Bytes.sha256 pubkey withdrawalCredentials signature
          amountLE)) ∧
      finalPost.returnData =
        (depositDataNode Bytes.sha256 pubkey withdrawalCredentials signature
          amountLE).toBytes ∧
      ReconstructMetaCarrier sevm base finalPost ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (finalPost.setMach ⟨[], finalPost.memory, G⟩) commitDeposit ex →
        Func.RunCompiledTo fs sevm
          (base.setMach ⟨[], base.memory, G + 1838⟩)
          (reconstructDepositDataNode depositSuccessGuards) ex := by
  have hnodeEq := reconstructedDepositNode_eq_model pubkey
    withdrawalCredentials signature amountLE hwithdrawal hamount hsignature
  obtain ⟨finalPost, hregisters, hreturn, hmeta, hlift⟩ :=
    reconstructDepositDataNode_runCompiledTo
      (fs := fs) (sevm := sevm) (base := base)
      (pubkeyInput := pubkey ++ zeros 16)
      (signatureFirst := signature.take 64)
      (signatureTail := signature.drop 64)
      (withdrawal := withdrawalCredentials)
      (amountPadded := amountLE ++ zeros 24)
      (oldCount := oldCount) (amount := amount) (stack := [])
      (success := depositSuccessGuards) (K := G + 59)
      source hnodeleg hwarm hpre hdepth hbound (by simp)
  obtain ⟨hcarrier⟩ := hregisters
  refine ⟨finalPost, ⟨?_⟩, ?_, hmeta, ?_⟩
  · rw [← hnodeEq]
    exact hcarrier.toInsertionStart
  · rw [← hnodeEq]
    exact hreturn
  · intro ex htail
    have hguards := depositSuccessGuards_runCompiledTo
      (fs := fs) (sevm := sevm) (base := finalPost)
      (memory := finalPost.memory) (G := G)
      hcarrier.toInsertionStart (hroot.trans hnodeEq.symm) hcap htail
    have hgas : G + 59 + 1779 = G + 1838 := by omega
    simpa only [hgas] using hlift hguards

end Blanc.BeaconDeposit
