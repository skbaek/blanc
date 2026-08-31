import Blanc.BeaconDepositReconstructStorageEffects
import Blanc.BeaconDepositInsertCommit
import Blanc.BeaconDepositSuccessGuards

/-!
# Exact storage effects through the Beacon deposit success suffix

The post-reconstruction guards are storage-neutral.  Composing them with the
exact reconstruction and commit carriers therefore exposes the successful
deposit chronology without weakening it to a final-state delta.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- Exact-effect companion of `depositRootGuard_runCompiledTo`. -/
theorem depositRootGuard_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount node : B256}
    {G : Nat} {rest : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hmem : InsertionStartMemoryCarrier memory oldCount node)
    (hroot : Sevm.argWord sevm 3 = node)
    (htail : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory, G⟩) rest ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory, G + 31⟩)
      (loadWord nodeWord +++ arg 3 +++ eq ::: iszero :::
        ((.call rootMismatchErrorSlot) <?> rest)) ex effects := by
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hcovered : 640 + 32 ≤ memory.size := by
    rw [hmem.size_eq]
    omega
  have hread : Bytes.toB256 (memory.read 640 32).1 = node := hmem.readNode
  have hmemory : (memory.read 640 32).2 = memory := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le hmod hcovered)]
  simp only [loadWord, arg, cdl, prepend,
    show (nodeWord * 32 : B256) = 640 by decide +kernel,
    show 32 * (3 : B256) + 4 = 100 by decide +kernel]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (w := 640) (c := gVerylow) (G := G + 28)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_mload_of
      (sevm := sevm)
      (devm := base.setMach ⟨[640], memory, G + 28⟩)
      (i := 640) (v := node) (s := []) (c := gVerylow)
      (G := G + 25) (M := memory) rfl
      (by
        rw [show (640 : B256).toNat = 640 by decide +kernel]
        rw [Devm.extCost_zero_of_le hmod hcovered]
        rfl)
      hread hmemory
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (w := 100) (c := gVerylow) (G := G + 22)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_calldataload
      (sevm := sevm)
      (devm := base.setMach ⟨100 :: node :: [], memory, G + 22⟩)
      (x := 100) (v := Sevm.argWord sevm 3) (s := node :: [])
      (G := G + 19) rfl
      (by rfl)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary
      (sevm := sevm)
      (devm := base.setMach
        ⟨Sevm.argWord sevm 3 :: node :: [], memory, G + 19⟩)
      (r := .eq) (f := B256.eqCheck) (cost := gVerylow)
      (x := Sevm.argWord sevm 3) (y := node) (v := 1) (s := [])
      (G := G + 16) (by rintro ⟨⟩) rfl rfl
      (by rw [hroot]; simp [B256.eqCheck])
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_unary
      (sevm := sevm)
      (devm := base.setMach ⟨[1], memory, G + 16⟩)
      (r := .iszero) (f := (B256.eqCheck · 0))
      (cost := gVerylow) (x := 1) (v := 0) (s := [])
      (G := G + 13) (by rintro ⟨⟩) rfl rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.zero
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (Devm.popBurnBy_setMach (s := []) (G := G)
      (by simp only [Devm.stack_setMach])
      (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh]))
  simpa only [Devm.setMach_setMach, Devm.memory_setMach] using htail

/-- Exact-effect companion of `depositCapGuard_runCompiledTo`. -/
theorem depositCapGuard_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount node : B256}
    {G : Nat} {rest : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hmem : InsertionStartMemoryCarrier memory oldCount node)
    (hcap : oldCount < Nat.toB256 (2 ^ 32 - 1))
    (htail : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory, G⟩) rest ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory, G + 28⟩)
      (Ninst.pushB256 (Nat.toB256 (2 ^ 32 - 1)) :::
        loadWord oldCountWord +++ lt ::: iszero :::
        ((.call treeFullErrorSlot) <?> rest)) ex effects := by
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hcovered : 576 + 32 ≤ memory.size := by
    rw [hmem.size_eq]
    omega
  have hread : Bytes.toB256 (memory.read 576 32).1 = oldCount :=
    hmem.readOldCount
  have hmemory : (memory.read 576 32).2 = memory := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le hmod hcovered)]
  simp only [loadWord, prepend,
    show (oldCountWord * 32 : B256) = 576 by decide +kernel]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256
      (w := Nat.toB256 (2 ^ 32 - 1)) (c := gVerylow) (G := G + 25)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (w := 576) (c := gVerylow) (G := G + 22)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_mload_of
      (sevm := sevm)
      (devm := base.setMach
        ⟨576 :: Nat.toB256 (2 ^ 32 - 1) :: [], memory, G + 22⟩)
      (i := 576) (v := oldCount)
      (s := Nat.toB256 (2 ^ 32 - 1) :: [])
      (c := gVerylow) (G := G + 19) (M := memory) rfl
      (by
        rw [show (576 : B256).toNat = 576 by decide +kernel]
        rw [Devm.extCost_zero_of_le hmod hcovered]
        rfl)
      hread hmemory
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary
      (sevm := sevm)
      (devm := base.setMach
        ⟨oldCount :: Nat.toB256 (2 ^ 32 - 1) :: [], memory, G + 19⟩)
      (r := .lt) (f := B256.ltCheck) (cost := gVerylow)
      (x := oldCount) (y := Nat.toB256 (2 ^ 32 - 1))
      (v := 1) (s := []) (G := G + 16)
      (by rintro ⟨⟩) rfl rfl
      (by rw [B256.ltCheck, if_pos hcap])
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_unary
      (sevm := sevm)
      (devm := base.setMach ⟨[1], memory, G + 16⟩)
      (r := .iszero) (f := (B256.eqCheck · 0))
      (cost := gVerylow) (x := 1) (v := 0) (s := [])
      (G := G + 13) (by rintro ⟨⟩) rfl rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.zero
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (Devm.popBurnBy_setMach (s := []) (G := G)
      (by simp only [Devm.stack_setMach])
      (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh]))
  simpa only [Devm.setMach_setMach, Devm.memory_setMach] using htail

/-- Both successful post-reconstruction guards preserve exact chronology. -/
theorem depositSuccessGuards_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount node : B256}
    {G : Nat} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hmem : InsertionStartMemoryCarrier memory oldCount node)
    (hroot : Sevm.argWord sevm 3 = node)
    (hcap : oldCount < Nat.toB256 (2 ^ 32 - 1))
    (htail : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory, G⟩) commitDeposit ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory, G + 59⟩)
      depositSuccessGuards ex effects := by
  have hcapRun := depositCapGuard_storageEffectRun hmem hcap htail
  have hrootRun := depositRootGuard_storageEffectRun hmem hroot hcapRun
  simpa only [depositSuccessGuards, Nat.add_assoc] using hrootRun

/-- Exact-effect reconstruction followed by both successful post-hash guards. -/
theorem reconstructDepositDataNode_successGuards_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {pubkey withdrawalCredentials signature amountLE : Bytes}
    {oldCount amount : B256} {G : Nat}
    {effects : List (Adr × B256 × B256)}
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
        Func.StorageEffectRun fs sevm
          (finalPost.setMach ⟨[], finalPost.memory, G⟩)
          commitDeposit ex effects →
        Func.StorageEffectRun fs sevm
          (base.setMach ⟨[], base.memory, G + 1838⟩)
          (reconstructDepositDataNode depositSuccessGuards) ex effects := by
  have hnodeEq := reconstructedDepositNode_eq_model pubkey
    withdrawalCredentials signature amountLE hwithdrawal hamount hsignature
  obtain ⟨finalPost, hregisters, hreturn, hmeta, hlift⟩ :=
    reconstructDepositDataNode_storageEffectRun
      (fs := fs) (sevm := sevm) (base := base)
      (pubkeyInput := pubkey ++ zeros 16)
      (signatureFirst := signature.take 64)
      (signatureTail := signature.drop 64)
      (withdrawal := withdrawalCredentials)
      (amountPadded := amountLE ++ zeros 24)
      (oldCount := oldCount) (amount := amount) (stack := [])
      (success := depositSuccessGuards) (K := G + 59)
      (effects := effects)
      source hnodeleg hwarm hpre hdepth hbound (by simp)
  obtain ⟨hcarrier⟩ := hregisters
  refine ⟨finalPost, ⟨?_⟩, ?_, hmeta, ?_⟩
  · rw [← hnodeEq]
    exact hcarrier.toInsertionStart
  · rw [← hnodeEq]
    exact hreturn
  · intro ex htail
    have hguards := depositSuccessGuards_storageEffectRun
      (fs := fs) (sevm := sevm) (base := finalPost)
      (memory := finalPost.memory) (G := G)
      hcarrier.toInsertionStart (hroot.trans hnodeEq.symm) hcap htail
    have hgas : G + 59 + 1779 = G + 1838 := by omega
    simpa only [hgas] using hlift hguards

/-- The complete post-decode success suffix retains exactly the count write
followed by the unique first-live branch write. -/
theorem depositSuccessSuffix_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {pubkey withdrawalCredentials signature amountLE : Bytes}
    {oldCount amount node : B256} {stor : Stor} {keys : KeySet}
    {countCost n size G : Nat}
    (source : ReconstructSourceMemoryCarrier base.memory
      (pubkey ++ zeros 16) (signature.take 64) (signature.drop 64)
      withdrawalCredentials (amountLE ++ zeros 24) oldCount amount 704)
    (hwithdrawal : withdrawalCredentials.length = 32)
    (hamount : amountLE.length = 8)
    (hsignature : signature.length = 96)
    (hnode : node =
      depositDataNode Bytes.sha256 pubkey withdrawalCredentials signature
        amountLE)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hstatic : sevm.isStatic = false)
    (hroot : Sevm.argWord sevm 3 = node)
    (hcap : oldCount < Nat.toB256 (2 ^ 32 - 1))
    (hshift : oldCount + 1 = Nat.toB256 size)
    (hheight : n < 32)
    (hsize : size < 2 ^ 32)
    (hfirst : FirstLive size n)
    (hstor : Devm.getStor
      (afterSstore sevm base depositCountSlot (oldCount + 1))
      sevm.currentTarget = stor)
    (hkeys :
      (afterSstore sevm base depositCountSlot
        (oldCount + 1)).accessedStorageKeys = keys)
    (hcount : sstoreCost sevm base depositCountSlot (oldCount + 1) = countCost)
    (hbranchSentry : gCallStipend < G + 2 +
      insertionFirstLiveStoreCost sevm stor keys 0 n node)
    (hbound :
      (G + 46 + insertionFirstLiveStoreCost sevm stor keys 0 n node) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0 size node keys) < 2 ^ 256)
    (hcountSentry : gCallStipend <
      ((G + 46 + insertionFirstLiveStoreCost sevm stor keys 0 n node) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0 size node keys)) + 14 + countCost)
    (hreconstructBound :
      ((((G + 46 + insertionFirstLiveStoreCost sevm stor keys 0 n node) +
          insertionDeadGas sevm.currentTarget stor n
            (insertionNatState 0 size node keys)) + 38 + countCost) + 59) +
        1762 < 2 ^ 256)
    (hinsertionContinuation :
      fs[insertionContinuationSlot]? = some insertionContinuation)
    (hinsertionLoop : fs[insertionLoopSlot]? = some insertionLoop) :
    ∃ mid finalBase finalMemory,
      ReconstructMetaCarrier sevm base mid ∧
      Nonempty (InsertionLoopCarrier
        (afterSstore sevm mid depositCountSlot (oldCount + 1))
        finalBase finalMemory oldCount
        (insertionLoopIter sevm.currentTarget stor n
          (insertionNatState 0 size node keys))) ∧
      Func.StorageEffectRun fs sevm
        (base.setMach
          ⟨[], base.memory,
            ((((G + 46 +
                  insertionFirstLiveStoreCost sevm stor keys 0 n node) +
                insertionDeadGas sevm.currentTarget stor n
                  (insertionNatState 0 size node keys)) + 38 + countCost)) +
              1838⟩)
        (reconstructDepositDataNode depositSuccessGuards)
        (.ok ((afterSstore sevm finalBase (branchSlot n)
          (accumulatedNode Bytes.sha256 (accOfStor stor).branch
            0 n node)).setMach ⟨[], finalMemory, G⟩))
        [(sevm.currentTarget, depositCountSlot, oldCount + 1),
          (sevm.currentTarget, branchSlot n,
            accumulatedNode Bytes.sha256 (accOfStor stor).branch
              0 n node)] := by
  subst hnode
  obtain ⟨mid, hcarrier, _hreturn, hmeta, hlift⟩ :=
    reconstructDepositDataNode_successGuards_storageEffectRun
      (fs := fs) (sevm := sevm) (base := base)
      (pubkey := pubkey) (withdrawalCredentials := withdrawalCredentials)
      (signature := signature) (amountLE := amountLE)
      (oldCount := oldCount) (amount := amount)
      (effects :=
        [(sevm.currentTarget, depositCountSlot, oldCount + 1),
          (sevm.currentTarget, branchSlot n,
            accumulatedNode Bytes.sha256 (accOfStor stor).branch 0 n
              (depositDataNode Bytes.sha256 pubkey withdrawalCredentials
                signature amountLE))])
      (G :=
        (((G + 46 + insertionFirstLiveStoreCost sevm stor keys 0 n
              (depositDataNode Bytes.sha256 pubkey withdrawalCredentials
                signature amountLE)) +
            insertionDeadGas sevm.currentTarget stor n
              (insertionNatState 0 size
                (depositDataNode Bytes.sha256 pubkey withdrawalCredentials
                  signature amountLE) keys)) + 38 + countCost))
      source hwithdrawal hamount hsignature hnodeleg hwarm hpre hdepth
      hreconstructBound hroot hcap
  obtain ⟨hstart⟩ := hcarrier
  have hstorMid : Devm.getStor
      (afterSstore sevm mid depositCountSlot (oldCount + 1))
      sevm.currentTarget = stor := by
    rw [Blanc.afterSstore_getStor_self, hmeta.storage sevm.currentTarget,
      ← Blanc.afterSstore_getStor_self]
    exact hstor
  have hkeysMid :
      (afterSstore sevm mid depositCountSlot
        (oldCount + 1)).accessedStorageKeys = keys := by
    rw [Blanc.afterSstore_accessedStorageKeys, hmeta.accessedStorageKeys,
      ← Blanc.afterSstore_accessedStorageKeys]
    exact hkeys
  have hnodelegMid : getDelegatedCodeAddress
      ((afterSstore sevm mid depositCountSlot (oldCount + 1)).getCode 2)
        = none := by
    rw [Blanc.afterSstore_getCode, hmeta.code 2]
    exact hnodeleg
  have hwarmMid : (2 : Adr) ∈
      (afterSstore sevm mid depositCountSlot
        (oldCount + 1)).accessedAddresses := by
    rw [Blanc.afterSstore_accessedAddresses, hmeta.accessedAddresses]
    exact hwarm
  have hcountMid :
      sstoreCost sevm mid depositCountSlot (oldCount + 1) = countCost := by
    rw [Blanc.sstoreCost_congr _ _ hmeta.accessedStorageKeys
      (hmeta.storage sevm.currentTarget)]
    exact hcount
  obtain ⟨finalBase, finalMemory, hfinal, hcommit⟩ :=
    commitDeposit_firstLive_exists_storageEffectRun
      (fs := fs) (sevm := sevm) (base := mid) (memory := mid.memory)
      (oldCount := oldCount) (n := n) (size := size) (G := G)
      hstart hshift hstorMid hkeysMid hheight hsize hfirst hnodelegMid
      hwarmMid hpre hdepth hstatic
      (by rw [hcountMid] at *; exact hbranchSentry)
      (by rw [hcountMid] at *; exact hbound)
      (by rw [hcountMid]; exact hcountSentry)
      hinsertionContinuation hinsertionLoop
  rw [hcountMid] at hcommit
  exact ⟨mid, finalBase, finalMemory, hmeta, hfinal, hlift hcommit⟩

end Blanc.BeaconDeposit
