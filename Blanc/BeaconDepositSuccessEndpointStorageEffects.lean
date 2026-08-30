import Blanc.BeaconDepositAbiStorageEffects
import Blanc.BeaconDepositEventStorageEffects
import Blanc.BeaconDepositGuardStorageEffects
import Blanc.BeaconDepositSuccess
import Blanc.BeaconDepositSuccessStorageEffects

/-! # Exact retained storage effects for a successful Beacon deposit endpoint -/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- A model-successful deposit endpoint retains exactly the deposit-count write
and then its unique first-live branch write. -/
theorem depositEndpoint_success_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {s s' : Acc} {ev : DepositEvent}
    {stor : Stor} {keys : KeySet} {countCost n G : Nat}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (hOk : deposit Bytes.sha256 s pubkey withdrawalCredentials signature
      depositDataRoot sevm.value.toNat = .ok (s', ev))
    (hcountValue :
      base.getStorVal sevm.currentTarget depositCountSlot =
        Nat.toB256 s.count)
    (hstor : Devm.getStor
      (afterSstore sevm (afterSload sevm base depositCountSlot)
        depositCountSlot (Nat.toB256 s.count + 1))
      sevm.currentTarget = stor)
    (hkeys :
      (afterSstore sevm (afterSload sevm base depositCountSlot)
        depositCountSlot
        (Nat.toB256 s.count + 1)).accessedStorageKeys = keys)
    (hcount :
      sstoreCost sevm (afterSload sevm base depositCountSlot)
        depositCountSlot (Nat.toB256 s.count + 1) = countCost)
    (hheight : n < 32)
    (hfirst : FirstLive (s.count + 1) n)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hstatic : sevm.isStatic = false)
    (hbranchSentry : gCallStipend < G + 2 +
      insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot)
    (hbound :
      (G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0 (s.count + 1) depositDataRoot keys) <
        2 ^ 256)
    (hcountSentry : gCallStipend <
      ((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0 (s.count + 1) depositDataRoot keys)) +
        14 + countCost)
    (hreconstructBound :
      ((((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0 (s.count + 1) depositDataRoot keys)) +
        38 + countCost) + 59) + 1762 < 2 ^ 256)
    (hinsertionContinuation :
      fs[insertionContinuationSlot]? = some insertionContinuation)
    (hinsertionLoop :
      fs[insertionLoopSlot]? = some insertionLoop) :
    ∃ logged mid finalBase finalMemory,
      logged.logs =
        base.logs ++ [depositEventLog sevm.currentTarget ev] ∧
      (∀ a k, logged.getStorVal a k =
        (afterSload sevm base depositCountSlot).getStorVal a k) ∧
      (∀ a, Devm.getStor logged a =
        Devm.getStor (afterSload sevm base depositCountSlot) a) ∧
      (∀ a, logged.getBal a =
        (afterSload sevm base depositCountSlot).getBal a) ∧
      (∀ a, logged.getCode a =
        (afterSload sevm base depositCountSlot).getCode a) ∧
      logged.accessedStorageKeys =
        (afterSload sevm base depositCountSlot).accessedStorageKeys ∧
      logged.accessedAddresses =
        (afterSload sevm base depositCountSlot).accessedAddresses ∧
      logged.output =
        (afterSload sevm base depositCountSlot).output ∧
      logged.error =
        (afterSload sevm base depositCountSlot).error ∧
      ReconstructMetaCarrier sevm
        (logged.setMach
          ⟨[], depositEventMemory sevm.data
            (sevm.value / Nat.toB256 oneGwei)
            (Nat.toB256 s.count), G⟩)
        mid ∧
      Nonempty (InsertionLoopCarrier
        (afterSstore sevm mid depositCountSlot
          (Nat.toB256 s.count + 1))
        finalBase finalMemory (Nat.toB256 s.count)
        (insertionLoopIter sevm.currentTarget stor n
          (insertionNatState 0 (s.count + 1)
            depositDataRoot keys))) ∧
      Func.StorageEffectRun fs sevm
        (base.setMach
          ⟨[], Mem.empty,
            depositEndpointSuccessGas sevm base stor keys depositDataRoot
              n (s.count + 1) countCost G⟩)
        depositEndpoint
        (.ok
          ((afterSstore sevm finalBase (branchSlot n)
            (accumulatedNode Bytes.sha256 (accOfStor stor).branch
              0 n depositDataRoot)).setMach
            ⟨[], finalMemory, G⟩))
        [(sevm.currentTarget, depositCountSlot, Nat.toB256 s.count + 1),
          (sevm.currentTarget, branchSlot n,
            accumulatedNode Bytes.sha256 (accOfStor stor).branch
              0 n depositDataRoot)] := by
  obtain ⟨hpubkey, hwithdrawal, hsignature, hlowerNat, hgweiNat,
      hupperNat, hrootModel, hcapNat, _hnewCount, hevent, _hinsert⟩ :=
    deposit_ok_spec Bytes.sha256 s pubkey withdrawalCredentials signature
      depositDataRoot sevm.value.toNat s' ev hOk
  let amount := sevm.value / Nat.toB256 oneGwei
  let oldCount := Nat.toB256 s.count
  have hdenNe : Nat.toB256 oneGwei ≠ 0 := by
    intro hzero
    have h := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt (by norm_num [oneGwei])] at h
    simp only [B256.toNat_zero] at h
    norm_num [oneGwei] at h
  have hdenNat : (Nat.toB256 oneGwei).toNat = oneGwei :=
    B256.toNat_toB256_of_lt (by norm_num [oneGwei])
  have hamountNat : amount.toNat = sevm.value.toNat / oneGwei := by
    dsimp only [amount]
    rw [B256.toNat_div hdenNe, hdenNat]
  have hlowerWord : Nat.toB256 oneEther ≤ sevm.value := by
    rw [B256.le_iff_toNat_le_toNat,
      B256.toNat_toB256_of_lt (by norm_num [oneEther])]
    exact hlowerNat
  have hgweiWord : sevm.value % Nat.toB256 oneGwei = 0 := by
    apply B256.toNat_inj
    simpa only [B256.toNat_mod hdenNe, hdenNat, B256.toNat_zero] using
      hgweiNat
  have hupperWord : amount ≤ Nat.toB256 (2 ^ 64 - 1) := by
    rw [B256.le_iff_toNat_le_toNat, hamountNat,
      B256.toNat_toB256_of_lt (by omega)]
    exact hupperNat
  have holdNat : oldCount.toNat = s.count :=
    B256.toNat_toB256_of_lt (by omega)
  have hcapWord : oldCount < Nat.toB256 (2 ^ 32 - 1) := by
    rw [B256.lt_iff_toNat_lt_toNat, holdNat,
      B256.toNat_toB256_of_lt (by omega)]
    exact hcapNat
  have hshift : oldCount + 1 = Nat.toB256 (s.count + 1) :=
    Blanc.toB256_add_one_of_lt s.count (by omega)
  have hrootArg : Sevm.argWord sevm 3 = depositDataRoot := by
    unfold Sevm.argWord
    rw [show 32 * (3 : B256) + 4 = Nat.toB256 100 by decide +kernel,
      dataWord_toB256 (by omega), hdec.root_eq]
  have hnode : depositDataRoot =
      depositDataNode Bytes.sha256 pubkey withdrawalCredentials signature
        (le64 amount.toNat) := by
    rw [hamountNat]
    exact hrootModel.symm
  have hstaged : stagedDepositEvent sevm.data amount oldCount = ev := by
    calc
      _ = ⟨pubkey, withdrawalCredentials, le64 amount.toNat, signature,
          le64 oldCount.toNat⟩ :=
        stagedDepositEvent_eq_of_decodable
          hdec hpubkey hwithdrawal hsignature
      _ = ev := by
        simpa only [hamountNat, holdNat] using hevent.symm
  let suffixGas :=
    ((((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0 (s.count + 1) depositDataRoot keys)) +
      38 + countCost) + 1838)
  obtain ⟨logged, hlogs, hstorVal, hstorMap, hbal, hcode, hloadedKeys,
      haddresses, houtput, herror, heventLift⟩ :=
    stageDepositEvent_storageEffectRun
      (fs := fs) (sevm := sevm) (base := base)
      (amount := amount) (oldCount := oldCount) (G := suffixGas)
      (body := depositAfterEvent)
      (effects :=
        [(sevm.currentTarget, depositCountSlot, oldCount + 1),
          (sevm.currentTarget, branchSlot n,
            accumulatedNode Bytes.sha256 (accOfStor stor).branch
              0 n depositDataRoot)])
      hdec.pubkeyTail hdec.withdrawalCredentialsTail hdec.signatureTail
      (by simpa only [oldCount] using hcountValue) hstatic
  let stagedBase := logged.setMach
    ⟨[], depositEventMemory sevm.data amount oldCount, G⟩
  have hsource :
      ReconstructSourceMemoryCarrier stagedBase.memory
        (pubkey ++ zeros 16) (signature.take 64) (signature.drop 64)
        withdrawalCredentials (le64 amount.toNat ++ zeros 24)
        oldCount amount 704 := by
    simpa only [stagedBase, Devm.memory_setMach] using
      (depositEventMemory_carrier sevm.data amount oldCount
        |>.toDecodedReconstructSource
          hdec hpubkey hwithdrawal hsignature)
  have hstagedStor : Devm.getStor stagedBase sevm.currentTarget =
      Devm.getStor (afterSload sevm base depositCountSlot)
        sevm.currentTarget := by
    change Devm.getStor logged sevm.currentTarget =
      Devm.getStor (afterSload sevm base depositCountSlot)
        sevm.currentTarget
    exact hstorMap sevm.currentTarget
  have hstagedKeys : stagedBase.accessedStorageKeys =
      (afterSload sevm base depositCountSlot).accessedStorageKeys := by
    change logged.accessedStorageKeys =
      (afterSload sevm base depositCountSlot).accessedStorageKeys
    exact hloadedKeys
  have hstor' : Devm.getStor
      (afterSstore sevm stagedBase depositCountSlot (oldCount + 1))
      sevm.currentTarget = stor := by
    rw [Blanc.afterSstore_getStor_self, hstagedStor,
      ← Blanc.afterSstore_getStor_self]
    simpa only [oldCount] using hstor
  have hkeys' :
      (afterSstore sevm stagedBase depositCountSlot
        (oldCount + 1)).accessedStorageKeys = keys := by
    rw [Blanc.afterSstore_accessedStorageKeys, hstagedKeys,
      ← Blanc.afterSstore_accessedStorageKeys]
    simpa only [oldCount] using hkeys
  have hcount' :
      sstoreCost sevm stagedBase depositCountSlot (oldCount + 1) =
        countCost := by
    rw [Blanc.sstoreCost_congr _ _ hstagedKeys hstagedStor]
    simpa only [oldCount] using hcount
  have hnodeleg' : getDelegatedCodeAddress (stagedBase.getCode 2) = none := by
    change getDelegatedCodeAddress (logged.getCode 2) = none
    rw [hcode 2, Blanc.afterSload_getCode]
    exact hnodeleg
  have hwarm' : (2 : Adr) ∈ stagedBase.accessedAddresses := by
    change (2 : Adr) ∈ logged.accessedAddresses
    rw [haddresses, Blanc.afterSload_accessedAddresses]
    exact hwarm
  obtain ⟨mid, finalBase, finalMemory, hmeta, hfinal, hsuffix⟩ :=
    depositSuccessSuffix_storageEffectRun
      (fs := fs) (sevm := sevm) (base := stagedBase)
      (pubkey := pubkey) (withdrawalCredentials := withdrawalCredentials)
      (signature := signature) (amountLE := le64 amount.toNat)
      (oldCount := oldCount) (amount := amount) (node := depositDataRoot)
      (stor := stor) (keys := keys) (countCost := countCost)
      (n := n) (size := s.count + 1) (G := G)
      hsource hwithdrawal rfl hsignature hnode hnodeleg' hwarm' hpre hdepth
      hstatic hrootArg hcapWord hshift hheight (by omega) hfirst hstor'
      hkeys' hcount' hbranchSentry hbound hcountSentry hreconstructBound
      hinsertionContinuation hinsertionLoop
  have heventRun : Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[], depositEventInputMemory sevm.data amount,
          suffixGas + 5799 + sloadCost sevm base depositCountSlot⟩)
      (stageDepositEvent +++ depositAfterEvent)
      (.ok
        ((afterSstore sevm finalBase (branchSlot n)
          (accumulatedNode Bytes.sha256 (accOfStor stor).branch
            0 n depositDataRoot)).setMach ⟨[], finalMemory, G⟩))
      [(sevm.currentTarget, depositCountSlot, oldCount + 1),
        (sevm.currentTarget, branchSlot n,
          accumulatedNode Bytes.sha256 (accOfStor stor).branch
            0 n depositDataRoot)] := by
    apply heventLift
    rw [show depositAfterEvent =
      reconstructDepositDataNode depositSuccessGuards by rfl]
    simpa only [stagedBase, Devm.setMach_setMach, Devm.memory_setMach,
      suffixGas] using hsuffix
  have hguards := depositGuards_storageEffectRun
    (fs := fs) (sevm := sevm) (base := base)
    (amount := amount)
    (G := suffixGas + 5799 + sloadCost sevm base depositCountSlot)
    hdec hpubkey hwithdrawal hsignature rfl hlowerWord hgweiWord hupperWord
    heventRun
  have habi := validateDepositAbi_success_storageEffectRun
    (fs := fs) (sevm := sevm) (base := base)
    (G := suffixGas + 5799 + sloadCost sevm base depositCountSlot +
      depositGuardsGas)
    hdataBound hdec hguards
  refine ⟨logged, mid, finalBase, finalMemory, ?_, hstorVal, hstorMap,
    hbal, hcode, hloadedKeys, haddresses, houtput, herror, hmeta, hfinal, ?_⟩
  · rw [Blanc.afterSload_logs, hstaged] at hlogs
    exact hlogs
  · simpa only [depositEndpoint, depositEndpointSuccessGas, suffixGas,
      oldCount] using habi

end Blanc.BeaconDeposit
