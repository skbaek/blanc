import Blanc.BeaconDepositRouteStorageEffects
import Blanc.BeaconDepositSuccessEndpointStorageEffects
import Blanc.BeaconDepositSuccessPublic

/-!
# Exact retained chronology of a successful Beacon deposit

This is the access-pillar companion to `deposit_success_runCompiled`.  The
existing theorem describes the successful poststate and canonical event; this
module identifies the complete retained SSTORE chronology of the same
model-successful public call.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- A model-successful public deposit has an actual compiled execution whose
complete retained storage-effect list is count first and the unique first-live
branch cell second. -/
theorem deposit_success_retainedStorageEffectTriples
    (sevm : Sevm) (base : Devm)
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) (s' : Acc) (ev : DepositEvent)
    (stor : Stor) (keys : KeySet) (countCost n G : Nat)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (hOk : deposit Bytes.sha256
      (accOfStor (Devm.getStor base sevm.currentTarget))
      pubkey withdrawalCredentials signature depositDataRoot
      sevm.value.toNat = .ok (s', ev))
    (hstor : Devm.getStor
      (afterSstore sevm (afterSload sevm base depositCountSlot)
        depositCountSlot
        (Nat.toB256
          (accOfStor (Devm.getStor base sevm.currentTarget)).count + 1))
      sevm.currentTarget = stor)
    (hkeys :
      (afterSstore sevm (afterSload sevm base depositCountSlot)
        depositCountSlot
        (Nat.toB256
          (accOfStor
            (Devm.getStor base sevm.currentTarget)).count + 1)).accessedStorageKeys =
        keys)
    (hcount : sstoreCost sevm
      (afterSload sevm base depositCountSlot) depositCountSlot
      (Nat.toB256
        (accOfStor (Devm.getStor base sevm.currentTarget)).count + 1) =
      countCost)
    (hheight : n < 32)
    (hfirst : FirstLive
      ((accOfStor (Devm.getStor base sevm.currentTarget)).count + 1) n)
    (hselector : Sevm.selector sevm = depositSelector)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hstatic : sevm.isStatic = false)
    (hbaseError : base.error = none)
    (hbranchSentry : gCallStipend < G + 2 +
      insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot)
    (hbound :
      (G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys) < 2 ^ 256)
    (hcountSentry : gCallStipend <
      ((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys)) + 14 + countCost)
    (hreconstructBound :
      ((((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys)) + 38 + countCost) + 59) +
        1762 < 2 ^ 256)
    (hcode : sevm.code.toList = code) :
    ∃ post,
      ∃ execution : Exec 0 sevm
          (base.setMach
            ⟨[], Mem.empty,
              depositRuntimeSuccessGas sevm base stor keys depositDataRoot n
                ((accOfStor
                  (Devm.getStor base sevm.currentTarget)).count + 1)
                countCost G⟩)
          (.ok post),
        Prog.RunCompiledTo sevm
          (base.setMach
            ⟨[], Mem.empty,
              depositRuntimeSuccessGas sevm base stor keys depositDataRoot n
                ((accOfStor
                  (Devm.getStor base sevm.currentTarget)).count + 1)
                countCost G⟩)
          runtime (.ok post) ∧
        Exec.retainedStorageEffectTriples execution =
          [(sevm.currentTarget, depositCountSlot,
              Nat.toB256
                (accOfStor
                  (Devm.getStor base sevm.currentTarget)).count + 1),
            (sevm.currentTarget, branchSlot n,
              accumulatedNode Bytes.sha256 (accOfStor stor).branch
                0 n depositDataRoot)] ∧
        some sevm.code.toList = Prog.compile runtime := by
  let s := accOfStor (Devm.getStor base sevm.currentTarget)
  have hcountValue :
      base.getStorVal sevm.currentTarget depositCountSlot =
        Nat.toB256 s.count := by
    change (Devm.getStor base sevm.currentTarget).get depositCountSlot =
      Nat.toB256
        ((Devm.getStor base sevm.currentTarget).get depositCountSlot).toNat
    exact (Jaune.toB256_toNat _).symm
  obtain ⟨_logged, _mid, finalBase, finalMemory, _hlogs, _hstorVal,
      _hstorMap, _hbal, _hloggedCode, _hloadedKeys, _haddresses,
      _houtput, _herror, _hmeta, _hfinal, hendpoint⟩ :=
    depositEndpoint_success_storageEffectRun
      (fs := runtime.main :: runtime.aux) (sevm := sevm) (base := base)
      (pubkey := pubkey) (withdrawalCredentials := withdrawalCredentials)
      (signature := signature) (depositDataRoot := depositDataRoot)
      (s := s) (s' := s') (ev := ev) (stor := stor) (keys := keys)
      (countCost := countCost) (n := n) (G := G)
      hdataBound hdec (by simpa only [s] using hOk) hcountValue
      (by simpa only [s] using hstor)
      (by simpa only [s] using hkeys)
      (by simpa only [s] using hcount)
      hheight (by simpa only [s] using hfirst) hnodeleg hwarm hpre hdepth
      hstatic hbranchSentry (by simpa only [s] using hbound)
      (by simpa only [s] using hcountSentry)
      (by simpa only [s] using hreconstructBound) (by rfl) (by rfl)
  let branchValue :=
    accumulatedNode Bytes.sha256 (accOfStor stor).branch
      0 n depositDataRoot
  let post :=
    (afterSstore sevm finalBase (branchSlot n) branchValue).setMach
      ⟨[], finalMemory, G⟩
  have hendpoint' : Func.StorageEffectRun
      (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[], Mem.empty,
          depositEndpointSuccessGas sevm base stor keys depositDataRoot n
            (s.count + 1) countCost G⟩)
      depositEndpoint (.ok post)
      [(sevm.currentTarget, depositCountSlot, Nat.toB256 s.count + 1),
        (sevm.currentTarget, branchSlot n, branchValue)] := by
    simpa only [post, branchValue] using hendpoint
  have hlengthWordNe : sevm.data.length.toB256 ≠ 0 := by
    intro hzero
    have hnat := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt hdataBound] at hnat
    simp only [B256.toNat_zero] at hnat
    have hhead := hdec.head
    omega
  obtain ⟨hcarrier⟩ := _hfinal
  have hpostError : post.error = none := by
    change
      (afterSstore sevm finalBase (branchSlot n) branchValue).error = none
    rw [Blanc.afterSstore_error, hcarrier.error,
      Blanc.afterSstore_error, _hmeta.error]
    change _logged.error = none
    rw [_herror, Blanc.afterSload_error, hbaseError]
  obtain ⟨execution, hrun, heffects, hcompiled⟩ :=
    deposit_route_retainedStorageEffectTriples
      hlengthWordNe hselector hendpoint'
        (by simpa [Execution.commits] using hpostError) hcode
  refine ⟨post, execution, ?_, ?_, hcompiled⟩
  · simpa only [depositRuntimeSuccessGas, s] using hrun
  · exact heffects

end Blanc.BeaconDeposit
