import Blanc.BeaconDepositBridge
import Blanc.BeaconDepositSuccessPublic

/-!
# Beacon deposit compiled/model bridge

Thin compiled consumer for the pure storage-abstraction lemmas in
`BeaconDepositBridge`.  The executable success theorem already exposes the
count write and the subsequent first-live branch write; this module packages
their model-history consequence without duplicating the runtime walk.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- C6 compiled flagship: a model-successful deposit starting from an
artifact-invariant storage state executes the compiled runtime and preserves
that invariant for the history extended by the deposited data node. -/
theorem deposit_success_artifactInv
    (sevm : Sevm) (base : Devm)
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) (s' : Acc) (ev : DepositEvent)
    (stor : Stor) (keys : KeySet) (countCost n G : Nat)
    (history : List B256)
    (hinvariant : ArtifactInv
      (Devm.getStor base sevm.currentTarget) history)
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
      Prog.RunCompiled sevm
        (base.setMach
          ⟨[], Mem.empty,
            depositRuntimeSuccessGas sevm base stor keys depositDataRoot n
              ((accOfStor
                (Devm.getStor base sevm.currentTarget)).count + 1)
              countCost G⟩)
        runtime post ∧
      ArtifactInv (Devm.getStor post sevm.currentTarget)
        (history ++ [depositDataNode Bytes.sha256 pubkey
          withdrawalCredentials signature
          (le64 (sevm.value.toNat / oneGwei))]) := by
  obtain ⟨post, run, _stack, _gas, _logs, countStorage, postStorage,
      _code, _addresses, _output, _error, _compile⟩ :=
    deposit_success_runCompiled sevm base pubkey withdrawalCredentials
      signature depositDataRoot s' ev stor keys countCost n G hdataBound hdec
      hOk hstor hkeys hcount hheight hfirst hselector hnodeleg hwarm hpre
      hdepth hstatic hbranchSentry hbound hcountSentry hreconstructBound hcode
  have targetStorage : Devm.getStor post sevm.currentTarget =
      stor.set (branchSlot n)
        (accumulatedNode Bytes.sha256 (accOfStor stor).branch
          0 n depositDataRoot) := by
    simpa only [if_pos] using postStorage sevm.currentTarget
  refine ⟨post, run, ?_⟩
  exact ArtifactInv.of_depositSuccessCompiledStorage
    hinvariant hOk hheight hfirst countStorage targetStorage

end Blanc.BeaconDeposit
