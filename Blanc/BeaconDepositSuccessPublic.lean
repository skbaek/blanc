import Blanc.BeaconDepositEffects
import Blanc.BeaconDepositSuccess

/-!
# Beacon deposit public success effect

Thin selector-route composition of the model-linked successful endpoint.  The
result states the exact event and two-cell storage effect at runtime altitude.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Ninst

/-- Exact successful runtime gas.  The selector route contributes 93 gas on
top of the endpoint's fixed 8,456-gas overhead and variable storage charges. -/
def depositRuntimeSuccessGas
    (sevm : Sevm) (base : Devm) (stor : Stor) (keys : KeySet)
    (node : B256) (n size countCost G : Nat) : Nat :=
  depositEndpointSuccessGas sevm base stor keys node n size countCost G +
    depositRouteGas

/-- A successful pure-model deposit has an exact successful compiled runtime
execution.  Storage is the count-updated target map followed by the unique
first-live branch write; every non-target storage map, code, accessed-address
set, output, and error is unchanged, and exactly one byte-exact event is
appended. -/
theorem deposit_success_runCompiled
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
      post.stack = [] ∧
      post.gasLeft = G ∧
      post.logs = base.logs ++
        [depositEventLog sevm.currentTarget ev] ∧
      stor =
        (Devm.getStor base sevm.currentTarget).set depositCountSlot
          (Nat.toB256
            (accOfStor (Devm.getStor base sevm.currentTarget)).count + 1) ∧
      (∀ a, Devm.getStor post a =
        if a = sevm.currentTarget then
          stor.set (branchSlot n)
            (accumulatedNode Bytes.sha256 (accOfStor stor).branch
              0 n depositDataRoot)
        else Devm.getStor base a) ∧
      (∀ a, post.getCode a = base.getCode a) ∧
      post.accessedAddresses = base.accessedAddresses ∧
      post.output = base.output ∧
      post.error = base.error ∧
      some sevm.code.toList = Prog.compile runtime := by
  let s := accOfStor (Devm.getStor base sevm.currentTarget)
  have hcountValue :
      base.getStorVal sevm.currentTarget depositCountSlot =
        Nat.toB256 s.count := by
    change (Devm.getStor base sevm.currentTarget).get depositCountSlot =
      Nat.toB256
        ((Devm.getStor base sevm.currentTarget).get depositCountSlot).toNat
    exact (Jaune.toB256_toNat _).symm
  obtain ⟨logged, mid, finalBase, finalMemory, hlogs, hstorVal, hstorMap,
      hbal, hloggedCode, hloadedKeys, hloggedAddresses, hloggedOutput,
      hloggedError, hmeta, hfinal, hendpointTo⟩ :=
    depositEndpoint_success_runCompiledTo
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
  obtain ⟨hcarrier⟩ := hfinal
  let branchValue :=
    accumulatedNode Bytes.sha256 (accOfStor stor).branch
      0 n depositDataRoot
  let post :=
    (afterSstore sevm finalBase (branchSlot n) branchValue).setMach
      ⟨[], finalMemory, G⟩
  have hendpointTo' : Func.RunCompiledTo
      (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[], Mem.empty,
          depositEndpointSuccessGas sevm base stor keys depositDataRoot n
            (s.count + 1) countCost G⟩)
      depositEndpoint (.ok post) := by
    simpa only [post, branchValue] using hendpointTo
  have hendpoint : Func.RunCompiled
      (runtime.main :: runtime.aux) sevm
      (base.setMach
        ⟨[], Mem.empty,
          depositEndpointSuccessGas sevm base stor keys depositDataRoot n
            (s.count + 1) countCost G⟩)
      depositEndpoint post :=
    Func.RunCompiled.of_runCompiledTo_ok hendpointTo'
  have hlengthWordNe : sevm.data.length.toB256 ≠ 0 := by
    intro hzero
    have hnat := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt hdataBound] at hnat
    simp only [B256.toNat_zero] at hnat
    have hhead := hdec.head
    omega
  have hroute := deposit_route_runCompiled hlengthWordNe hselector hendpoint
  have hrun : Prog.RunCompiled sevm
      (base.setMach
        ⟨[], Mem.empty,
          depositRuntimeSuccessGas sevm base stor keys depositDataRoot n
            (s.count + 1) countCost G⟩)
      runtime post := by
    simpa only [depositRuntimeSuccessGas] using hroute
  have hcountStor : stor =
      (Devm.getStor base sevm.currentTarget).set depositCountSlot
        (Nat.toB256 s.count + 1) := by
    calc
      stor = Devm.getStor
          (afterSstore sevm (afterSload sevm base depositCountSlot)
            depositCountSlot (Nat.toB256 s.count + 1))
          sevm.currentTarget := by simpa only [s] using hstor.symm
      _ = (Devm.getStor
          (afterSload sevm base depositCountSlot)
          sevm.currentTarget).set depositCountSlot
            (Nat.toB256 s.count + 1) :=
        Blanc.afterSstore_getStor_self _ _ _ _
      _ = (Devm.getStor base sevm.currentTarget).set depositCountSlot
          (Nat.toB256 s.count + 1) := by
        rw [Blanc.afterSload_getStor]
  refine ⟨post, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [s] using hrun
  · rfl
  · rfl
  · change
      (afterSstore sevm finalBase (branchSlot n) branchValue).logs =
        base.logs ++ [depositEventLog sevm.currentTarget ev]
    rw [Blanc.afterSstore_logs, hcarrier.logs, Blanc.afterSstore_logs,
      hmeta.logs]
    change logged.logs =
      base.logs ++ [depositEventLog sevm.currentTarget ev]
    exact hlogs
  · simpa only [s] using hcountStor
  · intro a
    by_cases ha : a = sevm.currentTarget
    · subst a
      simp only [if_pos]
      change Devm.getStor
        (afterSstore sevm finalBase (branchSlot n) branchValue)
          sevm.currentTarget = stor.set (branchSlot n) branchValue
      rw [Blanc.afterSstore_getStor_self, hcarrier.stor,
        Blanc.afterSstore_getStor_self, hmeta.storage]
      change
        ((Devm.getStor logged sevm.currentTarget).set depositCountSlot
          (Nat.toB256 s.count + 1)).set (branchSlot n) branchValue =
        stor.set (branchSlot n) branchValue
      rw [hstorMap sevm.currentTarget, Blanc.afterSload_getStor,
        ← hcountStor]
    · simp only [if_neg ha]
      change Devm.getStor
        (afterSstore sevm finalBase (branchSlot n) branchValue) a =
          Devm.getStor base a
      rw [Blanc.afterSstore_getStor_ne sevm finalBase (branchSlot n)
          branchValue a (Ne.symm ha),
        hcarrier.stor,
        Blanc.afterSstore_getStor_ne sevm mid depositCountSlot
          (Nat.toB256 s.count + 1) a (Ne.symm ha),
        hmeta.storage]
      change Devm.getStor logged a = Devm.getStor base a
      rw [hstorMap a, Blanc.afterSload_getStor]
  · intro a
    change
      (afterSstore sevm finalBase (branchSlot n) branchValue).getCode a =
        base.getCode a
    rw [Blanc.afterSstore_getCode, hcarrier.code,
      Blanc.afterSstore_getCode, hmeta.code]
    change logged.getCode a = base.getCode a
    rw [hloggedCode a, Blanc.afterSload_getCode]
  · change
      (afterSstore sevm finalBase (branchSlot n) branchValue).accessedAddresses =
        base.accessedAddresses
    rw [Blanc.afterSstore_accessedAddresses, hcarrier.addresses,
      Blanc.afterSstore_accessedAddresses, hmeta.accessedAddresses]
    change logged.accessedAddresses = base.accessedAddresses
    rw [hloggedAddresses, Blanc.afterSload_accessedAddresses]
  · change
      (afterSstore sevm finalBase (branchSlot n) branchValue).output =
        base.output
    rw [Blanc.afterSstore_output, hcarrier.output,
      Blanc.afterSstore_output, hmeta.output]
    change logged.output = base.output
    rw [hloggedOutput, Blanc.afterSload_output]
  · change
      (afterSstore sevm finalBase (branchSlot n) branchValue).error =
        base.error
    rw [Blanc.afterSstore_error, hcarrier.error,
      Blanc.afterSstore_error, hmeta.error]
    change logged.error = base.error
    rw [hloggedError, Blanc.afterSload_error]
  · rw [hcode, code_compile]

end Blanc.BeaconDeposit
