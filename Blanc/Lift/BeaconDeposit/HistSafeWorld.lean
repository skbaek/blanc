import Blanc.Lift.BeaconDeposit.BodySpec
import Blanc.Lift.HistAccessWalkFacts
import Blanc.Lift.HistShaWalk

/-!
# The Beacon body's world frames over a historical frame

The historical counterparts of the world vocabulary the modern safety segments share
(`Keep`, `LoopBase`, `ShaReady.keep`, `keep_afterSstore_sload_twice`), over the successors
`afterSloadH`/`afterSstoreH` of the frame's actual access schedule:

* `ShaReadyH.keep` — the historical SHA-256 premises across a `Keep`;
* `LoopBaseH` — what the insertion loop keeps of its starting base: `LoopBase` without the
  key-set field, which is false under flat access (where `afterSloadH` is the base itself) and
  which the loop's closing step never reads; `LoopBaseH.step` over `Keep (afterSloadH …)`;
* `keep_afterSstoreH_sloadH_twice` — the count increment's base, cased on the access schedule
  (the identity under flat access, an already-present key under EIP-2929).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

theorem _root_.Blanc.Lift.ShaReadyH.keep {sevm : Sevm} {b b' : Devm} (h : ShaReadyH sevm b)
    (hk : Keep b b') : ShaReadyH sevm b' :=
  h.of_eq hk.code hk.addrs

/-- What the insertion loop keeps of the base `b₀` it started from over a historical frame:
storage, code, the warm accounts, logs, output and error. -/
structure LoopBaseH (b₀ b : Devm) : Prop where
  stor : ∀ a, Devm.getStor b a = Devm.getStor b₀ a
  code : ∀ a, b.getCode a = b₀.getCode a
  addrs : b.accessedAddresses = b₀.accessedAddresses
  logs : b.logs = b₀.logs
  output : b.output = b₀.output
  error : b.error = b₀.error

theorem LoopBaseH.refl (b : Devm) : LoopBaseH b b :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩

theorem LoopBaseH.step {sevm : Sevm} {b₀ b b' : Devm} {k : B256}
    (hL : LoopBaseH b₀ b) (hK : Keep (afterSloadH sevm b k) b') : LoopBaseH b₀ b' where
  stor a := by rw [hK.stor, afterSloadH_getStor, hL.stor]
  code a := by rw [hK.code, afterSloadH_getCode, hL.code]
  addrs := by rw [hK.addrs, afterSloadH_accessedAddresses, hL.addrs]
  logs := by rw [hK.logs, afterSloadH_logs, hL.logs]
  output := by rw [hK.output, afterSloadH_output, hL.output]
  error := by rw [hK.error, afterSloadH_error, hL.error]

/-- The count increment's base: two `SLOAD`s of the key before its `SSTORE` change nothing the
body observes, under either access schedule. -/
theorem keep_afterSstoreH_sloadH_twice {sevm : Sevm} {b : Devm} {k v : B256} :
    Keep (afterSstoreH sevm b k v)
      (afterSstoreH sevm (afterSloadH sevm (afterSloadH sevm b k) k) k v) := by
  refine ⟨fun a => ?_, fun a => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [getStor_afterSstoreH, getStor_afterSstoreH, afterSloadH_getStor, afterSloadH_getStor,
      afterSloadH_getStor, afterSloadH_getStor]
  · rw [afterSstoreH_getCode, afterSstoreH_getCode, afterSloadH_getCode, afterSloadH_getCode]
  · rw [afterSstoreH_accessedAddresses, afterSstoreH_accessedAddresses,
      afterSloadH_accessedAddresses, afterSloadH_accessedAddresses]
  · rw [afterSstoreH_accessedStorageKeys, afterSstoreH_accessedStorageKeys,
      afterSloadH_accessedStorageKeys, afterSloadH_accessedStorageKeys]
    cases sevm.benvStat.rules.access with
    | flat _ => rfl
    | eip2929 =>
      dsimp only
      unfold sloadAccessedStorageKeys
      by_cases hk : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ b.accessedStorageKeys
      · simp only [hk, ↓reduceIte]
      · have hin : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈
            b.accessedStorageKeys.insert ⟨sevm.currentTarget, k⟩ := by
          simp only [Std.HashSet.mem_insert, BEq.rfl, true_or]
        simp only [hk, ↓reduceIte, hin]
  · rw [afterSstoreH_logs, afterSstoreH_logs, afterSloadH_logs, afterSloadH_logs]
  · rw [afterSstoreH_output, afterSstoreH_output, afterSloadH_output, afterSloadH_output]
  · rw [afterSstoreH_error, afterSstoreH_error, afterSloadH_error, afterSloadH_error]
  · rw [afterSstoreH_createdAccounts, afterSstoreH_createdAccounts,
      afterSloadH_createdAccounts, afterSloadH_createdAccounts]

end Blanc.Lift.BeaconDeposit
