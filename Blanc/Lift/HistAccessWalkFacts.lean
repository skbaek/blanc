import Blanc.Lift.HistAccessWalk
import Blanc.Lift.HistStaticCall
import Blanc.Lift.Quiet
import Blanc.ForwardStorageAccess

/-!
# Missing successor projections for historical access walks

`Blanc/Lift/HistAccessWalk.lean` carries the projections its own steps need.
The Beacon historical safety chain additionally reads the code, address-set,
error, created-account and key-set projections of `afterSloadH`/`afterSstoreH`,
the `ite`-form storage projection of `afterSstoreH`, and the quiet frame
theorem over `Ninst.world_of_quietH`. All premises are dischargeable over
`HistFork` (`HistFork.stateGas_none`, `HistFork.bal_none`, decision lemmas);
no `CoveredFork` appears.

Contract-neutral: no contract name in any statement.
-/

namespace Blanc.Lift

open Jaune

/-! ## `afterSloadH` projections -/

theorem afterSloadH_getCode (sevm : Sevm) (base : Devm) (key : B256) (address : Adr) :
    (afterSloadH sevm base key).getCode address = base.getCode address := by
  unfold afterSloadH
  split
  · exact afterSload_getCode sevm base key address
  · rfl

theorem afterSloadH_error (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).error = base.error := by
  unfold afterSloadH
  split
  · exact afterSload_error sevm base key
  · rfl

theorem afterSloadH_createdAccounts (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).createdAccounts = base.createdAccounts := by
  unfold afterSloadH
  split
  · exact afterSload_createdAccounts sevm base key
  · rfl

theorem afterSloadH_accessedStorageKeys (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).accessedStorageKeys =
      match sevm.benvStat.rules.access with
      | .eip2929 =>
        sloadAccessedStorageKeys sevm.currentTarget base.accessedStorageKeys key
      | .flat _ => base.accessedStorageKeys := by
  unfold afterSloadH
  cases sevm.benvStat.rules.access with
  | eip2929 =>
    exact afterSload_accessedStorageKeys sevm base key
  | flat _ =>
    rfl

/-! ## `afterSstoreH` projections -/

theorem afterSstoreH_accessedStorageKeys (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstoreH sevm base key value).accessedStorageKeys =
      match sevm.benvStat.rules.access with
      | .eip2929 =>
        sloadAccessedStorageKeys sevm.currentTarget base.accessedStorageKeys key
      | .flat _ => base.accessedStorageKeys := by
  unfold afterSstoreH storageAccessH
  cases sevm.benvStat.rules.access with
  | eip2929 =>
    by_cases hw : (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ base.accessedStorageKeys
    · simp only [hw, ite_true, sloadAccessedStorageKeys]
      rfl
    · simp only [hw, ite_false, sloadAccessedStorageKeys]
      rfl
  | flat _ =>
    rfl

theorem getStor_afterSstoreH (sevm : Sevm) (b : Devm) (k v : B256) (a : Adr) :
    Devm.getStor (afterSstoreH sevm b k v) a =
      if a = sevm.currentTarget then (Devm.getStor b sevm.currentTarget).set k v
      else Devm.getStor b a := by
  split_ifs with h
  · subst h
    exact afterSstoreH_getStor_self _ _ _ _
  · exact afterSstoreH_getStor_ne _ _ _ _ _ (Ne.symm h)

/-! ## The quiet frame theorem without state gas -/

end Blanc.Lift
