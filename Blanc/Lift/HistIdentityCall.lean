import Blanc.Lift.IdentityCallGas
import Blanc.Lift.HistAccessWalkFacts
import Blanc.HistoricalFork

/-!
# Identity readiness across the historical storage steps

`IdReadyH` (`IdentityCall.lean`) across `afterSloadH` and `afterSstoreH`. Nothing here mentions a
contract.
-/

namespace Blanc.Lift

open Jaune

variable {sevm : Sevm}

/-- On a covered fork the historical readiness is the modern one. -/
theorem IdReadyH.toCovered {b : Devm} (h : IdReadyH sevm b) (fork : CoveredFork sevm.benvStat.fork) :
    IdReady sevm b :=
  ⟨h.nodeleg, h.warm, h.pre, fork⟩

theorem IdReadyH.afterSload {b : Devm} (h : IdReadyH sevm b) (k : B256) :
    IdReadyH sevm (afterSload sevm b k) :=
  ⟨by rw [afterSload_getCode]; exact h.nodeleg,
    by rw [afterSload_accessedAddresses]; exact h.warm, h.pre, h.stateGas⟩

theorem IdReadyH.afterSstore {b : Devm} (h : IdReadyH sevm b) (k v : B256) :
    IdReadyH sevm (afterSstore sevm b k v) :=
  ⟨by rw [afterSstore_getCode]; exact h.nodeleg,
    by rw [afterSstore_accessedAddresses]; exact h.warm, h.pre, h.stateGas⟩

theorem IdReadyH.afterSloadH {b : Devm} (h : IdReadyH sevm b) (k : B256) :
    IdReadyH sevm (afterSloadH sevm b k) :=
  ⟨by rw [afterSloadH_getCode]; exact h.nodeleg, by
    have e := afterSloadH_accessedAddresses sevm b k
    rw [e]; exact h.warm, h.pre, h.stateGas⟩

theorem IdReadyH.afterSstoreH {b : Devm} (h : IdReadyH sevm b) (k v : B256) :
    IdReadyH sevm (afterSstoreH sevm b k v) :=
  ⟨by rw [afterSstoreH_getCode]; exact h.nodeleg, by
    have e := afterSstoreH_accessedAddresses sevm b k v
    rw [e]; exact h.warm, h.pre, h.stateGas⟩

/-! ## World steps at a historical fork

The pool's walks name their fork premise once; these read `ri_sloadH` and friends from it. -/

section World

variable {b : Devm} {S : List B256} {M : Mem} {G : Nat}

theorem ri_sloadF {k : B256} {d : Devm} (hfork : HistFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (k :: S) M G) (.reg .sload) d) :
    ∃ G', d = St (afterSloadH sevm b k) (b.getStorVal sevm.currentTarget k :: S) M G' :=
  ri_sloadH hfork.bal_none h

theorem ri_sstoreF {k v : B256} {d : Devm} (hfork : HistFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (k :: v :: S) M G) (.reg .sstore) d) :
    ∃ G', d = St (afterSstoreH sevm b k v) S M G' :=
  ri_sstoreH hfork.stateGas_none hfork.bal_none h

theorem ri_sstore_nonstaticF {k v : B256} {d : Devm} (hfork : HistFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (k :: v :: S) M G) (.reg .sstore) d) :
    sevm.isStatic = false :=
  ri_sstore_nonstaticH hfork.stateGas_none h

theorem getStorVal_afterSstoreH_self {k v : B256} (x : B256) :
    (afterSstoreH sevm b k v).getStorVal sevm.currentTarget x =
      ((b.getStor sevm.currentTarget).set k v).get x := by
  rw [getStorVal_eq_getStor, afterSstoreH_getStor_self]

theorem getStorVal_afterSstoreH_ne {k v x : B256} (h : k ≠ x) :
    (afterSstoreH sevm b k v).getStorVal sevm.currentTarget x =
      b.getStorVal sevm.currentTarget x := by
  rw [getStorVal_afterSstoreH_self, Stor.get_set_ne _ h, getStorVal_eq_getStor]

end World

/-- Loads only, under the frame's actual access schedule. -/
inductive SloadsOnlyH (sevm : Sevm) (b : Devm) : Devm → Prop
  | refl : SloadsOnlyH sevm b b
  | sload {B : Devm} (h : SloadsOnlyH sevm b B) (k : B256) :
      SloadsOnlyH sevm b (afterSloadH sevm B k)

theorem afterSloadH_getStorVal (sevm : Sevm) (b : Devm) (k : B256) (a : Adr) (x : B256) :
    (afterSloadH sevm b k).getStorVal a x = b.getStorVal a x := by
  rw [getStorVal_eq_getStor, getStorVal_eq_getStor, afterSloadH_getStor]

namespace SloadsOnlyH

variable {sevm : Sevm} {b B : Devm}

theorem getStor (h : SloadsOnlyH sevm b B) (a : Adr) : B.getStor a = b.getStor a := by
  induction h with
  | refl => rfl
  | sload _ k ih => rw [afterSloadH_getStor, ih]

theorem logs (h : SloadsOnlyH sevm b B) : B.logs = b.logs := by
  induction h with
  | refl => rfl
  | sload _ k ih => rw [afterSloadH_logs, ih]

theorem output (h : SloadsOnlyH sevm b B) : B.output = b.output := by
  induction h with
  | refl => rfl
  | sload _ k ih => rw [afterSloadH_output, ih]

theorem getCode (h : SloadsOnlyH sevm b B) (a : Adr) : B.getCode a = b.getCode a := by
  induction h with
  | refl => rfl
  | sload _ k ih => rw [afterSloadH_getCode, ih]

theorem trans {B' : Devm} (h : SloadsOnlyH sevm b B) (h' : SloadsOnlyH sevm B B') :
    SloadsOnlyH sevm b B' := by
  induction h' with
  | refl => exact h
  | sload _ k ih => exact ih.sload k

theorem idReady (h : SloadsOnlyH sevm b B) (hid : IdReadyH sevm b) : IdReadyH sevm B := by
  induction h with
  | refl => exact hid
  | sload _ k ih => exact ih.afterSloadH k

end SloadsOnlyH


end Blanc.Lift
