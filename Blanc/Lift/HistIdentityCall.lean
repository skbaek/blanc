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

/-! ## World steps at a historical fork

The pool's walks name their fork premise once; these read `ri_sloadH` and friends from it. -/

section World

variable {b : Devm} {S : List B256} {M : Mem} {G : Nat}

theorem ri_sloadF {k : B256} {d : Devm} (hfork : HistFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (k :: S) M G) (.reg .sload) d) :
    ∃ G', d = St (afterSloadH sevm b k) (b.getStorVal sevm.currentTarget k :: S) M G' :=
  ri_sloadH hfork.bal_none h

end World

/-- Loads only, under the frame's actual access schedule. -/
inductive SloadsOnlyH (sevm : Sevm) (b : Devm) : Devm → Prop
  | refl : SloadsOnlyH sevm b b
  | sload {B : Devm} (h : SloadsOnlyH sevm b B) (k : B256) :
      SloadsOnlyH sevm b (afterSloadH sevm B k)

namespace SloadsOnlyH

variable {sevm : Sevm} {b B : Devm}

theorem getStor (h : SloadsOnlyH sevm b B) (a : Adr) : B.getStor a = b.getStor a := by
  induction h with
  | refl => rfl
  | sload _ k ih => rw [afterSloadH_getStor, ih]

theorem getCode (h : SloadsOnlyH sevm b B) (a : Adr) : B.getCode a = b.getCode a := by
  induction h with
  | refl => rfl
  | sload _ k ih => rw [afterSloadH_getCode, ih]

end SloadsOnlyH


end Blanc.Lift
