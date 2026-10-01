import Blanc.ForwardStorageAccess

/-! Exact selected SLOAD schedule costs, retaining each access's incoming base. -/

namespace Blanc

open Jaune

theorem sloadCost_le (sevm : Sevm) (base : Devm) (key : B256) :
    sloadCost sevm base key ≤ gasColdSload := by
  unfold sloadCost
  split <;> decide

/-- A finite ordered read schedule includes the incoming state at every read. -/
abbrev SloadSchedule := List (Devm × B256)

def sloadScheduleCost (sevm : Sevm) (schedule : SloadSchedule) : Nat :=
  (schedule.map fun read => sloadCost sevm read.1 read.2).sum

def sloadColdCount (sevm : Sevm) (schedule : SloadSchedule) : Nat :=
  (schedule.filter fun read => decide
    ((sevm.currentTarget,read.2) ∉ read.1.accessedStorageKeys)).length

theorem sloadScheduleCost_eq (sevm : Sevm) (schedule : SloadSchedule) :
    sloadScheduleCost sevm schedule =
      gasWarmAccess * schedule.length + (gasColdSload-gasWarmAccess) * sloadColdCount sevm schedule := by
  induction schedule with
  | nil => rfl
  | cons read rest ih =>
    by_cases warm : (sevm.currentTarget,read.2) ∈ read.1.accessedStorageKeys
    · have coldFalse : decide ((sevm.currentTarget,read.2) ∉ read.1.accessedStorageKeys) = false :=
        decide_eq_false (not_not_intro warm)
      simp only [sloadScheduleCost, List.map_cons, List.sum_cons, sloadCost,
        ite_eq_left warm, sloadColdCount, List.filter_cons, coldFalse,
        Bool.false_eq_true, ite_false, List.length_cons]
      change gasWarmAccess + sloadScheduleCost sevm rest = _
      rw [ih, Nat.mul_add, Nat.mul_one]
      simp only [sloadColdCount, gasWarmAccess, gasColdSload] at *
      omega
    · simp only [sloadScheduleCost, List.map_cons, List.sum_cons, sloadCost,
        ite_eq_right warm, sloadColdCount, List.filter_cons, decide_eq_true warm,
        ite_true, List.length_cons]
      change gasColdSload + sloadScheduleCost sevm rest = _
      rw [ih, Nat.mul_add, Nat.mul_one]
      simp only [sloadColdCount, gasWarmAccess, gasColdSload] at *
      omega

theorem sloadColdCount_le (sevm : Sevm) (schedule : SloadSchedule) :
    sloadColdCount sevm schedule ≤ schedule.length := List.length_filter_le _ _

theorem sloadScheduleCost_le (sevm : Sevm) (schedule : SloadSchedule) :
    sloadScheduleCost sevm schedule ≤ gasColdSload * schedule.length := by
  rw [sloadScheduleCost_eq]
  have bound := sloadColdCount_le sevm schedule
  simp only [gasWarmAccess, gasColdSload]
  omega

end Blanc
