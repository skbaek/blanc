import Blanc.Lift.FiniteCheckpoint
import Blanc.Lift.Weth9.Footprint

/-!
# WETH9's footprint invariant by a finite checker

`checkFoot rows s b` decides `FootInv (rowKeys rows) s b` for a row list of WETH9 keys with their
precomputed slot words: the contract-neutral footprint checker (`checkRows`, complete support over
the storage tree) plus the backing bound, where the tracked ledger is summed over the listed balance
rows only (`trackedSum_eq_rowsBooked`).  `checkHolder` adds, for one holder, that its balance row
is listed with at least a given amount and that its listed allowance rows read zero.
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift.FiniteCheckpoint

/-- The listed balance rows: each holder with its slot word. -/
def balRows : List (Key × B256) → List (Adr × B256)
  | [] => []
  | (.bal a, x) :: rows => (a, x) :: balRows rows
  | (.allow _ _, _) :: rows => balRows rows

theorem mem_balRows {a : Adr} {x : B256} :
    ∀ {rows : List (Key × B256)}, (a, x) ∈ balRows rows ↔ (Key.bal a, x) ∈ rows
  | [] => by simp only [balRows, List.not_mem_nil]
  | (.bal b, y) :: rows => by
    simp only [balRows, List.mem_cons, Prod.mk.injEq, Key.bal.injEq, mem_balRows]
  | (.allow o p, y) :: rows => by
    simp only [balRows, List.mem_cons, Prod.mk.injEq, reduceCtorEq, false_and, false_or,
      mem_balRows]

theorem balRows_holders_nodup :
    ∀ {rows : List (Key × B256)}, (rows.map Prod.fst).Nodup → ((balRows rows).map Prod.fst).Nodup
  | [], _ => List.nodup_nil
  | (.bal a, x) :: rows, h => by
    show (((a, x) :: balRows rows).map Prod.fst).Nodup
    simp only [List.map_cons, List.nodup_cons] at h ⊢
    refine ⟨fun ha => h.1 ?_, balRows_holders_nodup h.2⟩
    obtain ⟨r, hr, hra⟩ := List.mem_map.mp ha
    have hr' := mem_balRows.mp (show (a, r.2) ∈ balRows rows from hra ▸ hr)
    exact List.mem_map_of_mem (f := Prod.fst) hr'
  | (.allow _ _, _) :: rows, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    show ((balRows rows).map Prod.fst).Nodup
    exact balRows_holders_nodup h.2

/-- The words at the listed balance rows, summed. -/
def rowsBooked (rows : List (Key × B256)) (s : Stor) : Nat :=
  ((balRows rows).map fun r => (s.get r.2).toNat).sum

/-- The checker: the footprint over the listed keys and the listed balances backed by `b`. -/
def checkFoot (rows : List (Key × B256)) (s : Stor) (b : B256) : Bool :=
  checkRows Key.slot fixedSlots rows s && decide (rowsBooked rows s ≤ b.toNat)

/-- Over sound rows, the tracked ledger is the sum of the listed balance words. -/
theorem trackedSum_eq_rowsBooked {rows : List (Key × B256)} {s : Stor}
    (h : RowsSound Key.slot fixedSlots rows s) : trackedSum (rowKeys rows) s = rowsBooked rows s := by
  have covers : FootprintCovers ((balRows rows).map Prod.fst) (tracked (rowKeys rows) s) := by
    intro a ha
    by_cases hK : rowKeys rows (.bal a)
    · obtain ⟨r, hr, hra⟩ := List.mem_map.mp hK
      have hr' : (Key.bal a, r.2) ∈ rows := hra ▸ hr
      exact List.mem_map_of_mem (f := Prod.fst) (mem_balRows.mpr hr')
    · exact absurd (tracked_of_not hK) ha
  unfold trackedSum
  rw [← footprintSum_eq_sum (balRows_holders_nodup h.nodup) covers]
  unfold footprintSum rowsBooked
  rw [List.map_map]
  have pointwise : ∀ r ∈ balRows rows,
      ((fun a => (tracked (rowKeys rows) s a).toNat) ∘ Prod.fst) r = (s.get r.2).toNat := by
    intro r hr
    have hrow : (Key.bal r.1, r.2) ∈ rows := mem_balRows.mp hr
    have hK : rowKeys rows (.bal r.1) := List.mem_map_of_mem (f := Prod.fst) hrow
    have hword : balSlot r.1 = r.2 := h.word _ hrow
    simp only [Function.comp_apply, tracked_self hK, hword]
  rw [List.map_congr_left pointwise]

/-- **Soundness of the WETH9 footprint checker.** -/
theorem checkFoot_sound {rows : List (Key × B256)} {s : Stor} {b : B256}
    (h : checkFoot rows s b = true) : FootInv (rowKeys rows) s b ∧ RowsSound Key.slot fixedSlots rows s := by
  simp only [checkFoot, Bool.and_eq_true, decide_eq_true_eq] at h
  have sound := checkRows_sound h.1
  refine ⟨⟨sound.support, sound.inj, sound.apart, ?_⟩, sound⟩
  rw [trackedSum_eq_rowsBooked sound]
  exact h.2

/-- One holder's rows: its balance row is listed with at least `n`, and each of its listed
allowance rows reads zero. -/
def checkHolder (rows : List (Key × B256)) (s : Stor) (a : Adr) (n : Nat) : Bool :=
  rows.any (fun r => decide (r.1 = .bal a) && decide (n ≤ (s.get r.2).toNat)) &&
    rows.all (fun r => match r.1 with
      | .allow o _ => decide (o ≠ a) || decide (s.get r.2 = 0)
      | .bal _ => true)

theorem checkHolder_sound {rows : List (Key × B256)} {s : Stor} {a : Adr} {n : Nat}
    (sound : RowsSound Key.slot fixedSlots rows s) (h : checkHolder rows s a n = true) :
    rowKeys rows (.bal a) ∧ n ≤ (s.get (balSlot a)).toNat ∧
      ∀ g, rowKeys rows (.allow a g) → s.get (allowSlot a g) = 0 := by
  simp only [checkHolder, Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨r, hr, hkey, hn⟩, hall⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨r, hr, hkey⟩
  · have hword : Key.slot r.1 = r.2 := sound.word r hr
    rw [hkey] at hword
    change balSlot a = r.2 at hword
    rw [hword]
    exact hn
  · intro g hg
    obtain ⟨r', hr', hkey'⟩ := List.mem_map.mp hg
    have hword : Key.slot r'.1 = r'.2 := sound.word r' hr'
    have hcheck := hall r' hr'
    rw [hkey'] at hword hcheck
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with hne | hzero
    · exact absurd rfl hne
    · change allowSlot a g = r'.2 at hword
      rw [hword]
      exact hzero

end Blanc.Lift.Weth9
