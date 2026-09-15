-- DripPreservation.lean : endpoint-local preservation of DRIP storage accounting.

import Blanc.DripInvariant
import Blanc.DripEndpoints

namespace Blanc

open Jaune

namespace Drip

/-- The guarded word-level fresh index has DRIP's established natural image. -/
theorem freshChi_toNat (chi : B256) (elapsed : Nat)
    (hguards : B256.RPowGuards scale half rate elapsed)
    (hnof : B256.Nofm chi (B256.rpow scale half rate elapsed)) :
    ((B256.rpow scale half rate elapsed * chi) / scale).toNat =
      freshNat chi.toNat elapsed := by
  unfold freshNat
  rw [B256.mul_comm, B256.toNat_div (by decide +kernel),
    B256.toNat_mul_eq_of_nofm hnof, drip_rpow_word_exact elapsed hguards]

/-- Successful fresh-index composition cannot lower an invariant index. -/
theorem AccountingInv.fresh_lower {s : Stor} (h : AccountingInv s)
    (elapsed : Nat)
    (hguards : B256.RPowGuards scale half rate elapsed)
    (hnof : B256.Nofm (s.get chiSlot)
      (B256.rpow scale half rate elapsed)) :
    scale.toNat ≤
      ((B256.rpow scale half rate elapsed * s.get chiSlot) / scale).toNat := by
  rw [freshChi_toNat _ _ hguards hnof]
  exact h.chi_lower.trans (freshNat_mono _ _)

/-- Replacing only the two scalar accrual words preserves full-address
conservation. -/
theorem AccountingInv.drip_write {s : Stor} {fresh now : B256}
    (h : AccountingInv s)
    (hlower : scale.toNat ≤ fresh.toNat)
    (hupper : fresh.toNat ≤ maxChi.toNat) :
    AccountingInv ((s.set chiSlot fresh).set rhoSlot now) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold chiN
    rw [Stor.get_set_ne _ scalarSlots_distinct.1.symm _, Stor.get_set_self]
    exact hlower
  · unfold chiN
    rw [Stor.get_set_ne _ scalarSlots_distinct.1.symm _, Stor.get_set_self]
    exact hupper
  · unfold totalN
    rw [Stor.get_set_ne _ scalarSlots_distinct.2.2 _,
      Stor.get_set_ne _ scalarSlots_distinct.2.1 _]
    exact h.total_upper
  · have htotal : totalN ((s.set chiSlot fresh).set rhoSlot now) = totalN s := by
      unfold totalN
      rw [Stor.get_set_ne _ scalarSlots_distinct.2.2 _,
        Stor.get_set_ne _ scalarSlots_distinct.2.1 _]
    have hsum : balSum ((s.set chiSlot fresh).set rhoSlot now) = balSum s := by
      unfold balSum
      rw [Stor.rest_set_rhoSlot, Stor.rest_set_chiSlot]
    rw [hsum, htotal]
    exact h.balSum_eq
  · intro holder
    unfold pieN
    rw [Stor.get_set_ne _ (pieSlot_ne_rhoSlot holder).symm _,
      Stor.get_set_ne _ (pieSlot_ne_chiSlot holder).symm _]
    exact h.row_upper holder

/-- The paired caller-row and total-unit mint preserves full-address
conservation once the endpoint's checked additions are known not to wrap. -/
theorem AccountingInv.join_ledger_write {s : Stor} {holder : Adr} {units : B256}
    (h : AccountingInv s)
    (hrowNof : B256.Nof (s.get (pieSlot holder)) units)
    (htotalNof : B256.Nof units (s.get totalUnitsSlot))
    (hrowCap : (s.get (pieSlot holder) + units).toNat ≤ maxUnits.toNat)
    (htotalCap : (units + s.get totalUnitsSlot).toNat ≤ maxPie.toNat) :
    AccountingInv
      ((s.set (pieSlot holder) (s.get (pieSlot holder) + units)).set
        totalUnitsSlot (units + s.get totalUnitsSlot)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold chiN
    rw [Stor.get_set_ne _ scalarSlots_distinct.2.1.symm _,
      Stor.get_set_ne _ (pieSlot_ne_chiSlot holder)]
    exact h.chi_lower
  · unfold chiN
    rw [Stor.get_set_ne _ scalarSlots_distinct.2.1.symm _,
      Stor.get_set_ne _ (pieSlot_ne_chiSlot holder)]
    exact h.chi_upper
  · unfold totalN
    rw [Stor.get_set_self]
    exact htotalCap
  · unfold balSum
    rw [Stor.rest_set_totalUnitsSlot]
    let row := s.get (pieSlot holder)
    have hrow :
        (Stor.rest (s.set (pieSlot holder) (row + units)) holder).toNat =
          (Stor.rest s holder).toNat + units.toNat := by
      change ((s.set holder.toB256 (row + units)).get holder.toB256).toNat =
        (s.get holder.toB256).toNat + units.toNat
      rw [Stor.get_set_self, B256.toNat_add_eq_of_nof _ _ hrowNof]
      rfl
    have hrest : ∀ b : Adr, b ≠ holder →
        Stor.rest (s.set (pieSlot holder) (row + units)) b = Stor.rest s b := by
      intro b hb
      exact Stor.rest_set_ne s hb _
    calc
      balSum (s.set (pieSlot holder) (row + units)) = balSum s + units.toNat := by
        exact sum_eq_add_of_row_add hrow hrest
      _ = totalN s + units.toNat := by rw [h.balSum_eq]
      _ = units.toNat + totalN s := Nat.add_comm _ _
      _ = totalN
          ((s.set (pieSlot holder) (row + units)).set totalUnitsSlot
            (units + s.get totalUnitsSlot)) := by
        unfold totalN
        rw [Stor.get_set_self, B256.toNat_add_eq_of_nof _ _ htotalNof]
  · intro b
    by_cases hb : b = holder
    · subst b
      unfold pieN
      rw [Stor.get_set_ne _ (pieSlot_ne_totalUnitsSlot holder).symm _,
        Stor.get_set_self]
      exact hrowCap
    · unfold pieN
      rw [Stor.get_set_ne _ (pieSlot_ne_totalUnitsSlot b).symm _,
        Stor.get_set_ne _ (fun heq => hb (pieSlot_injective heq).symm) _]
      exact h.row_upper b

/-- The paired caller-row and total-unit burn preserves full-address
conservation at the exact pre-callback settlement boundary. -/
theorem AccountingInv.exit_ledger_write {s : Stor} {holder : Adr} {units : B256}
    (h : AccountingInv s)
    (hrowCover : units ≤ s.get (pieSlot holder))
    (htotalCover : units ≤ s.get totalUnitsSlot) :
    AccountingInv
      ((s.set (pieSlot holder) (s.get (pieSlot holder) - units)).set
        totalUnitsSlot (s.get totalUnitsSlot - units)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold chiN
    rw [Stor.get_set_ne _ scalarSlots_distinct.2.1.symm _,
      Stor.get_set_ne _ (pieSlot_ne_chiSlot holder)]
    exact h.chi_lower
  · unfold chiN
    rw [Stor.get_set_ne _ scalarSlots_distinct.2.1.symm _,
      Stor.get_set_ne _ (pieSlot_ne_chiSlot holder)]
    exact h.chi_upper
  · unfold totalN
    rw [Stor.get_set_self, B256.toNat_sub_eq_of_le _ _ htotalCover]
    exact Nat.sub_le _ _ |>.trans h.total_upper
  · unfold balSum
    rw [Stor.rest_set_totalUnitsSlot]
    let row := s.get (pieSlot holder)
    have hrow :
        (Stor.rest (s.set (pieSlot holder) (row - units)) holder).toNat =
          (Stor.rest s holder).toNat - units.toNat := by
      change ((s.set holder.toB256 (row - units)).get holder.toB256).toNat =
        (s.get holder.toB256).toNat - units.toNat
      rw [Stor.get_set_self, B256.toNat_sub_eq_of_le _ _ hrowCover]
      rfl
    have hrest : ∀ b : Adr, b ≠ holder →
        Stor.rest (s.set (pieSlot holder) (row - units)) b = Stor.rest s b := by
      intro b hb
      exact Stor.rest_set_ne s hb _
    have hrowCoverN : units.toNat ≤ (Stor.rest s holder).toNat := by
      change units.toNat ≤ (s.get (pieSlot holder)).toNat
      exact B256.toNat_le_toNat hrowCover
    calc
      balSum (s.set (pieSlot holder) (row - units)) = balSum s - units.toNat := by
        exact sum_eq_sub_of_row_sub hrowCoverN hrow hrest
      _ = totalN s - units.toNat := by rw [h.balSum_eq]
      _ = totalN
          ((s.set (pieSlot holder) (row - units)).set totalUnitsSlot
            (s.get totalUnitsSlot - units)) := by
        unfold totalN
        rw [Stor.get_set_self, B256.toNat_sub_eq_of_le _ _ htotalCover]
  · intro b
    by_cases hb : b = holder
    · subst b
      unfold pieN
      rw [Stor.get_set_ne _ (pieSlot_ne_totalUnitsSlot holder).symm _,
        Stor.get_set_self, B256.toNat_sub_eq_of_le _ _ hrowCover]
      exact (Nat.sub_le _ _).trans (h.row_upper holder)
    · unfold pieN
      rw [Stor.get_set_ne _ (pieSlot_ne_totalUnitsSlot b).symm _,
        Stor.get_set_ne _ (fun heq => hb (pieSlot_injective heq).symm) _]
      exact h.row_upper b

/-- A successful `join`'s unit quotient cannot exceed its bounded assets:
the compiled fresh index is at least the scale, so the exact floor division
is bounded by the value after the runtime's own multiplication no-wrap check. -/
theorem join_units_le_value {value fresh units : B256}
    (hunits : units = scale * value / fresh)
    (hfreshLower : scale.toNat ≤ fresh.toNat)
    (hmul : B256.Nofm scale value) : units.toNat ≤ value.toNat := by
  have hfresh : fresh ≠ 0 := by
    intro hzero
    have hscalePos : 0 < scale.toNat := by
      rw [scale_literal]
      decide +kernel
    apply (Nat.ne_of_gt hscalePos)
    apply Nat.eq_zero_of_le_zero
    rw [hzero, B256.toNat_zero] at hfreshLower
    exact hfreshLower
  rw [hunits, B256.toNat_div hfresh, B256.toNat_mul_eq_of_nofm hmul]
  apply Nat.div_le_of_le_mul
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right value.toNat hfreshLower

/-- The actual asset guard supplies the multiplication no-wrap fact used by
the unit quotient; this is independent of the later wrapped-word cap checks. -/
theorem join_scale_value_nofm {value : B256}
    (hasset : ¬ maxAsset < value) : B256.Nofm scale value := by
  unfold B256.Nofm
  apply lt_of_le_of_lt
    (Nat.mul_le_mul_left scale.toNat
      (B256.toNat_le_toNat (le_of_not_gt hasset)))
  rw [scale_literal, maxAsset_literal]
  decide +kernel

/-- The actual `join` effect preserves full-address accounting.  Its two
addition no-wrap facts are derived from the guarded operands, never inferred
from a post-addition cap that a wrapped word could also satisfy. -/
theorem AccountingInv.join_write_of_effect {s : Stor} {holder : Adr}
    {value fresh units now : B256} {elapsed : Nat}
    (h : AccountingInv s)
    (hasset : ¬ maxAsset < value)
    (hguards : B256.RPowGuards scale half rate elapsed)
    (hnofFresh : B256.Nofm (s.get chiSlot)
      (B256.rpow scale half rate elapsed))
    (hcapFresh : ¬ maxChi < fresh)
    (hfresh : fresh =
      (B256.rpow scale half rate elapsed * s.get chiSlot) / scale)
    (hunits : units = scale * value / fresh)
    (hrowCap : ¬ maxUnits < s.get (pieSlot holder) + units)
    (htotalCap : ¬ maxPie < units + s.get totalUnitsSlot) :
    AccountingInv
      ((((s.set chiSlot fresh).set rhoSlot now).set (pieSlot holder)
          (s.get (pieSlot holder) + units)).set totalUnitsSlot
        (units + s.get totalUnitsSlot)) := by
  have hfreshLower : scale.toNat ≤ fresh.toNat := by
    rw [hfresh]
    exact h.fresh_lower elapsed hguards hnofFresh
  have hfreshUpper : fresh.toNat ≤ maxChi.toNat :=
    B256.toNat_le_toNat (le_of_not_gt hcapFresh)
  have hscaleValueNof : B256.Nofm scale value :=
    join_scale_value_nofm hasset
  have hunitLeValue : units.toNat ≤ value.toNat :=
    join_units_le_value hunits hfreshLower hscaleValueNof
  have hunitUpper : units.toNat ≤ maxAsset.toNat :=
    hunitLeValue.trans (B256.toNat_le_toNat (le_of_not_gt hasset))
  have hrowNof : B256.Nof (s.get (pieSlot holder)) units := by
    unfold B256.Nof
    exact lt_of_le_of_lt
      (Nat.add_le_add (h.row_upper holder) hunitUpper) (by
        rw [maxUnits_literal, maxAsset_literal]
        decide +kernel)
  have htotalNof : B256.Nof units (s.get totalUnitsSlot) := by
    unfold B256.Nof
    exact lt_of_le_of_lt
      (Nat.add_le_add hunitUpper h.total_upper) (by
        rw [maxAsset_literal, maxPie_literal]
        decide +kernel)
  have hrowCapN : (s.get (pieSlot holder) + units).toNat ≤ maxUnits.toNat :=
    B256.toNat_le_toNat (le_of_not_gt hrowCap)
  have htotalCapN : (units + s.get totalUnitsSlot).toNat ≤ maxPie.toNat :=
    B256.toNat_le_toNat (le_of_not_gt htotalCap)
  let accrued := (s.set chiSlot fresh).set rhoSlot now
  have hAccrued : AccountingInv accrued :=
    h.drip_write hfreshLower hfreshUpper
  have hrowNofAccrued : B256.Nof (accrued.get (pieSlot holder)) units := by
    dsimp [accrued]
    rw [Stor.get_set_ne _ (pieSlot_ne_rhoSlot holder).symm _,
      Stor.get_set_ne _ (pieSlot_ne_chiSlot holder).symm _]
    exact hrowNof
  have htotalNofAccrued : B256.Nof units (accrued.get totalUnitsSlot) := by
    dsimp [accrued]
    rw [Stor.get_set_ne _ scalarSlots_distinct.2.2 _,
      Stor.get_set_ne _ scalarSlots_distinct.2.1 _]
    exact htotalNof
  have hrowCapAccrued :
      (accrued.get (pieSlot holder) + units).toNat ≤ maxUnits.toNat := by
    dsimp [accrued]
    rw [Stor.get_set_ne _ (pieSlot_ne_rhoSlot holder).symm _,
      Stor.get_set_ne _ (pieSlot_ne_chiSlot holder).symm _]
    exact hrowCapN
  have htotalCapAccrued :
      (units + accrued.get totalUnitsSlot).toNat ≤ maxPie.toNat := by
    dsimp [accrued]
    rw [Stor.get_set_ne _ scalarSlots_distinct.2.2 _,
      Stor.get_set_ne _ scalarSlots_distinct.2.1 _]
    exact htotalCapN
  simpa only [accrued,
    Stor.get_set_ne _ (pieSlot_ne_rhoSlot holder).symm _,
    Stor.get_set_ne _ (pieSlot_ne_chiSlot holder).symm _,
    Stor.get_set_ne _ scalarSlots_distinct.2.2 _,
    Stor.get_set_ne _ scalarSlots_distinct.2.1 _] using
    hAccrued.join_ledger_write hrowNofAccrued htotalNofAccrued
      hrowCapAccrued htotalCapAccrued

end Drip

end Blanc
