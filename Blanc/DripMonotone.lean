-- DripMonotone.lean : DRIP's monotone clock and index as a storage invariant.

import Blanc.DripSound

/-!
# R4: the accrued index and the accrual clock never decrease

`MonoInv chi0 rho0` strengthens `AccountingInv` by two lower bounds: the
accrued index is at least `chi0` and the last-accrual timestamp is at least
`rho0`.  It is a unary, storage-only invariant, so it rides DRIP's existing
execution ladder through `ContractSpec.ofStorageOnly` with no relational
carrier: instantiated at a root state's own `chiN`/`rhoN`, preservation *is*
monotonicity.

Every successful accruing endpoint (`drip`, `join`, `exit`) writes the fresh
index and the block timestamp.  The index cannot fall because the guarded
fresh index is `freshNat chi elapsed ≥ chi` (`freshNat_mono`, floor
composition with a base-preserving factor — no exponent-monotonicity appeal).
The clock cannot fall because the endpoint's own runtime guard `¬ now < rho`
precedes the `rho := now` write.  No premise states that the index is fresh or
constrains any post-state; both facts come from the endpoint's source walk
through `StepClosed`.

What this module does NOT say: nothing about block-timestamp monotonicity (a
block with an earlier timestamp makes every accruing call revert, leaving `rho`
in place), and nothing yet about named execution rungs or configured-history
projections; those consume `dripMonoSpec_preserves` in a later module.
-/

namespace Blanc

open Jaune

namespace Drip

/-- DRIP's accounting invariant together with lower bounds `chi0` on the
accrued index and `rho0` on the accrual clock. -/
def MonoInv (chi0 rho0 : Nat) (s : Stor) : Prop :=
  AccountingInv s ∧ chi0 ≤ chiN s ∧ rho0 ≤ rhoN s

/-- DRIP's storage-only adapter for the monotone invariant. -/
def dripMonoSpec (chi0 rho0 : Nat) : ContractSpec :=
  ContractSpec.ofStorageOnly runtime (MonoInv chi0 rho0)

/-- The accrual write keeps both lower bounds: the index becomes the guarded
fresh index, which is at least the old index, and the clock becomes `now`,
which the endpoint's guard puts at or above the old clock. -/
private theorem monoInv_accrual {chi0 rho0 : Nat} {s : Stor}
    {fresh now : B256} {elapsed : Nat}
    (hchi : chi0 ≤ chiN s) (hrho : rho0 ≤ rhoN s)
    (hclock : ¬ now < s.get rhoSlot)
    (hguards : B256.RPowGuards scale half rate elapsed)
    (hnof : B256.Nofm (s.get chiSlot) (B256.rpow scale half rate elapsed))
    (hfresh : fresh = (B256.rpow scale half rate elapsed * s.get chiSlot) / scale) :
    chi0 ≤ chiN ((s.set chiSlot fresh).set rhoSlot now) ∧
      rho0 ≤ rhoN ((s.set chiSlot fresh).set rhoSlot now) := by
  constructor
  · unfold chiN
    rw [Stor.get_set_ne _ scalarSlots_distinct.1.symm _, Stor.get_set_self, hfresh,
      freshChi_toNat _ _ hguards hnof]
    exact hchi.trans (freshNat_mono _ _)
  · unfold rhoN
    rw [Stor.get_set_self]
    exact hrho.trans (B256.toNat_le_toNat (le_of_not_gt hclock))

/-- A paired row/total write after the accrual leaves both scalar words alone. -/
private theorem chiN_rhoN_ledger_write (s : Stor) (holder : Adr) (row total : B256) :
    chiN ((s.set (pieSlot holder) row).set totalUnitsSlot total) = chiN s ∧
      rhoN ((s.set (pieSlot holder) row).set totalUnitsSlot total) = rhoN s := by
  constructor
  · unfold chiN
    rw [Stor.get_set_ne _ scalarSlots_distinct.2.1.symm _,
      Stor.get_set_ne _ (pieSlot_ne_chiSlot holder) _]
  · unfold rhoN
    rw [Stor.get_set_ne _ scalarSlots_distinct.2.2.symm _,
      Stor.get_set_ne _ (pieSlot_ne_rhoSlot holder) _]

/-- `MonoInv` is step-closed: the accounting part is `accountingInv_stepClosed`,
the index bound follows from `freshNat_mono`, and the clock bound from each
endpoint's runtime guard `¬ now < rho`. -/
theorem monoInv_stepClosed (chi0 rho0 : Nat) : StepClosed (MonoInv chi0 rho0) where
  drip := by
    intro s fresh now elapsed h hclock hguards hnof hfresh hcap
    exact ⟨accountingInv_stepClosed.drip h.1 hclock hguards hnof hfresh hcap,
      monoInv_accrual h.2.1 h.2.2 hclock hguards hnof hfresh⟩
  join := by
    intro s holder value fresh units now elapsed h hclock hguards hnof hfresh hcap
      hasset hunits hrowCap htotalCap
    have hmono := monoInv_accrual h.2.1 h.2.2 hclock hguards hnof hfresh
    have hledger := chiN_rhoN_ledger_write
      ((s.set chiSlot fresh).set rhoSlot now) holder
      (s.get (pieSlot holder) + units) (units + s.get totalUnitsSlot)
    refine ⟨accountingInv_stepClosed.join h.1 hclock hguards hnof hfresh hcap
      hasset hunits hrowCap htotalCap, ?_, ?_⟩
    · rw [hledger.1]
      exact hmono.1
    · rw [hledger.2]
      exact hmono.2
  exit := by
    intro s holder fresh units now elapsed h hclock hguards hnof hfresh hcap
      hrowCover htotalCover
    have hmono := monoInv_accrual h.2.1 h.2.2 hclock hguards hnof hfresh
    have hledger := chiN_rhoN_ledger_write
      ((s.set chiSlot fresh).set rhoSlot now) holder
      (s.get (pieSlot holder) - units) (s.get totalUnitsSlot - units)
    refine ⟨accountingInv_stepClosed.exit h.1 hclock hguards hnof hfresh hcap
      hrowCover htotalCover, ?_, ?_⟩
    · rw [hledger.1]
      exact hmono.1
    · rw [hledger.2]
      exact hmono.2

/-- Every successful DRIP source run preserves `MonoInv chi0 rho0`: the same
dispatcher as `dripSpec_sound`, at the monotone instance. -/
theorem dripMonoSpec_sound (chi0 rho0 : Nat) (ca : Adr) :
    (dripMonoSpec chi0 rho0).Sound ca :=
  sound_of_stepClosed (monoInv_stepClosed chi0 rho0) ca

/-- The frame-level preservation form of `MonoInv`, consumed by the retained
execution ladder. -/
theorem dripMonoSpec_preserves (chi0 rho0 : Nat) (ca : Adr) :
    (dripMonoSpec chi0 rho0).Preserves ca :=
  (dripMonoSpec chi0 rho0).preserves_inv ca (dripMonoSpec_sound chi0 rho0 ca)

end Drip

end Blanc
