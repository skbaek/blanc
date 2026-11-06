import Blanc.Lift.SystemExecution.BeaconRoots.SystemWalk

/-!
# W1 probe: `SSTORE` under Amsterdam

Probe only (`blanc-eip8282-builder-requests-v1`, W1); does not land.
-/

namespace Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbe

open Jaune
open Blanc.Lift

/-- Whether this key is cold for the frame. -/
abbrev isColdA (sevm : Sevm) (devm : Devm) (key : B256) : Prop :=
  (⟨sevm.currentTarget, key⟩ : Adr × B256) ∉ devm.accessedStorageKeys

/-- The execution gas of one `SSTORE` under Amsterdam, against the rule record. -/
def sstoreCostA (state : StateGasRules) (sevm : Sevm) (devm : Devm) (key value : B256) : Nat :=
  sstoreAmsterdamGasCost state value (devm.getOrigStorVal sevm sevm.currentTarget key)
    (devm.getStorVal sevm.currentTarget key) (decide (isColdA sevm devm key))

/-- The state gas charged. -/
def sstoreChargeA (state : StateGasRules) (sevm : Sevm) (devm : Devm) (key value : B256) : Nat :=
  sstoreAmsterdamStateGas state value (devm.getOrigStorVal sevm sevm.currentTarget key)
    (devm.getStorVal sevm.currentTarget key)

/-- The state gas credited back. -/
def sstoreCreditA (state : StateGasRules) (sevm : Sevm) (devm : Devm) (key value : B256) : Nat :=
  sstoreAmsterdamStateRefund state value (devm.getOrigStorVal sevm sevm.currentTarget key)
    (devm.getStorVal sevm.currentTarget key)

/-- The state-gas meter after one `SSTORE` that does not spill, from a meter with no spill. -/
def sstoreMeterA (state : StateGasRules) (sevm : Sevm) (devm : Devm) (key value : B256) :
    StateGasMeter :=
  { devm.stateGas with
    left := devm.stateGas.left + sstoreCreditA state sevm devm key value -
      sstoreChargeA state sevm devm key value }

/-- The successor base of one `SSTORE` under Amsterdam: the warmed key, the two read records
(no-ops unless `rules.bal` is present), the Amsterdam refund and the state-gas meter. -/
def afterSstoreA (state : StateGasRules) (sevm : Sevm) (devm : Devm) (key value : B256) : Devm :=
  let ct := sevm.currentTarget
  let rules := sevm.benvStat.rules
  let accessed :=
    if isColdA sevm devm key then addAccessedStorageKey devm ct key else devm
  let read := accessed.balReadStorage rules ct key
  let refunded := read.withRefundCounter
    (sstoreAmsterdamRefundCounter rules.gas state value
      (devm.getOrigStorVal sevm ct key) (devm.getStorVal ct key) devm.refundCounter)
  let metered := refunded.setMach
    { refunded.mach with stateGas := sstoreMeterA state sevm devm key value }
  (metered.balReadAccount rules ct).setStorVal ct key value

theorem afterSstoreA_stateGas (state : StateGasRules) (sevm : Sevm) (devm : Devm)
    (key value : B256) :
    (afterSstoreA state sevm devm key value).stateGas =
      sstoreMeterA state sevm devm key value := by
  unfold afterSstoreA
  split <;> rfl

/-- `chargeStateGas` within the reservoir. Hoist debt: generic. -/
theorem chargeStateGas_of_le {amount : Nat} {devm : Devm} (h : amount ≤ devm.stateGas.left) :
    chargeStateGas amount devm = .ok (devm.setMach { devm.mach with
      stateGas := { devm.stateGas with left := devm.stateGas.left - amount } }) := by
  have h' : amount ≤ devm.mach.stateGas.left := h
  have core : Mach.chargeStateGas amount devm.mach = .ok ((), { devm.mach with
      stateGas := { devm.mach.stateGas with left := devm.mach.stateGas.left - amount } }) := by
    unfold Mach.chargeStateGas
    rw [if_pos h']
  simp only [chargeStateGas, liftMachExecution, liftMach, Footprint.liftOutcome, core,
    Footprint.toExecution]
  rfl

/-- `creditStateGasRefund` with no outstanding spill refills the reservoir. Hoist debt: generic. -/
theorem creditStateGasRefund_of_no_spill {amount : Nat} {devm : Devm}
    (h : devm.stateGas.spilled = 0) :
    devm.creditStateGasRefund amount = devm.setMach { devm.mach with
      stateGas := { devm.stateGas with left := devm.stateGas.left + amount } } := by
  have h' : devm.mach.stateGas.spilled = 0 := h
  simp only [Devm.creditStateGasRefund, Mach.creditStateGasRefund, h', h, Nat.min_zero,
    Nat.add_zero, Nat.sub_zero]
  rfl

/-- `chargeGas` at an exact remainder. Hoist debt: generic. -/
theorem chargeGas_ok_of_eq {cost G : Nat} {d : Devm} (h : d.gasLeft = G + cost) :
    chargeGas cost d = .ok (d.setMach ⟨d.stack, d.memory, G, d.stateGas⟩) := by
  rw [chargeGas_eq_ok (by omega)]
  have : d.gasLeft - cost = G := by omega
  rw [this]

theorem sstoreAmsterdamGasCost_access_le (state : StateGasRules) (v o c : B256) (cold : Bool) :
    (if cold then gasColdSload else gasWarmAccess) ≤ sstoreAmsterdamGasCost state v o c cold := by
  unfold sstoreAmsterdamGasCost
  omega

/-- The common tail of one Amsterdam `SSTORE`, after the access choice. -/
private theorem sstoreA_tail {rules : ForkRules} {ct : Adr} {key value : B256} {d : Devm}
    {r : Int} {credit charge cost G : Nat}
    (hspill : d.stateGas.spilled = 0) (hres : charge ≤ d.stateGas.left + credit)
    (hgas : d.gasLeft = G + cost) :
    Except.bind (chargeGas cost (Devm.creditStateGasRefund credit
        ((Devm.balReadStorage rules ct key d).withRefundCounter r))) (fun v =>
      Except.bind (chargeStateGas charge v) (fun v =>
        Except.ok ((Devm.balReadAccount rules ct v).setStorVal ct key value))) =
      Except.ok ((Devm.balReadAccount rules ct
        (((Devm.balReadStorage rules ct key d).withRefundCounter r).setMach
          ⟨d.stack, d.memory, G,
            { d.stateGas with left := d.stateGas.left + credit - charge }⟩)).setStorVal
        ct key value) := by
  have hsp : ((Devm.balReadStorage rules ct key d).withRefundCounter r).stateGas.spilled = 0 := hspill
  rw [creditStateGasRefund_of_no_spill hsp, chargeGas_ok_of_eq (G := G) (cost := cost) ?hg]
  case hg => exact hgas
  simp only [Except.bind]
  rw [chargeStateGas_of_le (amount := charge) ?hl]
  case hl => exact hres
  rfl

/-- **One exact `SSTORE` under Amsterdam.** -/
theorem runCompiled_sstoreA {state : StateGasRules} {sevm : Sevm} {base : Devm} {key value : B256}
    {stack : List B256} {memory : Mem} {G : Nat}
    (hsg : sevm.benvStat.rules.stateGas = some state)
    (hstatic : sevm.isStatic = false)
    (hsentry : gCallStipend < G + sstoreCostA state sevm base key value)
    (hspill : base.stateGas.spilled = 0)
    (hres : sstoreChargeA state sevm base key value ≤
      base.stateGas.left + sstoreCreditA state sevm base key value) :
    Ninst.RunCompiled sevm
      (St base (key :: value :: stack) memory (G + sstoreCostA state sevm base key value))
      (.reg .sstore)
      (St (afterSstoreA state sevm base key value) stack memory G) := by
  refine Ninst.runCompiled_reg (by rintro ⟨⟩) ?_
  generalize hX : G + sstoreCostA state sevm base key value = X at hsentry ⊢
  have hpop1 : (St base (key :: value :: stack) memory X).pop =
      .ok (key, St base (value :: stack) memory X) := rfl
  have hpop2 : (St base (value :: stack) memory X).pop =
      .ok (value, St base stack memory X) := rfl
  simp only [Rinst.runCore, hsg, assertDynamic, Except.assert, hstatic, Bool.not_false,
    ↓reduceIte, bind, Except.bind]
  rw [hpop1]
  simp only [bind, Except.bind]
  rw [hpop2]
  simp only [St.accessedStorageKeys]
  have hle := sstoreAmsterdamGasCost_access_le state value
    (base.getOrigStorVal sevm sevm.currentTarget key) (base.getStorVal sevm.currentTarget key)
    (decide (isColdA sevm base key))
  have hXeq : X = G + sstoreCostA state sevm base key value := hX.symm
  unfold sstoreCostA at hXeq
  by_cases hw : (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ base.accessedStorageKeys
  · have hcold : decide (isColdA sevm base key) = false := by simp only [isColdA, hw,
      not_true_eq_false, decide_false]
    rw [hcold] at hle hXeq
    simp only [Bool.false_eq_true, ↓reduceIte] at hle
    simp only [hw, not_true_eq_false, ↓reduceIte]
    have hfloor : max gasWarmAccess (gCallStipend + 1) ≤ (St base stack memory X).gasLeft := by
      show max gasWarmAccess (gCallStipend + 1) ≤ X
      omega
    rw [if_pos hfloor]
    simp only [Devm.balReadStorage_refundCounter, decide_false]
    have tail := sstoreA_tail (rules := sevm.benvStat.rules) (ct := sevm.currentTarget) (key := key)
      (value := value) (d := St base stack memory X)
      (r := sstoreAmsterdamRefundCounter sevm.benvStat.rules.gas state value
        (base.getOrigStorVal sevm sevm.currentTarget key)
        (base.getStorVal sevm.currentTarget key) base.refundCounter)
      (credit := sstoreCreditA state sevm base key value)
      (charge := sstoreChargeA state sevm base key value)
      (cost := sstoreAmsterdamGasCost state value (base.getOrigStorVal sevm sevm.currentTarget key)
        (base.getStorVal sevm.currentTarget key) false) (G := G) hspill hres hXeq
    simp only [Except.bind] at tail
    refine tail.trans ?_
    simp only [St, afterSstoreA, isColdA, hw, not_true_eq_false, ↓reduceIte]
    rfl
  · have hcold : decide (isColdA sevm base key) = true := by
      simp only [isColdA, hw, not_false_eq_true, decide_true]
    rw [hcold] at hle hXeq
    simp only [↓reduceIte] at hle
    simp only [hw, not_false_eq_true, ↓reduceIte]
    have hfloor : max gasColdSload (gCallStipend + 1) ≤ (St base stack memory X).gasLeft := by
      show max gasColdSload (gCallStipend + 1) ≤ X
      omega
    rw [if_pos hfloor]
    simp only [Devm.balReadStorage_refundCounter, decide_true]
    have tail := sstoreA_tail (rules := sevm.benvStat.rules) (ct := sevm.currentTarget) (key := key)
      (value := value) (d := addAccessedStorageKey (St base stack memory X) sevm.currentTarget key)
      (r := sstoreAmsterdamRefundCounter sevm.benvStat.rules.gas state value
        (base.getOrigStorVal sevm sevm.currentTarget key)
        (base.getStorVal sevm.currentTarget key) base.refundCounter)
      (credit := sstoreCreditA state sevm base key value)
      (charge := sstoreChargeA state sevm base key value)
      (cost := sstoreAmsterdamGasCost state value (base.getOrigStorVal sevm sevm.currentTarget key)
        (base.getStorVal sevm.currentTarget key) true) (G := G) hspill hres hXeq
    simp only [Except.bind] at tail
    refine tail.trans ?_
    simp only [St, afterSstoreA, isColdA, hw, not_false_eq_true, ↓reduceIte]
    rfl

/-- `SSTORE` in an exact run under Amsterdam: the analogue of `rx_sstore`. -/
theorem rx_sstoreA {state : StateGasRules} {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc}
    {o : Outcome} {S : List B256} {M : Mem} {G : Nat} {k' v : B256}
    (hsg : sevm.benvStat.rules.stateGas = some state)
    (hsentry : gCallStipend < G + sstoreCostA state sevm b k' v)
    (hstatic : sevm.isStatic = false)
    (hspill : b.stateGas.spilled = 0)
    (hres : sstoreChargeA state sevm b k' v ≤ b.stateGas.left + sstoreCreditA state sevm b k' v)
    (k : SFunc.RunExact fs sevm (St (afterSstoreA state sevm b k' v) S M G) f o) :
    SFunc.RunExact fs sevm (St b (k' :: v :: S) M (G + sstoreCostA state sevm b k' v))
      (.next (.reg .sstore) f) o :=
  .next (runCompiled_sstoreA hsg hstatic hsentry hspill hres) k

/-! ## The two cases the brief names -/

/-- A zero-to-nonzero first write draws `storageSet` from the reservoir. -/
theorem sstoreChargeA_set {state : StateGasRules} {sevm : Sevm} {b : Devm} {k v : B256}
    (ho : b.getOrigStorVal sevm sevm.currentTarget k = 0)
    (hc : b.getStorVal sevm.currentTarget k = 0) (hv : v ≠ 0) :
    sstoreChargeA state sevm b k v = state.storageSet ∧
      sstoreCreditA state sevm b k v = 0 := by
  unfold sstoreChargeA sstoreCreditA sstoreAmsterdamStateGas sstoreAmsterdamStateRefund
  rw [ho, hc]
  simp only [hv.symm, not_false_eq_true, and_self, and_false, ↓reduceIte, ne_eq, true_and,
    not_true_eq_false, false_and]

/-- A nonzero rewrite charges no state gas. -/
theorem sstoreChargeA_rewrite {state : StateGasRules} {sevm : Sevm} {b : Devm} {k v : B256}
    (ho : b.getOrigStorVal sevm sevm.currentTarget k ≠ 0) :
    sstoreChargeA state sevm b k v = 0 ∧ sstoreCreditA state sevm b k v = 0 := by
  unfold sstoreChargeA sstoreCreditA sstoreAmsterdamStateGas sstoreAmsterdamStateRefund
  simp only [ho, and_false, ↓reduceIte, false_and, and_self]

end Blanc.Lift.SystemExecution.BeaconRoots.AmsterdamProbe

