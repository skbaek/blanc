import Blanc.Lift.ExactWalk

/-!
# Exact walk steps under a state-gas fork

`SSTORE` and `SLOAD` on a fork whose rule record carries a `StateGasRules`, for gas-exact runs
(`Blanc/Lift/ExactWalk.lean`). The prices come from the record passed in, never from literals, so a
repricing moves numbers and not structure. `SSTORE` differs in shape from the legacy lane and has its
own carriers (`sstoreCostA`, `afterSstoreA`, the meter's `sstoreChargeA`, `sstoreCreditA`,
`sstoreMeterA`); `SLOAD`'s successor is `afterSloadA` from `Blanc/ForwardCall.lean`.
The observers below are what a frame's walk and its top-level envelope
(`Blanc/Lift/SystemCallAmsterdam.lean`) read. Nothing here mentions a contract or a fork name.
-/

namespace Blanc.Lift

open Jaune

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

/-- `chargeStateGas` within the reservoir. -/
theorem chargeStateGas_of_le {amount : Nat} {devm : Devm} (h : amount ≤ devm.stateGas.left) :
    chargeStateGas amount devm = .ok (devm.setMach { devm.mach with
      stateGas := { devm.stateGas with left := devm.stateGas.left - amount } }) := by
  have h' : amount ≤ devm.mach.stateGas.left := h
  have core : Mach.chargeStateGas amount devm.mach = .ok ((), { devm.mach with
      stateGas := { devm.mach.stateGas with left := devm.mach.stateGas.left - amount } }) := by
    unfold Mach.chargeStateGas
    rw [ite_eq_left h']
  simp only [chargeStateGas, liftMachExecution, liftMach, Footprint.liftOutcome, core,
    Footprint.toExecution]
  rfl

/-- `creditStateGasRefund` with no outstanding spill refills the reservoir. -/
theorem creditStateGasRefund_of_no_spill {amount : Nat} {devm : Devm}
    (h : devm.stateGas.spilled = 0) :
    devm.creditStateGasRefund amount = devm.setMach { devm.mach with
      stateGas := { devm.stateGas with left := devm.stateGas.left + amount } } := by
  have h' : devm.mach.stateGas.spilled = 0 := h
  simp only [Devm.creditStateGasRefund, Mach.creditStateGasRefund, h', h, Nat.min_zero,
    Nat.add_zero, Nat.sub_zero]
  rfl

/-- `chargeGas` at an exact remainder. -/
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
    rw [ite_eq_left hfloor]
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
    rw [ite_eq_left hfloor]
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

/-! ## Reading the charge -/

/-- A zero-to-nonzero first write draws `storageSet` from the reservoir. -/
theorem sstoreChargeA_set {state : StateGasRules} {sevm : Sevm} {b : Devm} {k v : B256}
    (ho : b.getOrigStorVal sevm sevm.currentTarget k = 0)
    (hc : b.getStorVal sevm.currentTarget k = 0) (hv : v ≠ 0) :
    sstoreChargeA state sevm b k v = state.storageSet ∧
      sstoreCreditA state sevm b k v = 0 := by
  unfold sstoreChargeA sstoreCreditA sstoreAmsterdamStateGas sstoreAmsterdamStateRefund
  rw [ho, hc]
  simp only [hv.symm, not_false_eq_true, and_self, and_false, ↓reduceIte, ne_eq, false_and]

/-- A nonzero rewrite charges no state gas. -/
theorem sstoreChargeA_rewrite {state : StateGasRules} {sevm : Sevm} {b : Devm} {k v : B256}
    (ho : b.getOrigStorVal sevm sevm.currentTarget k ≠ 0) :
    sstoreChargeA state sevm b k v = 0 ∧ sstoreCreditA state sevm b k v = 0 := by
  unfold sstoreChargeA sstoreCreditA sstoreAmsterdamStateGas sstoreAmsterdamStateRefund
  simp only [ho, and_false, ↓reduceIte, and_self]

theorem sstoreChargeA_le (state : StateGasRules) (sevm : Sevm) (b : Devm) (k v : B256) :
    sstoreChargeA state sevm b k v ≤ state.storageSet := by
  unfold sstoreChargeA sstoreAmsterdamStateGas
  split <;> omega

/-- The rule-relative bound on one `SSTORE`'s execution gas. -/
theorem sstoreCostA_le (state : StateGasRules) (sevm : Sevm) (b : Devm) (k v : B256) :
    sstoreCostA state sevm b k v ≤ gasColdSload + state.storageWrite := by
  unfold sstoreCostA sstoreAmsterdamGasCost
  have : gasWarmAccess ≤ gasColdSload := by decide
  split <;> split <;> omega

/-! ## Observers of the successor bases -/

/-- A store with `n + storageSet` of reservoir and no spill leaves no spill and `n` of reservoir. -/
theorem afterSstoreA_meter (state : StateGasRules) {sevm : Sevm} {b : Devm} {k v : B256} {n : Nat}
    (hs : b.stateGas.spilled = 0) (hl : n + state.storageSet ≤ b.stateGas.left) :
    (afterSstoreA state sevm b k v).stateGas.spilled = 0 ∧
      n ≤ (afterSstoreA state sevm b k v).stateGas.left := by
  have hc := sstoreChargeA_le state sevm b k v
  rw [afterSstoreA_stateGas]
  refine ⟨hs, ?_⟩
  show n ≤ b.stateGas.left + _ - sstoreChargeA state sevm b k v
  omega

theorem afterSstoreA_state (state : StateGasRules) (sevm : Sevm) (b : Devm) (k v : B256) :
    (afterSstoreA state sevm b k v).state = b.state.setStorVal sevm.currentTarget k v := by
  unfold afterSstoreA
  split <;> rfl

theorem balReadAccount_error (r : ForkRules) (a : Adr) (d : Devm) :
    (d.balReadAccount r a).error = d.error := by
  unfold Devm.balReadAccount
  split <;> rfl

theorem balReadStorage_error (r : ForkRules) (a : Adr) (k : B256) (d : Devm) :
    (d.balReadStorage r a k).error = d.error := by
  unfold Devm.balReadStorage
  split <;> rfl

theorem afterSstoreA_error (state : StateGasRules) (sevm : Sevm) (b : Devm) (k v : B256) :
    (afterSstoreA state sevm b k v).error = b.error := by
  unfold afterSstoreA
  dsimp only
  show (Devm.balReadAccount _ _ _).error = _
  rw [balReadAccount_error]
  show (Devm.balReadStorage _ _ _ _).error = _
  rw [balReadStorage_error]
  split <;> rfl

theorem afterSstoreA_refundCounter (state : StateGasRules) (sevm : Sevm) (b : Devm) (k v : B256) :
    (afterSstoreA state sevm b k v).refundCounter =
      sstoreAmsterdamRefundCounter sevm.benvStat.rules.gas state v
        (b.getOrigStorVal sevm sevm.currentTarget k) (b.getStorVal sevm.currentTarget k)
        b.refundCounter := by
  unfold afterSstoreA
  dsimp only
  show (Devm.balReadAccount _ _ _).refundCounter = _
  rw [Devm.balReadAccount_refundCounter]
  rfl

/-- The Amsterdam refund never lowers the counter on a slot not changed earlier in the transaction:
the slot's current value is still its original one, or its original one is zero. -/
theorem sstoreAmsterdamRefund_ge (gas : GasSchedule) (state : StateGasRules) {v o c : B256}
    {rc : Int} (h : o = c ∨ o = 0) :
    rc ≤ sstoreAmsterdamRefundCounter gas state v o c rc := by
  unfold sstoreAmsterdamRefundCounter
  by_cases hcv : c ≠ v
  · rw [ite_eq_left hcv]
    simp only
    have h1 : ¬ (o ≠ 0 ∧ c = 0) := by
      rintro ⟨ho, hc⟩
      rcases h with h | h
      · exact ho (h.trans hc)
      · exact ho h
    rw [ite_eq_right h1]
    split <;> split <;> omega
  · rw [ite_eq_right hcv]

theorem afterSloadA_state (sevm : Sevm) (b : Devm) (k : B256) :
    (afterSloadA sevm b k).state = b.state := by
  unfold afterSloadA afterSload
  split <;> rfl

theorem afterSloadA_error (sevm : Sevm) (b : Devm) (k : B256) :
    (afterSloadA sevm b k).error = b.error := by
  unfold afterSloadA
  rw [balReadStorage_error]
  unfold afterSload
  split <;> rfl

theorem afterSloadA_refundCounter (sevm : Sevm) (b : Devm) (k : B256) :
    (afterSloadA sevm b k).refundCounter = b.refundCounter := by
  unfold afterSloadA
  rw [Devm.balReadStorage_refundCounter]
  unfold afterSload
  split <;> rfl

/-! ## `SLOAD` -/

/-- `SLOAD` in an exact run on any fork with EIP-2929 access: no `stateGas` or `CoveredFork` premise.
`rx_sload_sel` is this one where the read record vanishes. -/
theorem rx_sloadA {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {oc : Outcome}
    {S : List B256} {M : Mem} {G : Nat} {k' : B256}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm
      (St (afterSloadA sevm b k') (b.getStorVal sevm.currentTarget k' :: S) M G) f oc) :
    SFunc.RunExact fs sevm (St b (k' :: S) M (G + sloadCost sevm b k')) (.next (.reg .sload) f) oc := by
  refine .next ?_ k
  have h := Ninst.runCompiled_sloadA (sevm := sevm) (base := b) (key := k') (stack := S)
    (memory := M) (G := G) hacc rfl hroom
  simpa only [St, afterSloadA_stateGas] using h

end Blanc.Lift
