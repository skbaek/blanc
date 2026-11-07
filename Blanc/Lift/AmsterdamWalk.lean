import Blanc.Lift.ExactWalk
import Blanc.StorageAccessGas
import Blanc.SystemCallForward
import Blanc.Lift.InvWalkWorld

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

/-- The part of the credit that repays an earlier spill, and so returns to `gasLeft`. -/
def sstoreRepayA (state : StateGasRules) (sevm : Sevm) (devm : Devm) (key value : B256) : Nat :=
  min (sstoreCreditA state sevm devm key value) devm.stateGas.spilled

/-- The state gas the reservoir cannot cover, drawn from `gasLeft`. An ordinary transaction's frame has an
empty reservoir, so there this is the whole charge. -/
def sstoreSpillA (state : StateGasRules) (sevm : Sevm) (devm : Devm) (key value : B256) : Nat :=
  sstoreChargeA state sevm devm key value -
    (devm.stateGas.left +
      (sstoreCreditA state sevm devm key value - sstoreRepayA state sevm devm key value))

/-- What one `SSTORE` takes from `gasLeft`: its execution gas and its spill. A repaid spill comes back
after: see `rx_sstoreS`. -/
def sstoreTotalA (state : StateGasRules) (sevm : Sevm) (devm : Devm) (key value : B256) : Nat :=
  sstoreCostA state sevm devm key value + sstoreSpillA state sevm devm key value

/-- The state-gas meter after one `SSTORE`, as Jaune's `creditStateGasRefund` and `chargeStateGas` leave it:
the credit repays the spill first and refills the reservoir with the rest, then the charge draws on the
reservoir and spills what it cannot cover. -/
def sstoreMeterA (state : StateGasRules) (sevm : Sevm) (devm : Devm) (key value : B256) :
    StateGasMeter :=
  { devm.stateGas with
    left := devm.stateGas.left +
        (sstoreCreditA state sevm devm key value - sstoreRepayA state sevm devm key value) -
      sstoreChargeA state sevm devm key value
    spilled := devm.stateGas.spilled - sstoreRepayA state sevm devm key value +
      sstoreSpillA state sevm devm key value }

theorem sstoreRepayA_of_no_spill {state : StateGasRules} {sevm : Sevm} {devm : Devm} {key value : B256}
    (h : devm.stateGas.spilled = 0) : sstoreRepayA state sevm devm key value = 0 := by
  simp only [sstoreRepayA, h, Nat.min_zero]

theorem sstoreSpillA_of_room {state : StateGasRules} {sevm : Sevm} {devm : Devm} {key value : B256}
    (hspill : devm.stateGas.spilled = 0)
    (hres : sstoreChargeA state sevm devm key value ≤
      devm.stateGas.left + sstoreCreditA state sevm devm key value) :
    sstoreSpillA state sevm devm key value = 0 := by
  rw [sstoreSpillA, sstoreRepayA_of_no_spill hspill]
  omega

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

/-- `chargeStateGas` under any meter: the reservoir first, then `gasLeft`. -/
theorem chargeStateGas_spill {amount : Nat} {devm : Devm}
    (h : amount - devm.stateGas.left ≤ devm.gasLeft) :
    chargeStateGas amount devm = .ok (devm.setMach { devm.mach with
      gasLeft := devm.gasLeft - (amount - devm.stateGas.left)
      stateGas := { devm.stateGas with
        left := devm.stateGas.left - amount
        spilled := devm.stateGas.spilled + (amount - devm.stateGas.left) } }) := by
  by_cases hle : amount ≤ devm.stateGas.left
  · rw [chargeStateGas_of_le hle, Nat.sub_eq_zero_of_le hle]
    rfl
  · have core : Mach.chargeStateGas amount devm.mach = .ok ((), { devm.mach with
        gasLeft := devm.gasLeft - (amount - devm.stateGas.left)
        stateGas := { devm.stateGas with
          left := devm.stateGas.left - amount
          spilled := devm.stateGas.spilled + (amount - devm.stateGas.left) } }) := by
      have h0 : devm.stateGas.left - amount = 0 := by omega
      have hle' : ¬ amount ≤ devm.mach.stateGas.left := hle
      have h' : amount - devm.mach.stateGas.left ≤ devm.mach.gasLeft := h
      unfold Mach.chargeStateGas
      rw [ite_eq_right hle', ite_eq_left h', h0]
      rfl
    simp only [chargeStateGas, liftMachExecution, liftMach, Footprint.liftOutcome, core,
      Footprint.toExecution]

/-- What a successful `chargeStateGas` leaves, under any meter: the inverse of `chargeStateGas_spill`. -/
theorem chargeStateGas_ok_inv {amount : Nat} {devm post : Devm}
    (h : chargeStateGas amount devm = .ok post) :
    post = devm.setMach { devm.mach with
      gasLeft := devm.gasLeft - (amount - devm.stateGas.left)
      stateGas := { devm.stateGas with
        left := devm.stateGas.left - amount
        spilled := devm.stateGas.spilled + (amount - devm.stateGas.left) } } := by
  by_cases hle : amount - devm.stateGas.left ≤ devm.gasLeft
  · rw [chargeStateGas_spill hle] at h
    exact (Except.ok.inj h).symm
  · have hcore : Mach.chargeStateGas amount devm.mach = .error (.halt (.outOfGas .none), devm.mach) := by
      have h1 : ¬ amount ≤ devm.mach.stateGas.left := fun hh => hle (by
        have : amount - devm.stateGas.left = 0 := Nat.sub_eq_zero_of_le hh
        omega)
      have h2 : ¬ amount - devm.mach.stateGas.left ≤ devm.mach.gasLeft := hle
      unfold Mach.chargeStateGas
      rw [ite_eq_right h1, ite_eq_right h2]
    simp only [chargeStateGas, liftMachExecution, liftMach, Footprint.liftOutcome, hcore,
      Footprint.toExecution] at h
    cases h

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

/-- The common tail of one Amsterdam `SSTORE`, after the access choice, under any meter. -/
private theorem sstoreA_tail {rules : ForkRules} {ct : Adr} {key value : B256} {d : Devm}
    {r : Int} {credit charge cost G : Nat}
    (hgas : d.gasLeft = G + cost +
      (charge - (d.stateGas.left + (credit - min credit d.stateGas.spilled)))) :
    Except.bind (chargeGas cost (Devm.creditStateGasRefund credit
        ((Devm.balReadStorage rules ct key d).withRefundCounter r))) (fun v =>
      Except.bind (chargeStateGas charge v) (fun v =>
        Except.ok ((Devm.balReadAccount rules ct v).setStorVal ct key value))) =
      Except.ok ((Devm.balReadAccount rules ct
        (((Devm.balReadStorage rules ct key d).withRefundCounter r).setMach
          ⟨d.stack, d.memory, G + min credit d.stateGas.spilled,
            { d.stateGas with
              left := d.stateGas.left + (credit - min credit d.stateGas.spilled) - charge
              spilled := d.stateGas.spilled - min credit d.stateGas.spilled +
                (charge - (d.stateGas.left + (credit - min credit d.stateGas.spilled))) }⟩)).setStorVal
        ct key value) := by
  generalize hrep : min credit d.stateGas.spilled = rep at hgas ⊢
  generalize hsp : charge - (d.stateGas.left + (credit - rep)) = sp at hgas ⊢
  have hcharge : chargeGas cost (Devm.creditStateGasRefund credit
      ((Devm.balReadStorage rules ct key d).withRefundCounter r)) = .ok
      ((Devm.creditStateGasRefund credit
        ((Devm.balReadStorage rules ct key d).withRefundCounter r)).setMach
        ⟨d.stack, d.memory, G + sp + rep, (Devm.creditStateGasRefund credit
          ((Devm.balReadStorage rules ct key d).withRefundCounter r)).stateGas⟩) := by
    refine chargeGas_ok_of_eq ?_
    show d.gasLeft + min credit d.stateGas.spilled = _
    omega
  rw [hcharge]
  simp only [Except.bind]
  have hmeter : (Devm.creditStateGasRefund credit
      ((Devm.balReadStorage rules ct key d).withRefundCounter r)).stateGas =
      { d.stateGas with left := d.stateGas.left + (credit - rep), spilled := d.stateGas.spilled - rep } := by
    subst hrep
    rfl
  rw [chargeStateGas_spill (amount := charge) ?hl]
  case hl =>
    show charge - (Devm.creditStateGasRefund credit _).stateGas.left ≤ G + sp + rep
    rw [hmeter]
    show charge - (d.stateGas.left + (credit - rep)) ≤ _
    omega
  simp only [Devm.setMach, Devm.stateGas, Devm.gasLeft, Devm.mach] at hmeter hsp ⊢
  have hl := congrArg StateGasMeter.left hmeter
  have hs := congrArg StateGasMeter.spilled hmeter
  simp only at hl hs
  have e : G + sp + rep - sp = G + rep := by omega
  simp only [hl, hs, hsp, e]
  rfl

/-- **One exact `SSTORE` under Amsterdam, under any meter**: it takes its execution gas and its spill from
`gasLeft`, and repays the spill it can. -/
theorem runCompiled_sstoreS {state : StateGasRules} {sevm : Sevm} {base : Devm} {key value : B256}
    {stack : List B256} {memory : Mem} {G : Nat}
    (hsg : sevm.benvStat.rules.stateGas = some state)
    (hstatic : sevm.isStatic = false)
    (hsentry : gCallStipend < G + sstoreTotalA state sevm base key value) :
    Ninst.RunCompiled sevm
      (St base (key :: value :: stack) memory (G + sstoreTotalA state sevm base key value))
      (.reg .sstore)
      (St (afterSstoreA state sevm base key value) stack memory
        (G + sstoreRepayA state sevm base key value)) := by
  refine Ninst.runCompiled_reg (by rintro ⟨⟩) ?_
  generalize hX : G + sstoreTotalA state sevm base key value = X at hsentry ⊢
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
  have hXeq : X = G + sstoreCostA state sevm base key value +
      sstoreSpillA state sevm base key value := by
    rw [← hX, sstoreTotalA, Nat.add_assoc]
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
        (base.getStorVal sevm.currentTarget key) false) (G := G) hXeq
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
        (base.getStorVal sevm.currentTarget key) true) (G := G) hXeq
    simp only [Except.bind] at tail
    refine tail.trans ?_
    simp only [St, afterSstoreA, isColdA, hw, not_false_eq_true, ↓reduceIte]
    rfl

/-- **One exact `SSTORE` under Amsterdam, from a frame that does not spill.** -/
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
  have ht : sstoreTotalA state sevm base key value = sstoreCostA state sevm base key value := by
    rw [sstoreTotalA, sstoreSpillA_of_room hspill hres, Nat.add_zero]
  have h := runCompiled_sstoreS (stack := stack) (memory := memory) (G := G) hsg hstatic
    (ht ▸ hsentry : gCallStipend < G + sstoreTotalA state sevm base key value)
  rwa [ht, sstoreRepayA_of_no_spill hspill, Nat.add_zero] at h

/-- `SSTORE` in an exact run under Amsterdam, under any meter: the charge is the execution gas and the spill,
and a repaid spill returns to `gasLeft`. -/
theorem rx_sstoreS {state : StateGasRules} {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc}
    {o : Outcome} {S : List B256} {M : Mem} {G : Nat} {k' v : B256}
    (hsg : sevm.benvStat.rules.stateGas = some state) (hstatic : sevm.isStatic = false)
    (hsentry : gCallStipend < G + sstoreTotalA state sevm b k' v)
    (k : SFunc.RunExact fs sevm
      (St (afterSstoreA state sevm b k' v) S M (G + sstoreRepayA state sevm b k' v)) f o) :
    SFunc.RunExact fs sevm (St b (k' :: v :: S) M (G + sstoreTotalA state sevm b k' v))
      (.next (.reg .sstore) f) o :=
  .next (runCompiled_sstoreS hsg hstatic hsentry) k

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
  have hrep := sstoreRepayA_of_no_spill (state := state) (sevm := sevm) (key := k) (value := v) hs
  rw [afterSstoreA_stateGas]
  refine ⟨?_, ?_⟩
  · show b.stateGas.spilled - sstoreRepayA state sevm b k v + sstoreSpillA state sevm b k v = 0
    rw [sstoreSpillA_of_room hs (by omega), hs, hrep]
  · show n ≤ b.stateGas.left + (_ - sstoreRepayA state sevm b k v) - sstoreChargeA state sevm b k v
    rw [hrep, Nat.sub_zero]
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

/-! ## The steps inverted, under any meter -/

/-- `SLOAD`, inverted, on any fork with EIP-2929 access. -/
theorem ri_sloadA {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem} {G : Nat} {k : B256}
    (hacc : sevm.benvStat.rules.access = .eip2929)
    (h : Ninst.Run sevm (St b (k :: S) M G) (.reg .sload) d) :
    ∃ G', d = St (afterSloadA sevm b k) (b.getStorVal sevm.currentTarget k :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore, hacc] at run
  rw [show (St b (k :: S) M G).pop = .ok (k, St b S M G) from rfl] at run
  simp only [Except.bind_ok] at run
  by_cases hw : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ b.accessedStorageKeys
  · simp only [St.accessedStorageKeys, hw, ite_true] at run
    rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
    have e2 := Devm.eq_of_push_ok h2
    subst e2
    have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
    rw [e1]
    refine ⟨s1.gasLeft, ?_⟩
    simp only [afterSloadA, afterSload, hw, ite_true]
    rfl
  · simp only [St.accessedStorageKeys, hw, ite_false] at run
    rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
    have e2 := Devm.eq_of_push_ok h2
    subst e2
    have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
    rw [e1]
    refine ⟨s1.gasLeft, ?_⟩
    simp only [afterSloadA, afterSload, hw, ite_false]
    rfl

/-- `SSTORE`, inverted, under any meter: the successor base is `afterSstoreA`, whatever the reservoir
held. Only the gas is left to the run. -/
theorem ri_sstoreA {state : StateGasRules} {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem}
    {G : Nat} {k v : B256} (hsg : sevm.benvStat.rules.stateGas = some state)
    (h : Ninst.Run sevm (St b (k :: v :: S) M G) (.reg .sstore) d) :
    ∃ G', d = St (afterSstoreA state sevm b k v) S M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore, hsg] at run
  rcases Except.bind_eq_ok run with ⟨_, -, run⟩
  rw [show (St b (k :: v :: S) M G).pop = .ok (k, St b (v :: S) M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (v :: S) M G).pop = .ok (v, St b S M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rcases Except.bind_eq_ok run with ⟨_, -, run⟩
  rcases Except.bind_eq_ok run with ⟨s5, h5, run⟩
  rcases Except.bind_eq_ok run with ⟨s6, h6, last⟩
  cases last
  have e5 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h5)
  have e6 := chargeStateGas_ok_inv h6
  refine ⟨s6.gasLeft, ?_⟩
  rw [e6, e5]
  by_cases hw : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ b.accessedStorageKeys
  · simp only [St.accessedStorageKeys, afterSstoreA, isColdA, hw, not_true_eq_false, ite_false,
      Devm.balReadStorage_refundCounter]
    rfl
  · simp only [St.accessedStorageKeys, afterSstoreA, isColdA, hw, not_false_eq_true, ite_true,
      Devm.balReadStorage_refundCounter]
    rfl

/-- A successful `SSTORE` runs in a non-static frame, under any meter. -/
theorem ri_sstore_nonstaticA {state : StateGasRules} {sevm : Sevm} {b d : Devm} {S : List B256}
    {M : Mem} {G : Nat} {k v : B256} (hsg : sevm.benvStat.rules.stateGas = some state)
    (h : Ninst.Run sevm (St b (k :: v :: S) M G) (.reg .sstore) d) :
    sevm.isStatic = false := by
  cases hs : sevm.isStatic with
  | false => rfl
  | true =>
    exfalso
    rcases of_run_reg h with ⟨pc, run⟩
    simp only [Rinst.run, Rinst.runCore, hsg, bind, Except.bind, assertDynamic, Except.assert, hs,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at run

/-! ## Reads leave the state alone

These serve any frame that reads and stores under Amsterdam. `Ready` is what it carries to its remaining
stores; `Ready.sstore` needs each key stored at most once. -/

theorem afterSloadA_getStorVal (sevm : Sevm) (d : Devm) (k : B256) (a : Adr) (k' : B256) :
    (afterSloadA sevm d k).getStorVal a k' = d.getStorVal a k' := by
  unfold Devm.getStorVal Devm.getAcct
  rw [afterSloadA_state]

/-- `SLOAD` with the value it reads named. -/
theorem rx_sloadV {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {oc : Outcome}
    {S : List B256} {M : Mem} {G : Nat} {k' v : B256}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hroom : S.length < 1024)
    (hv : b.getStorVal sevm.currentTarget k' = v)
    (k : SFunc.RunExact fs sevm (St (afterSloadA sevm b k') (v :: S) M G) f oc) :
    SFunc.RunExact fs sevm (St b (k' :: S) M (G + sloadCost sevm b k')) (.next (.reg .sload) f) oc :=
  rx_sloadA hacc hroom (hv ▸ k)

/-- The base after a list of reads, in order. -/
def readsBase (sevm : Sevm) (b : Devm) (keys : List B256) : Devm :=
  keys.foldl (afterSloadA sevm) b

/-- The selected charge of a list of reads, each against its actual incoming base. -/
def readsGas (sevm : Sevm) : Devm → List B256 → Nat
  | _, [] => 0
  | b, k :: ks => sloadCost sevm b k + readsGas sevm (afterSloadA sevm b k) ks

theorem readsGas_le (sevm : Sevm) (b : Devm) (keys : List B256) :
    readsGas sevm b keys ≤ keys.length * gasColdSload := by
  induction keys generalizing b with
  | nil => exact Nat.zero_le _
  | cons k ks ih =>
    have h1 := sloadCost_le sevm b k
    have h2 := ih (afterSloadA sevm b k)
    simp only [readsGas, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-! ## What a frame must keep to reach its stores -/

/-- amsterdamStateGasRules slot not yet changed in this transaction: its current value is its original one, or its
original one is zero. -/
def SlotClean (sevm : Sevm) (d : Devm) (k : B256) : Prop :=
  d.getOrigStorVal sevm sevm.currentTarget k = d.getStorVal sevm.currentTarget k ∨
    d.getOrigStorVal sevm sevm.currentTarget k = 0

/-- What the frame carries to its remaining `SSTORE`s at `keys`. -/
structure Ready (sevm : Sevm) (d : Devm) (keys : List B256) : Prop where
  error : d.error = none
  refund : 0 ≤ d.refundCounter
  spill : d.stateGas.spilled = 0
  reservoir : keys.length * amsterdamStateGasRules.storageSet ≤ d.stateGas.left
  clean : ∀ k ∈ keys, SlotClean sevm d k

theorem afterSloadA_createdAccounts (sevm : Sevm) (d : Devm) (k : B256) :
    (afterSloadA sevm d k).createdAccounts = d.createdAccounts := by
  unfold afterSloadA Devm.balReadStorage afterSload
  split <;> split <;> rfl

theorem afterSloadA_getOrig (sevm : Sevm) (d : Devm) (k : B256) (a : Adr) (k' : B256) :
    (afterSloadA sevm d k).getOrigStorVal sevm a k' = d.getOrigStorVal sevm a k' := by
  unfold Devm.getOrigStorVal
  rw [afterSloadA_createdAccounts]

theorem Ready.sload {sevm : Sevm} {d : Devm} {keys : List B256} (r : Ready sevm d keys) (k : B256) :
    Ready sevm (afterSloadA sevm d k) keys where
  error := (afterSloadA_error sevm d k).trans r.error
  refund := by rw [afterSloadA_refundCounter]; exact r.refund
  spill := by rw [afterSloadA_stateGas]; exact r.spill
  reservoir := by rw [afterSloadA_stateGas]; exact r.reservoir
  clean := fun k' hk' => by
    unfold SlotClean
    rw [afterSloadA_getOrig, afterSloadA_getStorVal]
    exact r.clean k' hk'

theorem Ready.reads {sevm : Sevm} {d : Devm} {ks : List B256} (r : Ready sevm d ks)
    (keys : List B256) : Ready sevm (readsBase sevm d keys) ks := by
  induction keys generalizing d with
  | nil => exact r
  | cons k rest ih => exact ih (r.sload k)

theorem readsBase_state (sevm : Sevm) (d : Devm) (keys : List B256) :
    (readsBase sevm d keys).state = d.state := by
  induction keys generalizing d with
  | nil => rfl
  | cons k rest ih =>
    show (readsBase sevm (afterSloadA sevm d k) rest).state = _
    rw [ih, afterSloadA_state]

theorem afterSstoreA_createdAccounts (sevm : Sevm) (d : Devm) (k v : B256) :
    (afterSstoreA amsterdamStateGasRules sevm d k v).createdAccounts = d.createdAccounts := by
  unfold afterSstoreA Devm.balReadAccount Devm.balReadStorage
  dsimp only
  split <;> split <;> rfl

theorem afterSstoreA_getStorVal_ne (sevm : Sevm) (d : Devm) {k k' : B256} (v : B256)
    (h : k ≠ k') :
    (afterSstoreA amsterdamStateGasRules sevm d k v).getStorVal sevm.currentTarget k' =
      d.getStorVal sevm.currentTarget k' := by
  unfold Devm.getStorVal Devm.getAcct
  rw [afterSstoreA_state]
  show ((d.state.setStorVal sevm.currentTarget k v).getStor sevm.currentTarget).get k' =
    (d.state.getStor sevm.currentTarget).get k'
  rw [State.getStor_setStorVal_self, Stor.get_set_ne _ h]

theorem Ready.sstore {sevm : Sevm} {d : Devm} {k : B256} {ks : List B256} (r : Ready sevm d (k :: ks))
    (fresh : k ∉ ks) (v : B256) : Ready sevm (afterSstoreA amsterdamStateGasRules sevm d k v) ks where
  error := (afterSstoreA_error amsterdamStateGasRules sevm d k v).trans r.error
  refund := by
    rw [afterSstoreA_refundCounter]
    have hc : d.getOrigStorVal sevm sevm.currentTarget k = d.getStorVal sevm.currentTarget k ∨
        d.getOrigStorVal sevm sevm.currentTarget k = 0 := r.clean k List.mem_cons_self
    exact Int.le_trans r.refund (sstoreAmsterdamRefund_ge _ amsterdamStateGasRules hc)
  spill := (afterSstoreA_meter amsterdamStateGasRules (n := 0) r.spill (by
    have := r.reservoir
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at this
    omega)).1
  reservoir := (afterSstoreA_meter amsterdamStateGasRules (n := ks.length * amsterdamStateGasRules.storageSet) r.spill (by
    have := r.reservoir
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at this
    omega)).2
  clean := fun k' hk' => by
    have hne : k ≠ k' := fun e => fresh (e ▸ hk')
    unfold SlotClean Devm.getOrigStorVal
    rw [afterSstoreA_createdAccounts, afterSstoreA_getStorVal_ne sevm d v hne]
    exact r.clean k' (List.mem_cons_of_mem _ hk')

/-- `Ready` keeps for fewer stores. -/
theorem Ready.skip {sevm : Sevm} {d : Devm} {k k' : B256} {ks : List B256}
    (r : Ready sevm d (k :: k' :: ks)) : Ready sevm d (k :: ks) where
  error := r.error
  refund := r.refund
  spill := r.spill
  reservoir := by
    have := r.reservoir
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at this ⊢
    omega
  clean := fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact r.clean _ List.mem_cons_self
    · exact r.clean _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))

/-- `SSTORE` from a `Ready` frame. -/
theorem rx_sstoreR {fs : List SFunc} {sevm : Sevm} {b : Devm} {f : SFunc} {o : Outcome} {S : List B256}
    {M : Mem} {G : Nat} {k' v : B256} {ks : List B256}
    (hsg : sevm.benvStat.rules.stateGas = some amsterdamStateGasRules) (hstatic : sevm.isStatic = false)
    (r : Ready sevm b (k' :: ks)) (hsentry : gCallStipend < G + sstoreCostA amsterdamStateGasRules sevm b k' v)
    (k : SFunc.RunExact fs sevm (St (afterSstoreA amsterdamStateGasRules sevm b k' v) S M G) f o) :
    SFunc.RunExact fs sevm (St b (k' :: v :: S) M (G + sstoreCostA amsterdamStateGasRules sevm b k' v))
      (.next (.reg .sstore) f) o := by
  refine rx_sstoreA hsg hsentry hstatic r.spill ?_ k
  have hc := sstoreChargeA_le amsterdamStateGasRules sevm b k' v
  have hr := r.reservoir
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hr
  omega

/-! ## Logs and output -/

theorem afterSloadA_logs (sevm : Sevm) (d : Devm) (k : B256) : (afterSloadA sevm d k).logs = d.logs := by
  unfold afterSloadA Devm.balReadStorage afterSload
  split <;> split <;> rfl

theorem afterSloadA_output (sevm : Sevm) (d : Devm) (k : B256) :
    (afterSloadA sevm d k).output = d.output := by
  unfold afterSloadA Devm.balReadStorage afterSload
  split <;> split <;> rfl

theorem afterSstoreA_logs (sevm : Sevm) (d : Devm) (k v : B256) :
    (afterSstoreA amsterdamStateGasRules sevm d k v).logs = d.logs := by
  unfold afterSstoreA Devm.balReadAccount Devm.balReadStorage
  dsimp only
  split <;> split <;> rfl

theorem afterSstoreA_output (sevm : Sevm) (d : Devm) (k v : B256) :
    (afterSstoreA amsterdamStateGasRules sevm d k v).output = d.output := by
  unfold afterSstoreA Devm.balReadAccount Devm.balReadStorage
  dsimp only
  split <;> split <;> rfl

/-! ## What a frame keeps to settle cleanly, under any state-gas meter -/

/-- What a top-level frame keeps while its remaining `SSTORE`s at `keys` hit slots untouched in this transaction.
`grant` is the frame's state-gas grant, `used` what its stores have charged so far, and `n` a bound on the stores
it makes. Regular gas is not in here: `used` is state gas. -/
structure Fresh (sevm : Sevm) (d : Devm) (keys : List B256) (grant used n : Nat) : Prop where
  error : d.error = none
  refund : 0 ≤ d.refundCounter
  deleted : d.accountsToDelete.toList = []
  /-- The remaining slots hold their original value. -/
  clean : ∀ k ∈ keys, d.getOrigStorVal sevm sevm.currentTarget k = d.getStorVal sevm.currentTarget k
  /-- The reservoir only falls. -/
  drawn : d.stateGas.left ≤ grant
  /-- State gas charged is what left the reservoir plus what spilled. -/
  ledger : d.stateGas.left + used = grant + d.stateGas.spilled
  committed : d.stateGas.committedSpill = 0
  budget : used + keys.length * amsterdamStateGasRules.storageSet ≤ n * amsterdamStateGasRules.storageSet

namespace Fresh

variable {sevm : Sevm} {d : Devm} {keys : List B256} {grant used n : Nat}

theorem sload (r : Fresh sevm d keys grant used n) (k : B256) :
    Fresh sevm (afterSloadA sevm d k) keys grant used n where
  error := (afterSloadA_error sevm d k).trans r.error
  refund := by rw [afterSloadA_refundCounter]; exact r.refund
  deleted := by
    have h : (afterSloadA sevm d k).accountsToDelete = d.accountsToDelete := by
      unfold afterSloadA Devm.balReadStorage afterSload
      split <;> split <;> rfl
    rw [h]
    exact r.deleted
  clean := fun k' hk' => by
    rw [afterSloadA_getOrig, afterSloadA_getStorVal]
    exact r.clean k' hk'
  drawn := by rw [afterSloadA_stateGas]; exact r.drawn
  ledger := by rw [afterSloadA_stateGas]; exact r.ledger
  committed := by rw [afterSloadA_stateGas]; exact r.committed
  budget := r.budget

theorem addLog (r : Fresh sevm d keys grant used n) (l : Log) :
    Fresh sevm (d.addLog l) keys grant used n where
  error := r.error
  refund := r.refund
  deleted := r.deleted
  clean := r.clean
  drawn := r.drawn
  ledger := r.ledger
  committed := r.committed
  budget := r.budget

/-- A store at an untouched slot credits nothing. -/
theorem credit_zero {k : B256} (v : B256)
    (h : d.getOrigStorVal sevm sevm.currentTarget k = d.getStorVal sevm.currentTarget k) :
    sstoreCreditA amsterdamStateGasRules sevm d k v = 0 := by
  unfold sstoreCreditA sstoreAmsterdamStateRefund
  rw [h]
  exact ite_eq_right fun hc => hc.1 hc.2.1

/-- A store at an untouched slot repays no spill. -/
theorem repay_zero {k : B256} (v : B256)
    (h : d.getOrigStorVal sevm sevm.currentTarget k = d.getStorVal sevm.currentTarget k) :
    sstoreRepayA amsterdamStateGasRules sevm d k v = 0 := by
  rw [sstoreRepayA, credit_zero v h, Nat.zero_min]

theorem sstore {k : B256} {ks : List B256} (r : Fresh sevm d (k :: ks) grant used n)
    (fresh : k ∉ ks) (v : B256) :
    Fresh sevm (afterSstoreA amsterdamStateGasRules sevm d k v) ks grant
      (used + sstoreChargeA amsterdamStateGasRules sevm d k v) n := by
  have hclean := r.clean k List.mem_cons_self
  have hcredit := credit_zero v hclean
  have hrepay := repay_zero v hclean
  have hle := sstoreChargeA_le amsterdamStateGasRules sevm d k v
  have hdrawn := r.drawn
  have hledger := r.ledger
  have hbudget := r.budget
  have hleft : (afterSstoreA amsterdamStateGasRules sevm d k v).stateGas.left =
      d.stateGas.left - sstoreChargeA amsterdamStateGasRules sevm d k v := by
    rw [afterSstoreA_stateGas]
    simp only [sstoreMeterA, hcredit, hrepay, Nat.sub_zero, Nat.add_zero]
  have hspilled : (afterSstoreA amsterdamStateGasRules sevm d k v).stateGas.spilled =
      d.stateGas.spilled + (sstoreChargeA amsterdamStateGasRules sevm d k v - d.stateGas.left) := by
    rw [afterSstoreA_stateGas]
    simp only [sstoreMeterA, sstoreSpillA, hcredit, hrepay, Nat.sub_zero, Nat.add_zero]
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hbudget
  refine ⟨(afterSstoreA_error _ sevm d k v).trans r.error, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [afterSstoreA_refundCounter]
    exact Int.le_trans r.refund (sstoreAmsterdamRefund_ge _ _ (Or.inl hclean))
  · have h : (afterSstoreA amsterdamStateGasRules sevm d k v).accountsToDelete = d.accountsToDelete := by
      unfold afterSstoreA Devm.balReadAccount Devm.balReadStorage
      dsimp only
      split <;> split <;> rfl
    rw [h]
    exact r.deleted
  · intro k' hk'
    have hne : k ≠ k' := fun e => fresh (e ▸ hk')
    have hk := r.clean k' (List.mem_cons_of_mem _ hk')
    unfold Devm.getOrigStorVal at hk ⊢
    rw [afterSstoreA_createdAccounts, afterSstoreA_getStorVal_ne sevm d v hne]
    exact hk
  · rw [hleft]
    omega
  · rw [hleft, hspilled]
    omega
  · rw [afterSstoreA_stateGas]
    exact r.committed
  · omega

/-- One store at an untouched slot: `Fresh` goes on, with the rest of the keys, and it repays no spill. -/
theorem step {k : B256} {ks : List B256} (r : Fresh sevm d (k :: ks) grant used n) (nodup : (k :: ks).Nodup) (v : B256) :
    (∃ used', Fresh sevm (afterSstoreA amsterdamStateGasRules sevm d k v) ks grant used' n) ∧ ks.Nodup ∧
      sstoreRepayA amsterdamStateGasRules sevm d k v = 0 :=
  ⟨⟨_, r.sstore (List.nodup_cons.mp nodup).1 v⟩, (List.nodup_cons.mp nodup).2,
    repay_zero v (r.clean k List.mem_cons_self)⟩

/-- `Fresh` passes through a machine-register replacement. -/
theorem st (r : Fresh sevm d keys grant used n) (S : List B256) (M : Mem) (G : Nat) :
    Fresh sevm (St d S M G) keys grant used n :=
  ⟨r.error, r.refund, r.deleted, r.clean, r.drawn, r.ledger, r.committed, r.budget⟩

end Fresh

end Blanc.Lift
