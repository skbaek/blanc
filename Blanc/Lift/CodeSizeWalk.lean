import Blanc.Lift.InvWalkWorld

/-! Shared warmth-aware EXTCODESIZE steps, hoisted from the temporal account
access donor and preserving its exact value, charge, and metadata image. -/
namespace Blanc.Lift

open Jaune

private theorem addAccessedAddress_setMach_setMach
    {base : Devm} {a : Adr} {m m' : Mach} :
    (addAccessedAddress (base.setMach m) a).setMach m' =
      (addAccessedAddress base a).setMach m' := rfl

/-- The world after an account access: unchanged when the address was warm,
warmed otherwise. -/
def temporalAccountAccessBase (base : Devm) (a : Adr) : Devm :=
  if a ∈ base.accessedAddresses then base else addAccessedAddress base a

/-- Account warming preserves the complete world state. -/
theorem temporalAccountAccessBase_state (base : Devm) (a : Adr) :
    (temporalAccountAccessBase base a).state = base.state := by
  unfold temporalAccountAccessBase
  split <;> rfl

/-- Account warming preserves the parent output. -/
theorem temporalAccountAccessBase_output (base : Devm) (a : Adr) :
    (temporalAccountAccessBase base a).output = base.output := by
  unfold temporalAccountAccessBase
  split <;> rfl

/-- Account warming preserves the ordered parent logs. -/
theorem temporalAccountAccessBase_logs (base : Devm) (a : Adr) :
    (temporalAccountAccessBase base a).logs = base.logs := by
  unfold temporalAccountAccessBase
  split <;> rfl

/-- The warmth-dependent account-access charge. -/
def temporalAccountAccessCost (base : Devm) (a : Adr) : Nat :=
  if a ∈ base.accessedAddresses then gasWarmAccess else gasColdAccountAccess

/-- Exact `EXTCODESIZE` step in the temporal convention: the charge is the
entry world's `temporalAccountAccessCost`, and the successor world is its
`temporalAccountAccessBase`. -/
theorem temporal_extcodesize_runCompiled
    {sevm : Sevm} {base : Devm} {x v : B256}
    {stack : List B256} {M : Mem} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hval : (base.getCode x.toAdr).size.toB256 = v)
    (hroom : stack.length < 1024) :
    Ninst.RunCompiled sevm
      (base.setMach ⟨x :: stack, M,
        G + temporalAccountAccessCost base x.toAdr, base.stateGas⟩)
      Ninst.extcodesize
      ((temporalAccountAccessBase base x.toAdr).setMach ⟨v :: stack, M, G, (temporalAccountAccessBase base x.toAdr).stateGas⟩) := by
  by_cases hwarm : x.toAdr ∈ base.accessedAddresses
  · simp only [temporalAccountAccessBase, temporalAccountAccessCost,
      ite_eq_left hwarm]
    simpa only [Devm.setMach_setMach, Devm.stateGas_setMach, Devm.memory_setMach] using
      Ninst.runCompiled_extcodesize_warm
        (devm := base.setMach ⟨x :: stack, M, G + gasWarmAccess, base.stateGas⟩)
        hfork.rules_stateGas_none rfl hwarm hval (by simp only [Devm.gasLeft_setMach]) hroom
  · simp only [temporalAccountAccessBase, temporalAccountAccessCost,
      ite_eq_right hwarm]
    have hsg : (addAccessedAddress base x.toAdr).stateGas = base.stateGas := rfl
    simpa only [addAccessedAddress_setMach_setMach, Devm.memory_setMach,
      Devm.stateGas_setMach, hsg] using
      Ninst.runCompiled_extcodesize_cold
        (devm := base.setMach ⟨x :: stack, M, G + gasColdAccountAccess, base.stateGas⟩)
        hfork.rules_stateGas_none rfl hwarm hval (by simp only [Devm.gasLeft_setMach]) hroom

/-- `EXTCODESIZE`, inverted with its actual account-warming image. -/
theorem ri_extcodesize {sevm : Sevm} {b d : Devm} {S : List B256}
    {M : Mem} {G : Nat} {x : B256}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (x :: S) M G) (.reg .extcodesize) d) :
    ∃ G', d = St (temporalAccountAccessBase b x.toAdr)
      ((b.getCode x.toAdr).size.toB256 :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore,
    Devm.balReadAccount_of_bal_none hfork.rules_bal_none] at run
  rw [BenvStat.gas_eq_prague_of_stateGas_none hfork.rules_stateGas_none] at run
  rw [show (St b (x :: S) M G).popToAdr = .ok (x.toAdr, St b S M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b S M G).accessedAddresses = b.accessedAddresses from rfl] at run
  by_cases hw : x.toAdr ∈ b.accessedAddresses
  · simp only [hw, ite_true] at run
    rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
    have e2 := Devm.eq_of_push_ok h2
    subst e2
    have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
    rw [e1]
    refine ⟨s1.gasLeft, ?_⟩
    simp only [temporalAccountAccessBase, hw, ite_true]
    rfl
  · simp only [hw, ite_false] at run
    rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
    have e2 := Devm.eq_of_push_ok h2
    subst e2
    have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
    rw [e1]
    refine ⟨s1.gasLeft, ?_⟩
    simp only [temporalAccountAccessBase, hw, ite_false]
    rfl

/-- `EXTCODESIZE`, with the selected warm/cold charge and exact continuation. -/
theorem rx_extcodesize {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {S : List B256} {M : Mem} {G : Nat} {x : B256} {f : SFunc} {o : Outcome}
    (hfork : CoveredFork sevm.benvStat.fork) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm
      (St (temporalAccountAccessBase b x.toAdr)
        ((b.getCode x.toAdr).size.toB256 :: S) M G) f o) :
    SFunc.RunExact fs sevm
      (St b (x :: S) M (G + temporalAccountAccessCost b x.toAdr))
      (.next (.reg .extcodesize) f) o :=
  .next (temporal_extcodesize_runCompiled hfork rfl hroom) k

end Blanc.Lift
