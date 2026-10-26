import Blanc.Lift.InvWalk
import Blanc.LadderBase

/-! Metadata and the physical input window of a raw historical DELEGATECALL.
No commitment, delegation-designator, BAL, or access-schedule premise is needed. -/

namespace Blanc.Lift

open Jaune Blanc

/-- A spawning DELEGATECALL inherits the execution context and reads the exact
input window of the original symbolic machine. State-gas absence is the only
rule constraint; address delegation may still select a different code account. -/
theorem Xinst.step_delegatecall_spawn_St_noStateGas {sevm : Sevm} {b : Devm}
    {g w ii sz oi os : B256} {S : List B256} {M : Mem} {G : Nat}
    {frame : Jaune.Frame} {resume : Resume}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (spawn : Xinst.step sevm (St b (g :: w :: ii :: sz :: oi :: os :: S) M G)
      .delegatecall = .spawn frame resume) :
    frame.inner.currentTarget = sevm.currentTarget ∧
      frame.inner.caller = sevm.caller ∧ frame.inner.value = sevm.value ∧
      frame.inner.isStatic = sevm.isStatic ∧
      frame.inner.data = (M.read ii.toNat sz.toNat).1 := by
  simp only [Xinst.step, hsg, Bind.bind, Except.bind] at spawn
  rw [show (St b (g :: w :: ii :: sz :: oi :: os :: S) M G).pop =
    .ok (g, St b (w :: ii :: sz :: oi :: os :: S) M G) from rfl] at spawn
  dsimp only at spawn
  rw [show (St b (w :: ii :: sz :: oi :: os :: S) M G).popToAdr =
    .ok (w.toAdr, St b (ii :: sz :: oi :: os :: S) M G) from rfl] at spawn
  dsimp only at spawn
  rw [show (St b (ii :: sz :: oi :: os :: S) M G).popToNat =
    .ok (ii.toNat, St b (sz :: oi :: os :: S) M G) from rfl] at spawn
  dsimp only at spawn
  rw [show (St b (sz :: oi :: os :: S) M G).popToNat =
    .ok (sz.toNat, St b (oi :: os :: S) M G) from rfl] at spawn
  dsimp only at spawn
  rw [show (St b (oi :: os :: S) M G).popToNat =
    .ok (oi.toNat, St b (os :: S) M G) from rfl] at spawn
  dsimp only at spawn
  rw [show (St b (os :: S) M G).popToNat =
    .ok (os.toNat, St b (S) M G) from rfl] at spawn
  dsimp only at spawn
  split at spawn
  · simp only [XStep.ofExcept, reduceCtorEq] at spawn
  rename_i charged charge
  simp only [Pure.pure, Except.pure, XStep.ofExcept] at spawn
  obtain ⟨same, _⟩ := genericCall_step_spawn_exact spawn
  subst frame
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · simp only [Jaune.Frame.ofCall, callMsg, Bool.false_or]
  · show ((charged.memory.extends [(ii.toNat, sz.toNat), (oi.toNat, os.toNat)]).read
      ii.toNat sz.toNat).1 = _
    rw [← (Devm.burn_of_chargeGas charge).memory, ForkRules.accessDelegation_memory]
    cases sevm.benvStat.rules.access <;> rfl

end Blanc.Lift
