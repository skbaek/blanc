import Blanc.Lift.HistCursorReturn
import Blanc.Lift.CursorStateCuts
import Blanc.Lift.CursorCutsToward
import Blanc.Lift.CursorOccurrence
import Blanc.Lift.ReachWalkSstore
import Blanc.Lift.CursorTreeNinst
import Blanc.Lift.RunPWalk

/-! Actual frame-free state cuts carrying the remaining path to an SSTORE. -/

namespace Blanc.Lift

open Jaune

/-- The existing actual state cut, together with the remaining raw path to the
observed SSTORE. The enclosing frame may have any final outcome. -/
structure CursorStateToward (code : ByteArray) (c : Cert) (start target : Exec.Deriv)
    (f : SFunc) (b : Devm) (S : List B256) (M : Mem) (K : List SFunc)
    extends CursorStateAt code c start f b S M K where
  toward : Exec.Deriv.ParentPrefix node target
  store : Ninst.At target.sevm.code target.pc (.reg .sstore)

/-- Cross one actual checked jump, using its real stateful step. -/
theorem CursorStateToward.jumpStep {code : ByteArray} {c : Cert} {start target : Exec.Deriv}
    {f tail : SFunc} {b b' : Devm} {S S' : List B256} {M M' : Mem} {K nextK : List SFunc}
    (cut : CursorStateToward code c start target f b S M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none)
    (different : ∀ tail, f ≠ .next (.reg .sstore) tail)
    {j : Jinst} (decoded : Jinst.At cut.node.sevm.code cut.node.pc j)
    (inverse : ∀ {G d f' K'},
      ConfStep (Ninst.RunWith (Cursor.DescOf cut.node)) c.prog start.sevm
        ⟨St b S M G, f, K⟩ ⟨d, f', K'⟩ →
      f' = tail ∧ K' = nextK ∧ ∃ G', d = St b' S' M' G') :
    ∃ result : CursorStateToward code c start target tail b' S' M' nextK,
      Exec.Deriv.ParentStep result.node cut.node := by
  obtain ⟨N, next, edge, later, _, stateful, placed⟩ :=
    cursor_step_toward_sstore_noStateGas checked cut.placed cut.toward cut.store
      (fun tail same => different tail (cut.tree.symm.trans same)) (cut.sevm_eq ▸ hsg)
  obtain ⟨G, state⟩ := cut.state
  have step : ConfStep (Ninst.RunWith (Cursor.DescOf cut.node)) c.prog start.sevm
      ⟨St b S M G, f, K⟩ ⟨N.devm, next.f, next.K.map Cont.f⟩ := by
    simpa only [Cursor.conf, cut.sevm_eq, state, cut.tree, cut.continuations] using stateful
  obtain ⟨tree, conts, state⟩ := inverse step
  have outcome : N.exn = cut.node.exn := by
    generalize origin : cut.node = F at edge ⊢
    cases edge <;> rfl
  exact ⟨{ toCursorStateAt := ⟨N, next, cut.free.trans
    (Exec.Deriv.ExecFreeUntil.ofStep edge (Blanc.Jinst.At.not_exec decoded)),
    (Cursor.parentStep_sevm edge).trans cut.sevm_eq, outcome.trans cut.exn_eq,
    placed, tree, state, conts⟩, toward := later, store := cut.store }, edge⟩

/-- Project the successor state cut of an actual checked jump. -/
theorem CursorStateToward.jump {code : ByteArray} {c : Cert} {start target : Exec.Deriv}
    {f tail : SFunc} {b b' : Devm} {S S' : List B256} {M M' : Mem} {K nextK : List SFunc}
    (cut : CursorStateToward code c start target f b S M K)
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none)
    (different : ∀ tail, f ≠ .next (.reg .sstore) tail)
    {j : Jinst} (decoded : Jinst.At cut.node.sevm.code cut.node.pc j)
    (inverse : ∀ {G d f' K'},
      ConfStep (Ninst.RunWith (Cursor.DescOf cut.node)) c.prog start.sevm
        ⟨St b S M G, f, K⟩ ⟨d, f', K'⟩ →
      f' = tail ∧ K' = nextK ∧ ∃ G', d = St b' S' M' G') :
    Nonempty (CursorStateToward code c start target tail b' S' M' nextK) := by
  obtain ⟨result, _⟩ := cut.jumpStep checked hsg different decoded inverse
  exact ⟨result⟩

section ControlCuts

variable {code : ByteArray} {c : Cert} {start : Exec.Deriv} {b : Devm}
  {S : List B256} {M : Mem} {K : List SFunc} {target : Exec.Deriv}

/-- An actual internal return uses its real pending continuation and preserves
all machine fields except the residual gas charged by the return. -/
theorem CursorStateToward.ret {f : SFunc} {address : B256}
    (cut : CursorStateToward code c start target .ret b (address :: S) M (f :: K))
    (checked : Cert.check code c = true) (hsg : start.sevm.benvStat.rules.stateGas = none) :
    Nonempty (CursorStateToward code c start target f b S M K) := by
  apply cut.jump checked hsg (by intro tail same; cases same) (cut.placed.jumpAt_of_ret cut.tree)
  intro G d f' K' step
  cases step with
  | ret _ pop => exact ⟨rfl, rfl, _, (St.of_pop1 pop).2⟩

end ControlCuts

end Blanc.Lift
