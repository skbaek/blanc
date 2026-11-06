import Blanc.Lift.BalanceLocality

/-!
# A frame whose chain executes only `STATICCALL`

`chain_static_descendants`: such a frame's descendants are all static, so its writes lie on its own chain. A code with one
calling path, like FiatToken's `rescueERC20`, is a `CertFrame` on every other selector. With `ReachKinds` for the chain.
-/

namespace Blanc.Lift

open Jaune Blanc

/-- **A frame whose chain executes only `STATICCALL` has static descendants.** -/
theorem chain_static_descendants {root : Exec.Deriv}
    (only : ∀ N, Exec.Deriv.ParentPrefix root N → ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .staticcall) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, out, run⟩ →
      ∀ D ∈ Exec.rawFrameDescendants run, D.sevm.isStatic = true := by
  intro pc sevm pre out run
  induction run with
  | halt step => simp only [Exec.rawFrameDescendants, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true]
  | cont step next ih =>
    intro chain
    simpa only [Exec.rawFrameDescendants] using ih (chain.snoc (.cont step next))
  | doneErr step enter resume => simp only [Exec.rawFrameDescendants, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  | doneOk step enter resume next ih =>
    intro chain
    simpa only [Exec.rawFrameDescendants] using ih (chain.snoc (.doneOk step enter resume next))
  | runErr step enter child resume ih =>
    intro chain D member
    obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
    have onlyStatic : x = .staticcall := only _ chain x instruction
    subst x
    have stc := (Frame.enter_run_isStatic enter).trans (Xinst.step_staticcall_spawn_isStatic spawn)
    exact Exec.rawFrameRoots_isStatic child stc D (by
      simpa only [Exec.rawFrameRoots, Exec.rawFrameDescendants] using member)
  | runOk step enter child resume next childIH nextIH =>
    intro chain D member
    obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
    have onlyStatic : x = .staticcall := only _ chain x instruction
    subst x
    have stc := (Frame.enter_run_isStatic enter).trans (Xinst.step_staticcall_spawn_isStatic spawn)
    simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at member
    rcases member with rfl | member | member
    · exact stc
    · exact Exec.rawFrameRoots_isStatic child stc D (List.mem_cons_of_mem _ member)
    · exact nextIH (chain.snoc (.runOk step enter child resume next)) D member

end Blanc.Lift
