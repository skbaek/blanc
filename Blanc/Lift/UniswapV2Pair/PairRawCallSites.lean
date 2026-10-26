import Blanc.Lift.CallSiteChildren
import Blanc.Lift.UniswapV2Pair.SafeTransferWalk

/-! The two actual CALL suffixes of the Pair, independent of final success or settlement. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The literal continuation of the callback CALL at t_09aa_c4. -/
def pairCallback_afterCall : SFunc :=
  .next (.reg .iszero) (.next (.reg (.dup 0)) (.next (.reg .iszero)
    (.next (.push [0x09, 0xbe] (by decide)) (.branch t_09b5_c4 t_09be_c4))))

/-- Only STATICCALL, or CALL at one of the two literal continuations, passes the node check. -/
def pairCallSiteCheck : Ninst → SFunc → Bool
  | .exec x, tail => (x == .staticcall) ||
      ((x == .call) && decide (tail = safeTransfer_afterCall ∨ tail = pairCallback_afterCall))
  | _, _ => true

private theorem pair_call_sites_checked :
    ∀ f ∈ cert.prog, f.nodesSatisfy pairCallSiteCheck = true := by
  have checked : cert.prog.all (fun f => f.nodesSatisfy pairCallSiteCheck) = true := by
    decide +kernel
  exact List.all_eq_true.mp checked

/-- Every raw source prefix from pc zero reaches either STATICCALL or one of the two exact
CALL suffixes. The instruction relation and starting machine are unrestricted. -/
theorem pair_raw_reach_call_sites {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {d : Devm} {T : Conf} {x : Xinst} {tail : SFunc}
    (run : Reach P cert.prog sevm ⟨d, t_0000_c0, []⟩ T)
    (instruction : T.f = .next (.exec x) tail) :
    x = .staticcall ∨
      (x = .call ∧ (tail = safeTransfer_afterCall ∨ tail = pairCallback_afterCall)) := by
  change Reach _ _ _ ((Cursor.start cert).conf d) T at run
  have checked := (Reach.nodesSatisfy pair_call_sites_checked run).1
  rw [instruction] at checked
  simp only [SFunc.nodesSatisfy, Bool.and_eq_true] at checked
  simpa only [pairCallSiteCheck, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] using checked.1

/-- An actual decoded node of a raw Pair frame retains its original StepIn-root reach and
checked cursor while its external instruction is classified. No final outcome or child
commitment is required; this source restriction adds no history-exclusion premise. -/
theorem pair_raw_node_call_sites {root node : Exec.Deriv} {x : Xinst}
    (pc : root.pc = 0) (codeEq : root.sevm.code = code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (instruction : Ninst.At node.sevm.code node.pc (.exec x)) :
    ∃ cursor : Cursor,
      Reach (StepIn root) cert.prog root.sevm
        ((Cursor.start cert).conf root.devm) (cursor.conf node.devm) ∧
      CursorOK code cert node cursor ∧
      (x = .staticcall ∨ (x = .call ∧
        (cursor.f = .next (.exec .call) safeTransfer_afterCall ∨
         cursor.f = .next (.exec .call) pairCallback_afterCall))) := by
  obtain ⟨cursor, reach, placed⟩ :=
    reach_of_parentPrefix_noStateGas cert_check pc codeEq hsg chain
  obtain ⟨tail, shape, _⟩ := placed.tree_of_exec instruction
  have classified := pair_raw_reach_call_sites reach shape
  refine ⟨cursor, reach, placed, ?_⟩
  rcases classified with static | ⟨rfl, transfer | callback⟩
  · exact Or.inl static
  · exact Or.inr ⟨rfl, Or.inl (by rw [shape, transfer])⟩
  · exact Or.inr ⟨rfl, Or.inr (by rw [shape, callback])⟩

end Blanc.Lift.UniswapV2Pair
