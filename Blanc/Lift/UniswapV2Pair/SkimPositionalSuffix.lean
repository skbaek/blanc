import Blanc.Lift.UniswapV2Pair.SkimPositionalFour
import Blanc.Lift.UniswapV2Pair.SkimRawFacts
import Blanc.Lift.CursorNoExecSuffix
import Blanc.Lift.CursorSourceRunReturn

namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem SkimFourCallsH.noExecTail {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (r : SkimFourCallsH root b toWord R) (stateGas : root.sevm.benvStat.rules.stateGas = none) :
    ∀ N, Exec.Deriv.ParentPrefix r.transfer.call.returned N → ∀ x,
      ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  have env : r.transfer.call.returned.sevm = root.sevm :=
    Blanc.Exec.Deriv.ParentPrefix.sevm_eq (r.transfer.call.sameFrame.snoc r.transfer.call.edge)
  apply r.transfer.placed.noExecSuffixH cert_check (by rw [env]; exact stateGas)
    (E := [16, 17, 73]) (by decide)
  · rw [r.transfer.tree]; decide
  · intro f member
    rw [r.transfer.continuations] at member
    simp only [List.mem_singleton] at member
    subst f
    decide

/-- The original final CALL's checked helper/caller suffix contains no further
external instruction, including its real pending return and stop entry. -/
theorem SkimFourCalls.noExecTail {root : Exec.Deriv} {b : Devm} {toWord : B256} {R : List B256}
    (r : SkimFourCalls root b toWord R) (fork : CoveredFork root.sevm.benvStat.fork) :
    ∀ N, Exec.Deriv.ParentPrefix r.transfer.call.returned N → ∀ x,
      ¬ Ninst.At N.sevm.code N.pc (.exec x) :=
  SkimFourCallsH.noExecTail (r.toH fork) fork.rules_stateGas_none


theorem SkimFourCallsH.post_image {root : Exec.Deriv} {b post : Devm} {toWord : B256}
    (r : SkimFourCallsH root b toWord [0x0257, 0xbc25cf77])
    (success : root.exn = .ok post) (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (bal : root.sevm.benvStat.rules.bal = none) :
    ∃ M G, post = St (afterSstoreH root.sevm r.transfer.call.returned.devm 12 1)
      [0xbc25cf77] M G := by
  let cut := r.transfer.returned
  have reached := r.transfer.call.sameFrame.snoc r.transfer.call.edge
  have env : cut.node.sevm = root.sevm := cut.sevm_eq.trans
    (Blanc.Exec.Deriv.ParentPrefix.sevm_eq reached)
  have outcome : cut.node.exn = .ok post := cut.exn_eq.trans
    ((Blanc.Exec.Deriv.ParentPrefix.exn_eq reached).trans success)
  rcases cut.placed.sourceRunReturnH cert_check outcome (by rw [env]; exact stateGas) with halted | returned
  · obtain ⟨G, state⟩ := cut.state
    rw [cut.tree, state, env] at halted
    exact skimUnlockTail_invH stateGas bal (SFunc.runP_iff_runCutP_nil.mp halted)
  · obtain ⟨continuation, tail, d, run, stack, rest⟩ := returned
    have conts := cut.continuations
    rw [stack, List.map_cons] at conts
    cases conts

/-- The final unlock image is derived from the actual original successful
continuation, whose mapped continuation stack is empty. -/
theorem SkimFourCalls.post_image {root : Exec.Deriv} {b post : Devm} {toWord : B256}
    (r : SkimFourCalls root b toWord [0x0257, 0xbc25cf77])
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    ∃ M G, post = St (afterSstore root.sevm r.transfer.call.returned.devm 12 1)
      [0xbc25cf77] M G := by
  have h := SkimFourCallsH.post_image (r.toH fork) success fork.rules_stateGas_none fork.rules_bal_none
  simp only [afterSstoreH_of_eip2929 fork.rules_access (by rw [fork.rules_sstore])] at h
  exact h


theorem SkimFourCallsH.output_eq {root : Exec.Deriv} {b post : Devm} {toWord : B256}
    (r : SkimFourCallsH root b toWord [0x0257, 0xbc25cf77])
    (success : root.exn = .ok post) (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (bal : root.sevm.benvStat.rules.bal = none) :
    post.output = b.output := by
  obtain ⟨M, G, image⟩ := r.post_image success stateGas bal
  rw [image, St, Devm.setMach_output, afterSstoreH_output, r.transfer.output, r.reply.reply.output rfl,
    SkimTwoCallsH.secondWorld, accountAccessH_output, afterSloadH_output,
    r.two.transfer.output, r.two.first.reply.output rfl, accountAccessH_output,
    skim_cached_outputH]

/-- Every physical static reply and transfer return preserves this invocation's
output; the actual unlock/STOP result has the same bytes. -/
theorem SkimFourCalls.output_eq {root : Exec.Deriv} {b post : Devm} {toWord : B256}
    (r : SkimFourCalls root b toWord [0x0257, 0xbc25cf77])
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    post.output = b.output :=
  SkimFourCallsH.output_eq (r.toH fork) success fork.rules_stateGas_none fork.rules_bal_none


end Blanc.Lift.UniswapV2Pair
