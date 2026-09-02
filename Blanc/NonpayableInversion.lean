-- NonpayableInversion.lean : contract-neutral source-wrapper inversion.

import Blanc.CommonProofs

/-!
# Nonpayable wrapper inversion

`run_body_of_run_nonpayable_frame` carries state and memory across Blanc's
shared `nonpayable` wrapper.  Event and returndata-sensitive composition also
needs the wrapper's unchanged log and output frames.  This module owns that
stronger neutral seam so contract families do not reproduce its instruction
walk locally.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

/-- A successful run through the shared `nonpayable` wrapper reaches its body
with zero call value and unchanged state, memory, logs, and output. -/
theorem run_body_of_run_nonpayable_frame_logs
    {fs : List Func} {sevm : Sevm} {s r : Devm} {body : Func}
    (run : Func.Run fs sevm s (nonpayable body) r) :
    ∃ mid, sevm.value = 0 ∧ s.state = mid.state ∧
      s.memory = mid.memory ∧ s.logs = mid.logs ∧
      s.output = mid.output ∧ Func.Run fs sevm mid body r := by
  unfold nonpayable at run
  refine run_prepend_elim _ [callvalue, iszero] ?_ run
  intro s1 hline hbranch
  rcases Line.of_run_cons hline with ⟨s0, hcv, hline'⟩
  rcases Line.of_run_cons hline' with ⟨s1', hiz, hnil⟩
  cases hnil
  have hpv : [sevm.value] <<+ s0.stack :=
    prefix_of_push (of_run_callvalue hcv) nil_pref
  have hpflag : [sevm.value =? 0] <<+ s1.stack :=
    prefix_of_iszero hiz hpv
  rcases of_run_branch hbranch with
    ⟨s2, hpop, hrev⟩ |
    ⟨w, s2, s3, hnz, hpop, hburn, hbody⟩
  · exact absurd hrev not_run_revert
  · have hpop' := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpop'
    rw [hpop'] at hpflag
    have hw : (sevm.value =? 0) = w :=
      pref_head_unique hpflag (pref_append [w] s2.stack)
    have hflag : (sevm.value =? 0) ≠ 0 := by
      rw [hw]
      exact hnz
    have hvalue : sevm.value = 0 := by
      by_cases hvalue : sevm.value = 0
      · exact hvalue
      · simp [B256.eqCheck, hvalue] at hflag
    refine ⟨s3, hvalue, ?_, ?_, ?_, ?_, hbody⟩
    · exact (Line.of_inv Devm.state (by line_inv) hline).trans
        (hpop.state.trans hburn.state)
    · exact (Line.of_inv Devm.memory (by line_inv) hline).trans
        (hpop.memory.trans hburn.memory)
    · exact ((of_run_callvalue hcv).logs.trans
        (Ninst.Hinv.inv (f := Devm.logs) hiz)).trans
          (hpop.logs.trans hburn.logs)
    · exact ((of_run_callvalue hcv).output.trans
        (Ninst.Hinv.inv (f := Devm.output) hiz)).trans
          (hpop.output.trans hburn.output)

end Blanc
