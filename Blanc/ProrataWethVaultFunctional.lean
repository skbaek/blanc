-- ProrataWethVaultFunctional.lean : compiled selector entry for the vault.

import Blanc.ProrataWethVaultArithmetic
import Blanc.CommonProofs
import Blanc.Compiled

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace ProrataWethVault

/-!
# Compiled vault entry

The endpoint laws in this family are proved about executions of the compiled
vault, not about a body supplied by a caller.  This module specializes Blanc's
neutral sorted-dispatch reachability theorem to `vault`, then peels the two
shared wrappers.  A successful execution therefore reaches the exact selected
body with the entry state, memory, event log, and output buffer preserved.

The static-argument fact is a conclusion.  In particular, endpoint theorems do
not assume that malformed calldata somehow reached a body; the successful run
itself rules out the reverting guard arm.
-/

/-- The shared nonpayable wrapper is silent in the log and output frames as
well as in the state and memory frames exported by the neutral seam. -/
private theorem run_body_of_run_nonpayable_frame_logs
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
  · exact absurd hrev not_run_rev
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

/-- A successful static-argument wrapper reaches its body, and the exact EVM
comparison word must be zero.  This statement remains exact even for calldata
lengths whose `Nat.toB256` image wraps. -/
private theorem run_body_of_run_requireStaticArgs_frame_logs
    {fs : List Func} {sevm : Sevm} {s r : Devm} {words : Nat} {body : Func}
    (run : Func.Run fs sevm s (requireStaticArgs words body) r) :
    ∃ mid,
      B256.ltCheck sevm.data.length.toB256
          (Nat.toB256 (4 + 32 * words)) = 0 ∧
      s.state = mid.state ∧ s.memory = mid.memory ∧
      s.logs = mid.logs ∧ s.output = mid.output ∧
      Func.Run fs sevm mid body r := by
  unfold requireStaticArgs at run
  refine run_prepend_elim _
    [pushB256 (Nat.toB256 (4 + 32 * words)), calldatasize, lt] ?_ run
  intro testPre hline hbranch
  rcases Line.of_run_cons hline with ⟨afterWord, qword, hline⟩
  rcases Line.of_run_cons hline with ⟨afterSize, qsize, hline⟩
  rcases Line.of_run_cons hline with ⟨afterTest, qlt, hnil⟩
  cases hnil
  have p1 : [Nat.toB256 (4 + 32 * words)] <<+ afterWord.stack :=
    prefix_of_push (of_run_pushB256 qword) nil_pref
  have p2 : [sevm.data.length.toB256,
      Nat.toB256 (4 + 32 * words)] <<+ afterSize.stack :=
    prefix_of_push (of_run_calldatasize qsize) p1
  have p3 : [B256.ltCheck sevm.data.length.toB256
      (Nat.toB256 (4 + 32 * words))] <<+ testPre.stack :=
    prefix_of_lt qlt p2
  rcases of_run_branch hbranch with
    ⟨bodyPre, hpop, hbody⟩ |
    ⟨w, popped, revPre, hnz, hpop, hburn, hrev⟩
  · have hguard : B256.ltCheck sevm.data.length.toB256
        (Nat.toB256 (4 + 32 * words)) = 0 :=
      (popBurn_pref hpop p3).1.symm
    refine ⟨bodyPre, hguard, ?_, ?_, ?_, ?_, hbody⟩
    · exact (Line.of_inv Devm.state (by line_inv)
        (Line.Run.cons qword (Line.Run.cons qsize
          (Line.Run.cons qlt Line.Run.nil)))).trans hpop.state
    · exact (Line.of_inv Devm.memory (by line_inv)
        (Line.Run.cons qword (Line.Run.cons qsize
          (Line.Run.cons qlt Line.Run.nil)))).trans hpop.memory
    · exact ((of_run_pushB256 qword).logs.trans
        ((of_run_calldatasize qsize).logs.trans
          (Ninst.Hinv.inv (f := Devm.logs) qlt))).trans hpop.logs
    · exact ((of_run_pushB256 qword).output.trans
        ((of_run_calldatasize qsize).output.trans
          (Ninst.Hinv.inv (f := Devm.output) qlt))).trans hpop.output
  · exact absurd hrev not_run_rev

/-! ## Exact selector and body entry -/

/-- A successful compiled vault run with a recognized selector reaches that
selector's exact routed endpoint.  Selector extraction and dispatch are silent
in every frame used by the functional endpoint laws. -/
theorem runCompiled_enters_endpoint_logs
    {sevm : Sevm} {pre post : Devm} {sig : B256}
    {words : Nat} {body : Func}
    (run : Prog.RunCompiled sevm pre vault post)
    (hselector : Sevm.selector sevm = sig)
    (hmember : (sig, routed words body) ∈ vaultFuncs) :
    ∃ mid,
      pre.state = mid.state ∧ pre.memory = mid.memory ∧
      pre.logs = mid.logs ∧ pre.output = mid.output ∧
      Func.Run (vault.main :: vault.aux) sevm mid
        (endpoint words body) post := by
  have sourceRun : Prog.Run sevm pre vault post :=
    Prog.Run.of_runCompiled run
  dsimp only [Prog.Run] at sourceRun
  cases sourceRun
  rename (_ = _) => rootLookup
  rename (Func.Run _ _ _ _ _) => rootRun
  rename (Devm.Burn _ _) => rootBurn
  rename Devm => rootPre
  cases rootLookup
  have mainRun :
      Func.Run (vault.main :: vault.aux) sevm rootPre
        (fsig +++ dispatchWith revertSlot vaultTree) post := by
    simpa only [vault, Func.mainWith] using rootRun
  refine run_prepend_elim _ fsig ?_ mainRun
  intro dispatchPre hfsig hdispatch
  have selectorPrefix : sig :: [] <<+ dispatchPre.stack := by
    rw [← hselector]
    exact prefix_of_fsig nil_pref hfsig
  rcases reach_of_dispatchWith_logs vaultFuncs_sorted hmember
      selectorPrefix hdispatch with
    ⟨selectedPre, -, dispatchState, dispatchMemory, dispatchLogs,
      dispatchOutput, selectedRun⟩
  refine ⟨selectedPre, ?_, ?_, ?_, ?_, ?_⟩
  · exact rootBurn.state.trans
      ((Line.of_inv Devm.state (by line_inv) hfsig).trans dispatchState)
  · exact rootBurn.memory.trans
      ((Line.of_inv Devm.memory (by line_inv) hfsig).trans dispatchMemory)
  · exact rootBurn.logs.trans
      ((fsig_logs hfsig).trans dispatchLogs)
  · exact rootBurn.output.trans
      ((fsig_output hfsig).trans dispatchOutput)
  · simpa only [routed] using selectedRun

/-- A successful compiled vault run with a recognized selector reaches the
actual endpoint body.  Nonpayability and sufficient static calldata are
derived, while the complete functional frame is carried from program entry. -/
theorem runCompiled_enters_body_logs
    {sevm : Sevm} {pre post : Devm} {sig : B256}
    {words : Nat} {body : Func}
    (run : Prog.RunCompiled sevm pre vault post)
    (hselector : Sevm.selector sevm = sig)
    (hmember : (sig, routed words body) ∈ vaultFuncs) :
    ∃ bodyPre,
      sevm.value = 0 ∧
      B256.ltCheck sevm.data.length.toB256
          (Nat.toB256 (4 + 32 * words)) = 0 ∧
      pre.state = bodyPre.state ∧ pre.memory = bodyPre.memory ∧
      pre.logs = bodyPre.logs ∧ pre.output = bodyPre.output ∧
      Func.Run (vault.main :: vault.aux) sevm bodyPre body post := by
  rcases runCompiled_enters_endpoint_logs run hselector hmember with
    ⟨endpointPre, endpointState, endpointMemory, endpointLogs,
      endpointOutput, endpointRun⟩
  unfold endpoint at endpointRun
  rcases run_body_of_run_nonpayable_frame_logs endpointRun with
    ⟨staticPre, hvalue, wrapperState, wrapperMemory, wrapperLogs,
      wrapperOutput, staticRun⟩
  rcases run_body_of_run_requireStaticArgs_frame_logs staticRun with
    ⟨bodyPre, hguard, staticState, staticMemory, staticLogs,
      staticOutput, bodyRun⟩
  exact ⟨bodyPre, hvalue, hguard,
    endpointState.trans (wrapperState.trans staticState),
    endpointMemory.trans (wrapperMemory.trans staticMemory),
    endpointLogs.trans (wrapperLogs.trans staticLogs),
    endpointOutput.trans (wrapperOutput.trans staticOutput), bodyRun⟩

end ProrataWethVault

end Blanc
