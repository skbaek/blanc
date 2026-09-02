-- ProrataWethVaultFunctional.lean : compiled selector entry for the vault.

import Blanc.ProrataWethVaultArithmetic
import Blanc.CommonProofs
import Blanc.Compiled
import Blanc.CompiledWalkInversion
import Blanc.NonpayableInversion

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
    ⟨w, popped, revertPre, hnz, hpop, hburn, hrev⟩
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
  · exact absurd hrev not_run_revert

/-! ## Exact compiled binary dispatch

`reach_of_dispatchWith_logs` intentionally targets the loose safety semantics.
The vault's WETH boundaries additionally need the selected
`Func.RunCompiledTo` suffix: that is what retains the exact child slot at an
external instruction.  The following family-local companion follows the same
sorted tree, but uses Blanc's contract-neutral compiled-walk inversions.
-/

private theorem reach_of_dispatchWith_leaf_compiled_logs
    {sig w : B256} {f p : Func} {fs : List Func} {k : Nat}
    {sevm : Sevm} {s : Devm} {out : Execution} {tail : Stack}
    (hmember : (sig, f) ∈ [(w, p)])
    (hp : sig :: tail <<+ s.stack)
    (run : Func.RunCompiledTo fs sevm s
      (dispatchWith k (DispatchTree.leaf w p)) out) :
    ∃ bodyPre,
      tail <<+ bodyPre.stack ∧ s.state = bodyPre.state ∧
      s.memory = bodyPre.memory ∧ s.logs = bodyPre.logs ∧
      s.output = bodyPre.output ∧
      Func.RunCompiledTo fs sevm bodyPre f out := by
  have heq : (sig, f) = (w, p) := List.mem_singleton.mp hmember
  injection heq with hsig hbody
  subst hsig
  subst hbody
  change Func.RunCompiledTo fs sevm s
    ([pushB256 sig, eq] +++ (f <?> .call k)) out at run
  obtain ⟨testPre, testRun, branchRun⟩ := runCompiledTo_prepend_inv run
  rcases Line.of_run_cons testRun with ⟨afterPush, qpush, testRun⟩
  rcases Line.of_run_cons testRun with ⟨afterEq, qeq, hnil⟩
  cases hnil
  have p1 : [sig, sig] ++ tail <<+ afterPush.stack := by
    have pushed := prefix_of_push (of_run_pushB256 qpush) hp
    simpa only [List.cons_append, List.nil_append] using pushed
  have p2 : (1 : B256) :: tail <<+ testPre.stack := by
    have compared := prefix_of_eq qeq p1
    simpa [B256.eqCheck] using compared
  obtain ⟨bodyPre, branchWord, -, hpop, bodyRun, bodyStack⟩ :=
    Func.RunCompiledTo.succ_branch_of_prefix
      (by decide : (1 : B256) ≠ 0) p2 branchRun
  refine ⟨bodyPre, bodyStack, ?_, ?_, ?_, ?_, bodyRun⟩
  · exact (Line.of_inv Devm.state (by line_inv)
      (Line.Run.cons qpush (Line.Run.cons qeq Line.Run.nil))).trans hpop.state
  · exact (Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons qpush (Line.Run.cons qeq Line.Run.nil))).trans hpop.memory
  · exact (Line.of_inv Devm.logs (by line_inv)
      (Line.Run.cons qpush (Line.Run.cons qeq Line.Run.nil))).trans hpop.logs
  · exact (Line.of_inv Devm.output (by line_inv)
      (Line.Run.cons qpush (Line.Run.cons qeq Line.Run.nil))).trans hpop.output

private theorem reach_of_dispatchWith_build_compiled_logs :
    ∀ {n : Nat} {entries : List (B256 × Func)} {sig : B256} {body : Func}
      {fs : List Func} {k : Nat} {sevm : Sevm} {s : Devm}
      {out : Execution} {tail : Stack},
      DispatchTree.sorted entries = true →
      entries.length ≤ n + 1 →
      (sig, body) ∈ entries →
      (sig :: tail <<+ s.stack) →
      Func.RunCompiledTo fs sevm s
        (dispatchWith k (DispatchTree.build n entries)) out →
      ∃ bodyPre,
        tail <<+ bodyPre.stack ∧ s.state = bodyPre.state ∧
        s.memory = bodyPre.memory ∧ s.logs = bodyPre.logs ∧
        s.output = bodyPre.output ∧
        Func.RunCompiledTo fs sevm bodyPre body out := by
  intro n
  induction n with
  | zero =>
    intro entries sig body fs k sevm s out tail hsorted hlen hmember hp run
    rcases entries with _ | ⟨⟨w, p⟩, _ | ⟨y, ys⟩⟩
    · cases hmember
    · exact reach_of_dispatchWith_leaf_compiled_logs hmember hp run
    · exfalso
      simp only [List.length_cons] at hlen
      omega
  | succ n ih =>
    intro entries sig body fs k sevm s out tail hsorted hlen hmember hp run
    rcases entries with _ | ⟨⟨w, p⟩, _ | ⟨y, ys⟩⟩
    · cases hmember
    · exact reach_of_dispatchWith_leaf_compiled_logs hmember hp run
    · simp only [List.length_cons] at hlen
      let all := (w, p) :: y :: ys
      let split := (all.length + 1) / 2
      have htakeLen : (all.take split).length ≤ n + 1 := by
        simp only [all, split, List.length_take, List.length_cons]
        omega
      have hdropLen : (all.drop split).length ≤ n + 1 := by
        simp only [all, split, List.length_drop, List.length_cons]
        omega
      obtain ⟨z, zs, hdrop⟩ : ∃ z zs, all.drop split = z :: zs := by
        rcases hd : all.drop split with _ | ⟨z, zs⟩
        · exfalso
          have hl := congrArg List.length hd
          simp only [all, split, List.length_drop, List.length_cons,
            List.length_nil] at hl
          omega
        · exact ⟨z, zs, rfl⟩
      have hsortedSplit :
          DispatchTree.sorted (all.take split ++ all.drop split) = true := by
        rw [List.take_append_drop]
        exact hsorted
      have hsortedTake := DispatchTree.sorted_append_left hsortedSplit
      have hsortedDrop := DispatchTree.sorted_append_right hsortedSplit
      have hmemberSplit :
          (sig, body) ∈ all.take split ∨
            (sig, body) ∈ all.drop split := by
        apply List.mem_append.mp
        rw [List.take_append_drop]
        exact hmember
      change Func.RunCompiledTo fs sevm s
        ([dup 0, pushB256 (leftmostFsig (DispatchTree.build n
            (all.drop split))), gt] +++
          (dispatchWith k (DispatchTree.build n (all.take split)) <?>
            dispatchWith k (DispatchTree.build n (all.drop split)))) out at run
      obtain ⟨branchPre, testRun, branchRun⟩ :=
        runCompiledTo_prepend_inv run
      have ptest :
          (leftmostFsig (DispatchTree.build n (all.drop split)) >? sig) ::
            sig :: tail <<+ branchPre.stack := by
        generalize_line_prefix
      rw [hdrop, DispatchTree.leftmostFsig_build] at ptest
      rcases runCompiledTo_branch_inv branchRun with hzero | hsucc
      · rcases hzero with ⟨rightPre, -, hpop, rightRun⟩
        have popped := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) ptest
        have hle : z.fst ≤ sig := by
          rw [← B256.not_lt]
          intro hlt
          have hgt : z.fst > sig := hlt
          rw [B256.gtCheck, if_pos hgt] at popped
          exact B256.zero_ne_one popped.1
        have hmemberDrop : (sig, body) ∈ all.drop split := by
          rcases hmemberSplit with hin | hin
          · exfalso
            have hz : z ∈ all.drop split := by
              rw [hdrop]
              exact List.mem_cons_self ..
            have hlt :=
              DispatchTree.fst_lt_of_sorted_append hsortedSplit hin hz
            have h1 : sig.toNat < z.fst.toNat := B256.toNat_lt_toNat hlt
            have h2 : z.fst.toNat ≤ sig.toNat := B256.toNat_le_toNat hle
            omega
          · exact hin
        rcases ih hsortedDrop hdropLen hmemberDrop popped.2 rightRun with
          ⟨bodyPre, bodyStack, bodyState, bodyMemory, bodyLogs,
            bodyOutput, bodyRun⟩
        refine ⟨bodyPre, bodyStack, ?_, ?_, ?_, ?_, bodyRun⟩
        · exact (Line.of_inv Devm.state (by line_inv) testRun).trans
            (hpop.state.trans bodyState)
        · exact (Line.of_inv Devm.memory (by line_inv) testRun).trans
            (hpop.memory.trans bodyMemory)
        · exact (Line.of_inv Devm.logs (by line_inv) testRun).trans
            (hpop.logs.trans bodyLogs)
        · exact (Line.of_inv Devm.output (by line_inv) testRun).trans
            (hpop.output.trans bodyOutput)
      · rcases hsucc with ⟨flag, leftPre, hflag, -, hpop, leftRun⟩
        have popped := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) ptest
        have hlt : sig < z.fst := by
          by_contra hnlt
          rw [B256.gtCheck, if_neg (fun hgt => hnlt hgt)] at popped
          exact hflag popped.1
        have hmemberTake : (sig, body) ∈ all.take split := by
          rcases hmemberSplit with hin | hin
          · exact hin
          · exfalso
            rw [hdrop] at hin
            have hsortedZ : DispatchTree.sorted (z :: zs) = true := by
              rw [← hdrop]
              exact hsortedDrop
            have hle := DispatchTree.fst_le_of_sorted_mem hsortedZ hin
            have h1 : z.fst.toNat ≤ sig.toNat := B256.toNat_le_toNat hle
            have h2 : sig.toNat < z.fst.toNat := B256.toNat_lt_toNat hlt
            omega
        rcases ih hsortedTake htakeLen hmemberTake popped.2 leftRun with
          ⟨bodyPre, bodyStack, bodyState, bodyMemory, bodyLogs,
            bodyOutput, bodyRun⟩
        refine ⟨bodyPre, bodyStack, ?_, ?_, ?_, ?_, bodyRun⟩
        · exact (Line.of_inv Devm.state (by line_inv) testRun).trans
            (hpop.state.trans bodyState)
        · exact (Line.of_inv Devm.memory (by line_inv) testRun).trans
            (hpop.memory.trans bodyMemory)
        · exact (Line.of_inv Devm.logs (by line_inv) testRun).trans
            (hpop.logs.trans bodyLogs)
        · exact (Line.of_inv Devm.output (by line_inv) testRun).trans
            (hpop.output.trans bodyOutput)

private theorem reach_of_dispatchWith_compiled_logs
    {entries : List (B256 × Func)} {sig : B256} {body : Func}
    {fs : List Func} {k : Nat} {sevm : Sevm} {s : Devm}
    {out : Execution} {tail : Stack}
    (hsorted : DispatchTree.sorted entries = true)
    (hmember : (sig, body) ∈ entries)
    (hp : sig :: tail <<+ s.stack)
    (run : Func.RunCompiledTo fs sevm s
      (dispatchWith k (DispatchTree.ofSorted entries)) out) :
    ∃ bodyPre,
      tail <<+ bodyPre.stack ∧ s.state = bodyPre.state ∧
      s.memory = bodyPre.memory ∧ s.logs = bodyPre.logs ∧
      s.output = bodyPre.output ∧
      Func.RunCompiledTo fs sevm bodyPre body out :=
  reach_of_dispatchWith_build_compiled_logs hsorted (Nat.le_succ _)
    hmember hp run

/-- Gas-exact counterpart of the successful nonpayable-frame inversion. -/
private theorem run_body_of_run_nonpayable_compiled_frame_logs
    {fs : List Func} {sevm : Sevm} {s r : Devm} {body : Func}
    (run : Func.RunCompiledTo fs sevm s (nonpayable body) (.ok r)) :
    ∃ bodyPre,
      sevm.value = 0 ∧ s.state = bodyPre.state ∧
      s.memory = bodyPre.memory ∧ s.logs = bodyPre.logs ∧
      s.output = bodyPre.output ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok r) := by
  have hvalue : sevm.value = 0 :=
    value_eq_zero_of_run_nonpayable
      (Func.Run.of_runCompiled
        (Func.RunCompiled.of_runCompiledTo_ok run))
  unfold nonpayable at run
  obtain ⟨afterValue, qvalue, run⟩ := runCompiledTo_next_inv run
  obtain ⟨testPre, qzero, branchRun⟩ := runCompiledTo_next_inv run
  have rvalue := Ninst.Run.of_runCompiled qvalue
  have rzero := Ninst.Run.of_runCompiled qzero
  have pvalue : [sevm.value] <<+ afterValue.stack :=
    prefix_of_push (of_run_callvalue rvalue) nil_pref
  have ptest : (1 : B256) :: [] <<+ testPre.stack := by
    have p := prefix_of_iszero rzero pvalue
    simpa [hvalue, B256.eqCheck] using p
  obtain ⟨bodyPre, branchWord, -, hpop, bodyRun, -⟩ :=
    Func.RunCompiledTo.succ_branch_of_prefix
      (by decide : (1 : B256) ≠ 0) ptest branchRun
  refine ⟨bodyPre, hvalue, ?_, ?_, ?_, ?_, bodyRun⟩
  · exact (Ninst.Hinv.inv (f := Devm.state) rvalue).trans
      ((Ninst.Hinv.inv (f := Devm.state) rzero).trans hpop.state)
  · exact (Ninst.Hinv.inv (f := Devm.memory) rvalue).trans
      ((Ninst.Hinv.inv (f := Devm.memory) rzero).trans hpop.memory)
  · exact (of_run_callvalue rvalue).logs.trans
      ((Ninst.Hinv.inv (f := Devm.logs) rzero).trans hpop.logs)
  · exact (of_run_callvalue rvalue).output.trans
      ((Ninst.Hinv.inv (f := Devm.output) rzero).trans hpop.output)

/-- Gas-exact counterpart of the successful static-head inversion. -/
private theorem run_body_of_run_requireStaticArgs_compiled_frame_logs
    {fs : List Func} {sevm : Sevm} {s r : Devm}
    {words : Nat} {body : Func}
    (run : Func.RunCompiledTo fs sevm s
      (requireStaticArgs words body) (.ok r)) :
    ∃ bodyPre,
      B256.ltCheck sevm.data.length.toB256
          (Nat.toB256 (4 + 32 * words)) = 0 ∧
      s.state = bodyPre.state ∧ s.memory = bodyPre.memory ∧
      s.logs = bodyPre.logs ∧ s.output = bodyPre.output ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok r) := by
  unfold requireStaticArgs at run
  change Func.RunCompiledTo fs sevm s
    ([pushB256 (Nat.toB256 (4 + 32 * words)), calldatasize, lt] +++
      (Func.revert <?> body)) (.ok r) at run
  obtain ⟨testPre, testRun, branchRun⟩ := runCompiledTo_prepend_inv run
  rcases Line.of_run_cons testRun with ⟨afterWord, qword, testRun⟩
  rcases Line.of_run_cons testRun with ⟨afterSize, qsize, testRun⟩
  rcases Line.of_run_cons testRun with ⟨afterTest, qlt, hnil⟩
  cases hnil
  have p1 : [Nat.toB256 (4 + 32 * words)] <<+ afterWord.stack :=
    prefix_of_push (of_run_pushB256 qword) nil_pref
  have p2 : [sevm.data.length.toB256,
      Nat.toB256 (4 + 32 * words)] <<+ afterSize.stack :=
    prefix_of_push (of_run_calldatasize qsize) p1
  have p3 : [B256.ltCheck sevm.data.length.toB256
      (Nat.toB256 (4 + 32 * words))] <<+ testPre.stack :=
    prefix_of_lt qlt p2
  rcases runCompiledTo_branch_inv branchRun with hzero | hsucc
  · rcases hzero with ⟨bodyPre, -, hpop, bodyRun⟩
    have popped := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) p3
    refine ⟨bodyPre, popped.1.symm, ?_, ?_, ?_, ?_, bodyRun⟩
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
  · rcases hsucc with ⟨flag, revertPre, -, -, -, revertRun⟩
    rcases runCompiledTo_revert_inv revertRun with ⟨revertPost, hbad, -⟩
    simp at hbad

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

/-! ## Gas-exact selector and body entry -/

/-- The gas-exact compiled vault execution reaches its exact routed endpoint.
Unlike the loose compatibility theorem above, this retains the
`Func.RunCompiledTo` suffix needed to identify external child occurrences. -/
theorem runCompiled_enters_endpoint_compiled_logs
    {sevm : Sevm} {pre post : Devm} {sig : B256}
    {words : Nat} {body : Func}
    (run : Prog.RunCompiled sevm pre vault post)
    (hselector : Sevm.selector sevm = sig)
    (hmember : (sig, routed words body) ∈ vaultFuncs) :
    ∃ endpointPre,
      pre.state = endpointPre.state ∧ pre.memory = endpointPre.memory ∧
      pre.logs = endpointPre.logs ∧ pre.output = endpointPre.output ∧
      Func.RunCompiledTo (vault.main :: vault.aux) sevm endpointPre
        (endpoint words body) (.ok post) := by
  rcases run with ⟨rootPre, rootBurn, rootRun⟩
  have mainRun :
      Func.RunCompiledTo (vault.main :: vault.aux) sevm rootPre
        (fsig +++ dispatchWith revertSlot vaultTree) (.ok post) := by
    simpa only [vault, Func.mainWith] using
      (Func.RunCompiledTo.of_runCompiled rootRun)
  obtain ⟨dispatchPre, hfsig, hdispatch⟩ :=
    runCompiledTo_prepend_inv mainRun
  have selectorPrefix : sig :: [] <<+ dispatchPre.stack := by
    rw [← hselector]
    exact prefix_of_fsig nil_pref hfsig
  rcases reach_of_dispatchWith_compiled_logs vaultFuncs_sorted hmember
      selectorPrefix hdispatch with
    ⟨selectedPre, -, dispatchState, dispatchMemory, dispatchLogs,
      dispatchOutput, selectedRun⟩
  refine ⟨selectedPre, ?_, ?_, ?_, ?_, ?_⟩
  · exact rootBurn.state.trans
      ((Line.of_inv Devm.state (by line_inv) hfsig).trans dispatchState)
  · exact rootBurn.memory.trans
      ((Line.of_inv Devm.memory (by line_inv) hfsig).trans dispatchMemory)
  · exact rootBurn.logs.trans ((fsig_logs hfsig).trans dispatchLogs)
  · exact rootBurn.output.trans ((fsig_output hfsig).trans dispatchOutput)
  · simpa only [routed] using selectedRun

/-- Gas-exact successful entry to the actual vault endpoint body.  The result
simultaneously retains child-occurrence evidence and derives the shared ABI
guards from the run itself. -/
theorem runCompiled_enters_body_compiled_logs
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
      Func.RunCompiledTo (vault.main :: vault.aux) sevm bodyPre body
        (.ok post) := by
  rcases runCompiled_enters_endpoint_compiled_logs run hselector hmember with
    ⟨endpointPre, endpointState, endpointMemory, endpointLogs,
      endpointOutput, endpointRun⟩
  unfold endpoint at endpointRun
  rcases run_body_of_run_nonpayable_compiled_frame_logs endpointRun with
    ⟨staticPre, hvalue, wrapperState, wrapperMemory, wrapperLogs,
      wrapperOutput, staticRun⟩
  rcases run_body_of_run_requireStaticArgs_compiled_frame_logs staticRun with
    ⟨bodyPre, hguard, staticState, staticMemory, staticLogs,
      staticOutput, bodyRun⟩
  exact ⟨bodyPre, hvalue, hguard,
    endpointState.trans (wrapperState.trans staticState),
    endpointMemory.trans (wrapperMemory.trans staticMemory),
    endpointLogs.trans (wrapperLogs.trans staticLogs),
    endpointOutput.trans (wrapperOutput.trans staticOutput), bodyRun⟩

end ProrataWethVault

end Blanc
