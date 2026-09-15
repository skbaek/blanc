-- DripFunctional.lean : DRIP's source-level ingress classification.
--
-- One successful DRIP call is either the empty-calldata receive, which moves
-- no observable but the stack and gas, or one of the five frozen endpoints,
-- reached with its selector removed and its frame intact.  Nothing else can
-- succeed: an unrecognized selector meets the dispatcher's inline revert, a
-- recognized selector with the wrong calldata length meets its exact-length
-- guard, and a value-bearing call to any endpoint but `join()` meets the
-- shared nonpayable guard.  Those three are stated here as the absence of a
-- successful run, which is what `Func.Run` says.

import Blanc.DripEndpoints
import Blanc.DripIngress
import Blanc.Ladder
import Blanc.MessageExecution

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Drip

/-- The installed runtime bytes are exactly the compiled DRIP program. -/
theorem installed_compile {sevm : Sevm} (h_code : sevm.code.toList = code) :
    some sevm.code.toList = Prog.compile runtime := by
  rw [h_code, code_compile]

/-! ## Guard inversions

`exactCalldata` and the shared `nonpayable` wrapper are the only two guards a
DRIP endpoint crosses before its own body.  Both are stated as inversions: a
*successful* run forces the guard's condition, because the rejecting arm is
`Func.revert` and has no successful run at all. -/

/-- A successful run through an exact-length guard forces the frozen calldata
size and leaves world state, memory, logs and output untouched. -/
theorem of_run_exactCalldata {fs : List Func} {sevm : Sevm} {s r : Devm}
    {size : B256} {body : Func}
    (run : Func.Run fs sevm s (exactCalldata size body) r) :
    ∃ mid, sevm.data.length.toB256 = size ∧
      s.state = mid.state ∧ s.memory = mid.memory ∧
      s.logs = mid.logs ∧ s.output = mid.output ∧
      Func.Run fs sevm mid body r := by
  unfold exactCalldata at run
  refine run_prepend_elim _ [pushB256 size, calldatasize, eq] ?_ run
  intro s1 hline hbranch
  have hframe := hline
  rcases Line.of_run_cons hline with ⟨a, hpush, htail⟩
  rcases Line.of_run_cons htail with ⟨b, hsize, htail⟩
  rcases Line.of_run_cons htail with ⟨c, heq, hnil⟩
  cases hnil
  have hp0 : size :: [] <<+ a.stack :=
    prefix_of_push (of_run_pushB256 hpush) nil_pref
  have hp1 : sevm.data.length.toB256 :: size :: [] <<+ b.stack :=
    prefix_of_push (of_run_calldatasize hsize) hp0
  have hp2 : (sevm.data.length.toB256 =? size) :: [] <<+ s1.stack :=
    prefix_of_eq heq hp1
  rcases of_run_branch hbranch with
    ⟨u, hpop, hrev⟩ | ⟨w, u, v, hnz, hpop, hburn, hbody⟩
  · exact absurd hrev not_run_revert
  · have hw : w = (sevm.data.length.toB256 =? size) :=
      (popBurn_pref hpop hp2).1
    have hsize' : sevm.data.length.toB256 = size := by
      by_cases h : sevm.data.length.toB256 = size
      · exact h
      · exact absurd (by rw [hw, B256.eqCheck, if_neg h]) hnz
    exact ⟨v, hsize',
      (Line.of_inv Devm.state (by line_inv) hframe).trans
        (hpop.state.trans hburn.state),
      (Line.of_inv Devm.memory (by line_inv) hframe).trans
        (hpop.memory.trans hburn.memory),
      (Line.of_inv Devm.logs (by line_inv) hframe).trans
        (hpop.logs.trans hburn.logs),
      (Line.of_inv Devm.output (by line_inv) hframe).trans
        (hpop.output.trans hburn.output),
      hbody⟩

/-- The four nonpayable endpoints: a successful run forces zero call value and
the frozen calldata size together. -/
theorem of_run_nonpayable_exactCalldata {fs : List Func} {sevm : Sevm}
    {s r : Devm} {size : B256} {body : Func}
    (run : Func.Run fs sevm s (nonpayable (exactCalldata size body)) r) :
    ∃ mid, sevm.value = 0 ∧ sevm.data.length.toB256 = size ∧
      s.state = mid.state ∧ s.memory = mid.memory ∧
      s.logs = mid.logs ∧ s.output = mid.output ∧
      Func.Run fs sevm mid body r := by
  rcases run_body_of_run_nonpayable_logs run with
    ⟨t, hvalue, hst, hmm, hlg, hou, hguarded⟩
  rcases of_run_exactCalldata hguarded with
    ⟨mid, hsize, hst', hmm', hlg', hou', hbody⟩
  exact ⟨mid, hvalue, hsize, hst.trans hst', hmm.trans hmm',
    hlg.trans hlg', hou.trans hou', hbody⟩

/-! ## Ingress classification -/

/-- Empty calldata is the receive route: the run reaches the runtime's
top-level `STOP` and moves no observable but the stack and gas. -/
theorem main_receive {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre main post)
    (hempty : sevm.data.length.toB256 = 0) :
    pre.state = post.state ∧ pre.memory = post.memory ∧
      pre.logs = post.logs ∧ pre.output = post.output := by
  unfold main at run
  refine run_prepend_elim _ [calldatasize] ?_ run
  intro s1 hline hbranch
  have hframe := hline
  rcases Line.of_run_cons hline with ⟨a, hsize, hnil⟩
  cases hnil
  have hp : sevm.data.length.toB256 :: [] <<+ s1.stack :=
    prefix_of_push (of_run_calldatasize hsize) nil_pref
  rcases of_run_branch hbranch with
    ⟨u, hpop, hstop⟩ | ⟨w, u, v, hnz, hpop, hburn, hmain⟩
  · have hu : u = post := by
      cases hstop with
      | last hrun => exact Except.ok.inj hrun
    subst hu
    exact ⟨(Line.of_inv Devm.state (by line_inv) hframe).trans hpop.state,
      (Line.of_inv Devm.memory (by line_inv) hframe).trans hpop.memory,
      (Line.of_inv Devm.logs (by line_inv) hframe).trans hpop.logs,
      (Line.of_inv Devm.output (by line_inv) hframe).trans hpop.output⟩
  · exact absurd ((popBurn_pref hpop hp).1.trans hempty) hnz

/-- Nonempty calldata reaches the shared dispatcher with the frame intact and
the selector alone on the stack. -/
private theorem dispatch_entry_of_run_main {fs : List Func} {sevm : Sevm}
    {pre post : Devm}
    (run : Func.Run fs sevm pre main post)
    (hnonempty : sevm.data.length.toB256 ≠ 0) :
    ∃ entry, pre.state = entry.state ∧ pre.memory = entry.memory ∧
      pre.logs = entry.logs ∧ pre.output = entry.output ∧
      (Sevm.selector sevm :: [] <<+ entry.stack) ∧
      Func.Run fs sevm entry (dispatch tree) post := by
  unfold main at run
  refine run_prepend_elim _ [calldatasize] ?_ run
  intro s1 hline hbranch
  have hframe := hline
  rcases Line.of_run_cons hline with ⟨a, hsize, hnil⟩
  cases hnil
  have hp : sevm.data.length.toB256 :: [] <<+ s1.stack :=
    prefix_of_push (of_run_calldatasize hsize) nil_pref
  rcases of_run_branch hbranch with
    ⟨u, hpop, hstop⟩ | ⟨w, u, v, hnz, hpop, hburn, hmain⟩
  · exact absurd (popBurn_pref hpop hp).1.symm hnonempty
  · refine run_prepend_elim _ fsig ?_ hmain
    intro s2 hfsig hdispatch
    refine ⟨s2, ?_, ?_, ?_, ?_, ?_, hdispatch⟩
    · exact (Line.of_inv Devm.state (by line_inv) hframe).trans
        (hpop.state.trans (hburn.state.trans
          (Line.of_inv Devm.state (by line_inv) hfsig)))
    · exact (Line.of_inv Devm.memory (by line_inv) hframe).trans
        (hpop.memory.trans (hburn.memory.trans
          (Line.of_inv Devm.memory (by line_inv) hfsig)))
    · exact (Line.of_inv Devm.logs (by line_inv) hframe).trans
        (hpop.logs.trans (hburn.logs.trans (fsig_logs hfsig)))
    · exact (Line.of_inv Devm.output (by line_inv) hframe).trans
        (hpop.output.trans (hburn.output.trans (fsig_output hfsig)))
    · exact prefix_of_fsig nil_pref hfsig

/-- A successful nonempty call reaches the frozen endpoint its selector names,
with the selector removed and the frame intact. -/
theorem main_body {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {sig : B256} {f : Func}
    (run : Func.Run fs sevm pre main post)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hsel : Sevm.selector sevm = sig)
    (hmem : (sig, f) ∈ funcs) :
    ∃ entry, pre.state = entry.state ∧ pre.memory = entry.memory ∧
      pre.logs = entry.logs ∧ pre.output = entry.output ∧
      Func.Run fs sevm entry f post := by
  rcases dispatch_entry_of_run_main run hnonempty with
    ⟨s2, hst, hmm, hlg, hou, hpfx, hdispatch⟩
  rw [hsel] at hpfx
  rcases reach_of_dispatch_logs funcs_sorted hmem hpfx hdispatch with
    ⟨entry, -, hst', hmm', hlg', hou', hbody⟩
  exact ⟨entry, hst.trans hst', hmm.trans hmm', hlg.trans hlg',
    hou.trans hou', hbody⟩

/-- **The selector census is exhaustive.** A successful nonempty call carries
one of the five frozen selectors; every other selector reaches the
dispatcher's inline revert, which has no successful run. -/
theorem main_selector_mem {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre main post)
    (hnonempty : sevm.data.length.toB256 ≠ 0) :
    Sevm.selector sevm ∈ selectors := by
  by_contra hmiss
  rcases dispatch_entry_of_run_main run hnonempty with
    ⟨s2, -, -, -, -, hpfx, hdispatch⟩
  have htree : ∀ body : Func, (Sevm.selector sevm, body) ∉ tree := by
    intro body hbody
    exact hmiss ((tree_hasSelector_iff (Sevm.selector sevm)).1 ⟨body, hbody⟩)
  exact not_run_dispatch_of_miss htree hpfx hdispatch

/-! ## The same classification at deployed-byte altitude -/

/-- Every successful execution of the deployed DRIP runtime factors through a
successful source run of its main program, at a state the entry `JUMPDEST`
burn leaves observationally identical. -/
theorem run_main_of_exec {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code) :
    ∃ entry, pre.state = entry.state ∧ pre.memory = entry.memory ∧
      pre.logs = entry.logs ∧ pre.output = entry.output ∧
      Func.Run (runtime.main :: runtime.aux) sevm entry main post := by
  have hrun : Prog.Run sevm pre runtime post :=
    correct sevm pre runtime post exc (installed_compile hcode)
  dsimp only [Prog.Run] at hrun
  cases hrun
  rename (_ = _) => heq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => entry
  cases heq
  exact ⟨entry, burn.state, burn.memory, burn.logs, burn.output, run⟩

/-- Deployed-byte receive: an empty-calldata call to the installed runtime
leaves world state, memory, logs and output exactly as it found them. -/
theorem exec_receive {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hempty : sevm.data.length.toB256 = 0) :
    pre.state = post.state ∧ pre.memory = post.memory ∧
      pre.logs = post.logs ∧ pre.output = post.output := by
  rcases run_main_of_exec exc hcode with ⟨entry, hst, hmm, hlg, hou, run⟩
  rcases main_receive run hempty with ⟨hst', hmm', hlg', hou'⟩
  exact ⟨hst.trans hst', hmm.trans hmm', hlg.trans hlg', hou.trans hou'⟩

/-- Deployed-byte selector census: a successful nonempty call to the installed
runtime carries one of the five frozen selectors. -/
theorem exec_selector_mem {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hnonempty : sevm.data.length.toB256 ≠ 0) :
    Sevm.selector sevm ∈ selectors := by
  rcases run_main_of_exec exc hcode with ⟨entry, -, -, -, -, run⟩
  exact main_selector_mem run hnonempty

/-- Deployed-byte endpoint entry: a successful nonempty call reaches the frozen
entry its selector names. -/
theorem exec_enters_entry {sevm : Sevm} {pre post : Devm}
    {sig : B256} {f : Func}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = sig)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hmem : (sig, f) ∈ funcs) :
    ∃ entry, pre.state = entry.state ∧ pre.memory = entry.memory ∧
      pre.logs = entry.logs ∧ pre.output = entry.output ∧
      Func.Run (runtime.main :: runtime.aux) sevm entry f post := by
  rcases run_main_of_exec exc hcode with ⟨mid, hst, hmm, hlg, hou, run⟩
  rcases main_body run hnonempty hsel hmem with
    ⟨entry, hst', hmm', hlg', hou', hbody⟩
  exact ⟨entry, hst.trans hst', hmm.trans hmm', hlg.trans hlg',
    hou.trans hou', hbody⟩

/-! ## The five endpoints, with their guards discharged

Each theorem states what a *successful* deployed call on that selector forces:
the frozen payability, the frozen exact calldata length, and entry into the
raw body with the frame intact.  A value-bearing call to a nonpayable entry,
or one with missing or trailing argument bytes, therefore has no successful
run at all. -/

private theorem entry_of_nonpayable_selector {sevm : Sevm} {pre post : Devm}
    {sig size : B256} {body : Func}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = sig)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hmem : (sig, nonpayable (exactCalldata size body)) ∈ funcs) :
    sevm.value = 0 ∧ sevm.data.length.toB256 = size ∧
      ∃ entry, pre.state = entry.state ∧ pre.memory = entry.memory ∧
        pre.logs = entry.logs ∧ pre.output = entry.output ∧
        Func.Run (runtime.main :: runtime.aux) sevm entry body post := by
  rcases exec_enters_entry exc hcode hsel hnonempty hmem with
    ⟨mid, hst, hmm, hlg, hou, hwrapped⟩
  rcases of_run_nonpayable_exactCalldata hwrapped with
    ⟨entry, hvalue, hsize, hst', hmm', hlg', hou', hbody⟩
  exact ⟨hvalue, hsize, entry, hst.trans hst', hmm.trans hmm',
    hlg.trans hlg', hou.trans hou', hbody⟩

theorem exec_enters_drip {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = dripSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0) :
    sevm.value = 0 ∧ sevm.data.length.toB256 = 4 ∧
      ∃ entry, pre.state = entry.state ∧ pre.memory = entry.memory ∧
        pre.logs = entry.logs ∧ pre.output = entry.output ∧
        Func.Run (runtime.main :: runtime.aux) sevm entry drip post :=
  entry_of_nonpayable_selector exc hcode hsel hnonempty
    (by simp [funcs])

theorem exec_enters_exit {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = exitSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0) :
    sevm.value = 0 ∧ sevm.data.length.toB256 = 36 ∧
      ∃ entry, pre.state = entry.state ∧ pre.memory = entry.memory ∧
        pre.logs = entry.logs ∧ pre.output = entry.output ∧
        Func.Run (runtime.main :: runtime.aux) sevm entry exit post :=
  entry_of_nonpayable_selector exc hcode hsel hnonempty
    (by simp [funcs])

theorem exec_enters_convertToAssets {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = convertToAssetsSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0) :
    sevm.value = 0 ∧ sevm.data.length.toB256 = 36 ∧
      ∃ entry, pre.state = entry.state ∧ pre.memory = entry.memory ∧
        pre.logs = entry.logs ∧ pre.output = entry.output ∧
        Func.Run (runtime.main :: runtime.aux) sevm entry convertToAssets post :=
  entry_of_nonpayable_selector exc hcode hsel hnonempty
    (by simp [funcs])

theorem exec_enters_convertToUnits {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = convertToUnitsSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0) :
    sevm.value = 0 ∧ sevm.data.length.toB256 = 36 ∧
      ∃ entry, pre.state = entry.state ∧ pre.memory = entry.memory ∧
        pre.logs = entry.logs ∧ pre.output = entry.output ∧
        Func.Run (runtime.main :: runtime.aux) sevm entry convertToUnits post :=
  entry_of_nonpayable_selector exc hcode hsel hnonempty
    (by simp [funcs])

/-- `join()` is the one payable entry, so its theorem forces only the frozen
exact calldata length. -/
theorem exec_enters_join {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = joinSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0) :
    sevm.data.length.toB256 = 4 ∧
      ∃ entry, pre.state = entry.state ∧ pre.memory = entry.memory ∧
        pre.logs = entry.logs ∧ pre.output = entry.output ∧
        Func.Run (runtime.main :: runtime.aux) sevm entry join post := by
  rcases exec_enters_entry exc hcode hsel hnonempty
      (show (joinSelector, exactCalldata 4 join) ∈ funcs by simp [funcs]) with
    ⟨mid, hst, hmm, hlg, hou, hwrapped⟩
  rcases of_run_exactCalldata hwrapped with
    ⟨entry, hsize, hst', hmm', hlg', hou', hbody⟩
  exact ⟨hsize, entry, hst.trans hst', hmm.trans hmm', hlg.trans hlg',
    hou.trans hou', hbody⟩

/-! ## Failure paths, ingress layer: absence of success

A value-bearing call to a nonpayable entry, a recognized selector with the
wrong calldata length, and an unrecognized selector can never end `.ok`:
each contradicts a guard the corresponding `exec_enters_*` theorem (or the
selector census) forces on every successful deployed call.  (`Exec` is data,
not a `Prop`, so absence is stated as a universal over derivations.) -/

theorem no_exec_success_of_drip_value_or_length {sevm : Sevm} {pre : Devm}
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = dripSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hbad : sevm.value ≠ 0 ∨ sevm.data.length.toB256 ≠ 4)
    (post : Devm) (exc : Exec 0 sevm pre (.ok post)) : False := by
  rcases exec_enters_drip exc hcode hsel hnonempty with ⟨hvalue, hsize, -⟩
  rcases hbad with h | h
  · exact h hvalue
  · exact h hsize

theorem no_exec_success_of_exit_value_or_length {sevm : Sevm} {pre : Devm}
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = exitSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hbad : sevm.value ≠ 0 ∨ sevm.data.length.toB256 ≠ 36)
    (post : Devm) (exc : Exec 0 sevm pre (.ok post)) : False := by
  rcases exec_enters_exit exc hcode hsel hnonempty with ⟨hvalue, hsize, -⟩
  rcases hbad with h | h
  · exact h hvalue
  · exact h hsize

theorem no_exec_success_of_convertToAssets_value_or_length {sevm : Sevm}
    {pre : Devm}
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = convertToAssetsSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hbad : sevm.value ≠ 0 ∨ sevm.data.length.toB256 ≠ 36)
    (post : Devm) (exc : Exec 0 sevm pre (.ok post)) : False := by
  rcases exec_enters_convertToAssets exc hcode hsel hnonempty with
    ⟨hvalue, hsize, -⟩
  rcases hbad with h | h
  · exact h hvalue
  · exact h hsize

theorem no_exec_success_of_convertToUnits_value_or_length {sevm : Sevm}
    {pre : Devm}
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = convertToUnitsSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hbad : sevm.value ≠ 0 ∨ sevm.data.length.toB256 ≠ 36)
    (post : Devm) (exc : Exec 0 sevm pre (.ok post)) : False := by
  rcases exec_enters_convertToUnits exc hcode hsel hnonempty with
    ⟨hvalue, hsize, -⟩
  rcases hbad with h | h
  · exact h hvalue
  · exact h hsize

/-- `join()` is payable, so only a wrong calldata length rules out success. -/
theorem no_exec_success_of_join_length {sevm : Sevm} {pre : Devm}
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = joinSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hbad : sevm.data.length.toB256 ≠ 4)
    (post : Devm) (exc : Exec 0 sevm pre (.ok post)) : False := by
  rcases exec_enters_join exc hcode hsel hnonempty with ⟨hsize, -⟩
  exact hbad hsize

/-- An unrecognized selector never ends `.ok`, at any nonempty length. -/
theorem no_exec_success_of_unknown_selector {sevm : Sevm} {pre : Devm}
    (hcode : sevm.code.toList = code)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hmiss : Sevm.selector sevm ∉ selectors)
    (post : Devm) (exc : Exec 0 sevm pre (.ok post)) : False :=
  hmiss (exec_selector_mem exc hcode hnonempty)

/-! ## Whole-call rollback at `Exec` altitude

Any execution of the installed runtime that ends `.error` — a guard revert,
a failed child, or a halt — retains no storage write and commits no frame.
The installed-code premise scopes these absorbers to DRIP's boundary; the
proofs themselves are the shared settlement substrate's rollback-first route
(`Execution.commits (.error _) = false`), so every failure path below
inherits rollback without re-walking it. -/

theorem drip_exec_error_noRetainedWriteTo {sevm : Sevm} {pre : Devm} {err}
    (exc : Exec 0 sevm pre (.error err))
    (_hcode : sevm.code.toList = code)
    (owner : Adr) (key : B256) :
    Exec.NoRetainedWriteTo exc owner key :=
  exc.noRetainedWriteTo_of_not_commits (by simp [Execution.commits]) owner key

theorem drip_exec_error_retainedWrites_nil {sevm : Sevm} {pre : Devm} {err}
    (exc : Exec 0 sevm pre (.error err))
    (_hcode : sevm.code.toList = code) :
    Exec.retainedStorageWrites exc = [] := by
  have hnc : Execution.commits (.error err) ≠ true := by
    simp [Execution.commits]
  have hnodes := Exec.retainedNodes_eq_nil_of_not_commits exc hnc
  simp [Exec.retainedStorageWrites, hnodes]

theorem drip_exec_error_retainedTriples_nil {sevm : Sevm} {pre : Devm} {err}
    (exc : Exec 0 sevm pre (.error err))
    (hcode : sevm.code.toList = code) :
    Exec.retainedStorageEffectTriples exc = [] := by
  have hwrites := drip_exec_error_retainedWrites_nil exc hcode
  simp [Exec.retainedStorageEffectTriples, hwrites]

theorem drip_exec_error_committedFrames_nil {sevm : Sevm} {pre : Devm} {err}
    (exc : Exec 0 sevm pre (.error err))
    (_hcode : sevm.code.toList = code) :
    Exec.committedFrames exc = [] := by
  apply Exec.committedFrames_eq_nil_of_not_commits
  simp [Execution.commits]

/-! ## Failure paths, deep guards: surface and machine-guard absence

A successful deployed call on a recognized selector with the right length and
payability still has to cross that endpoint's surface caps and the shared
machine's guards. Each theorem below says one violated guard rules out
success. The endpoint inversions need a machine `Frame` at the endpoint body,
built from the canonical-entry hypothesis (`pre.memory = Mem.empty`, true of
every real frame via `initDevm`) transported along the dispatcher's memory
equation; the stack tail is empty (`nil_pref`). -/

private theorem entryFrame_of_canonical {pre entry : Devm}
    (hmm : pre.memory = entry.memory) (hcanon : pre.memory = Mem.empty) :
    Frame [] entry entry := by
  have hmem : entry.memory = Mem.empty := by rw [← hmm, hcanon]
  exact ⟨by rw [hmem]; exact Mem.wf_empty,
    by rw [hmem]; exact Mem.reads_empty, rfl, rfl⟩

private theorem getStorVal_entry_of_pre {sevm : Sevm} {pre entry : Devm}
    (hst : pre.state = entry.state) (k : B256) :
    Devm.getStorVal entry sevm.currentTarget k =
      Devm.getStorVal pre sevm.currentTarget k :=
  Devm.getStorVal_of_state hst.symm sevm.currentTarget k

theorem no_exec_success_of_drip_machine_guards {sevm : Sevm} {pre : Devm}
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = dripSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty)
    (hbad : Devm.getStorVal pre sevm.currentTarget chiSlot < scale ∨
      maxChi < Devm.getStorVal pre sevm.currentTarget chiSlot ∨
      sevm.benvStat.time < Devm.getStorVal pre sevm.currentTarget rhoSlot ∨
      maxElapsed <
        sevm.benvStat.time - Devm.getStorVal pre sevm.currentTarget rhoSlot ∨
      ¬ B256.RPowGuards scale half rate
        (sevm.benvStat.time -
          Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat ∨
      ¬ B256.Nofm (Devm.getStorVal pre sevm.currentTarget chiSlot)
        (B256.rpow scale half rate
          (sevm.benvStat.time -
            Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat) ∨
      maxChi <
        (B256.rpow scale half rate
              (sevm.benvStat.time -
                Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat *
            Devm.getStorVal pre sevm.currentTarget chiSlot) / scale)
    (post : Devm) (exc : Exec 0 sevm pre (.ok post)) : False := by
  rcases exec_enters_drip exc hcode hsel hnonempty with
    ⟨-, -, entry, hst, hmm, -, -, hbody⟩
  have hframe := entryFrame_of_canonical hmm hcanon
  rcases of_run_drip auxLookup_runtime hframe nil_pref hbody with
    ⟨hlower, hupper, hclock, helapsed, hguards, hnofm, hcap, -, -⟩
  have hgv : ∀ k, Devm.getStorVal entry sevm.currentTarget k =
      Devm.getStorVal pre sevm.currentTarget k :=
    getStorVal_entry_of_pre hst
  simp only [hgv] at hlower hupper hclock helapsed hguards hnofm hcap
  rcases hbad with h|h|h|h|h|h|h
  · exact hlower h
  · exact hupper h
  · exact hclock h
  · exact helapsed h
  · exact h hguards
  · exact h hnofm
  · exact hcap h

theorem no_exec_success_of_exit_guards {sevm : Sevm} {pre : Devm}
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = exitSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty)
    (hbad : maxUnits < Sevm.dataWord sevm (32 * 0 + 4) ∨
      maxUnits < Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 ∨
      maxPie < Devm.getStorVal pre sevm.currentTarget totalUnitsSlot ∨
      Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 <
        Sevm.dataWord sevm (32 * 0 + 4) ∨
      Devm.getStorVal pre sevm.currentTarget totalUnitsSlot <
        Sevm.dataWord sevm (32 * 0 + 4) ∨
      Devm.getStorVal pre sevm.currentTarget chiSlot < scale ∨
      maxChi < Devm.getStorVal pre sevm.currentTarget chiSlot ∨
      sevm.benvStat.time < Devm.getStorVal pre sevm.currentTarget rhoSlot ∨
      maxElapsed <
        sevm.benvStat.time - Devm.getStorVal pre sevm.currentTarget rhoSlot ∨
      ¬ B256.RPowGuards scale half rate
        (sevm.benvStat.time -
          Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat)
    (post : Devm) (exc : Exec 0 sevm pre (.ok post)) : False := by
  rcases exec_enters_exit exc hcode hsel hnonempty with
    ⟨-, -, entry, hst, hmm, -, -, hbody⟩
  have hframe := entryFrame_of_canonical hmm hcanon
  rcases of_run_exit_settles auxLookup_runtime hframe nil_pref hbody with
    ⟨harg, hrow, htotal, hown, hfund, hlower, hupper, hclock, helapsed,
      hguards, -⟩
  have hgv : ∀ k, Devm.getStorVal entry sevm.currentTarget k =
      Devm.getStorVal pre sevm.currentTarget k :=
    getStorVal_entry_of_pre hst
  simp only [hgv] at harg hrow htotal hown hfund hlower hupper hclock helapsed hguards
  rcases hbad with h|h|h|h|h|h|h|h|h|h
  · exact harg h
  · exact hrow h
  · exact htotal h
  · exact hown h
  · exact hfund h
  · exact hlower h
  · exact hupper h
  · exact hclock h
  · exact helapsed h
  · exact h hguards

theorem no_exec_success_of_join_guards {sevm : Sevm} {pre : Devm}
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = joinSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty)
    (hbad : maxAsset < sevm.value ∨
      maxUnits < Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 ∨
      maxPie < Devm.getStorVal pre sevm.currentTarget totalUnitsSlot ∨
      Devm.getStorVal pre sevm.currentTarget chiSlot < scale ∨
      maxChi < Devm.getStorVal pre sevm.currentTarget chiSlot ∨
      sevm.benvStat.time < Devm.getStorVal pre sevm.currentTarget rhoSlot ∨
      maxElapsed <
        sevm.benvStat.time - Devm.getStorVal pre sevm.currentTarget rhoSlot ∨
      ¬ B256.RPowGuards scale half rate
        (sevm.benvStat.time -
          Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat ∨
      maxUnits <
        Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 +
          scale * sevm.value /
            ((B256.rpow scale half rate
                (sevm.benvStat.time -
                  Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat *
              Devm.getStorVal pre sevm.currentTarget chiSlot) / scale) ∨
      maxPie <
        scale * sevm.value /
            ((B256.rpow scale half rate
                (sevm.benvStat.time -
                  Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat *
              Devm.getStorVal pre sevm.currentTarget chiSlot) / scale) +
          Devm.getStorVal pre sevm.currentTarget totalUnitsSlot)
    (post : Devm) (exc : Exec 0 sevm pre (.ok post)) : False := by
  rcases exec_enters_join exc hcode hsel hnonempty with
    ⟨-, entry, hst, hmm, -, -, hbody⟩
  have hframe := entryFrame_of_canonical hmm hcanon
  rcases of_run_join auxLookup_runtime hframe nil_pref hbody with
    ⟨hasset, hrowPre, htotalPre, hlower, hupper, hclock, helapsed, hguards,
      freshChi, units, hfreshEq, hunitsEq, hrowPost, htotalPost, -, -⟩
  have hgv : ∀ k, Devm.getStorVal entry sevm.currentTarget k =
      Devm.getStorVal pre sevm.currentTarget k :=
    getStorVal_entry_of_pre hst
  simp only [hgv] at hasset hrowPre htotalPre hlower hupper hclock helapsed hguards hfreshEq hunitsEq hrowPost htotalPost
  rw [hunitsEq, hfreshEq] at hrowPost htotalPost
  rcases hbad with h|h|h|h|h|h|h|h|h|h
  · exact hasset h
  · exact hrowPre h
  · exact htotalPre h
  · exact hlower h
  · exact hupper h
  · exact hclock h
  · exact helapsed h
  · exact h hguards
  · exact hrowPost h
  · exact htotalPost h

theorem no_exec_success_of_convertToAssets_guards {sevm : Sevm} {pre : Devm}
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = convertToAssetsSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty)
    (hbad : maxUnits < Sevm.dataWord sevm (32 * 0 + 4) ∨
      Devm.getStorVal pre sevm.currentTarget chiSlot < scale ∨
      maxChi < Devm.getStorVal pre sevm.currentTarget chiSlot ∨
      sevm.benvStat.time < Devm.getStorVal pre sevm.currentTarget rhoSlot ∨
      maxElapsed <
        sevm.benvStat.time - Devm.getStorVal pre sevm.currentTarget rhoSlot ∨
      ¬ B256.RPowGuards scale half rate
        (sevm.benvStat.time -
          Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat)
    (post : Devm) (exc : Exec 0 sevm pre (.ok post)) : False := by
  rcases exec_enters_convertToAssets exc hcode hsel hnonempty with
    ⟨-, -, entry, hst, hmm, -, -, hbody⟩
  have hframe := entryFrame_of_canonical hmm hcanon
  rcases of_run_convertToAssets auxLookup_runtime hframe nil_pref hbody with
    ⟨hcap, hlower, hupper, hclock, helapsed, hguards, -, -⟩
  have hgv : ∀ k, Devm.getStorVal entry sevm.currentTarget k =
      Devm.getStorVal pre sevm.currentTarget k :=
    getStorVal_entry_of_pre hst
  simp only [hgv] at hcap hlower hupper hclock helapsed hguards
  rcases hbad with h|h|h|h|h|h
  · exact hcap h
  · exact hlower h
  · exact hupper h
  · exact hclock h
  · exact helapsed h
  · exact h hguards

theorem no_exec_success_of_convertToUnits_guards {sevm : Sevm} {pre : Devm}
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = convertToUnitsSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty)
    (hbad : maxAsset < Sevm.dataWord sevm (32 * 0 + 4) ∨
      Devm.getStorVal pre sevm.currentTarget chiSlot < scale ∨
      maxChi < Devm.getStorVal pre sevm.currentTarget chiSlot ∨
      sevm.benvStat.time < Devm.getStorVal pre sevm.currentTarget rhoSlot ∨
      maxElapsed <
        sevm.benvStat.time - Devm.getStorVal pre sevm.currentTarget rhoSlot ∨
      ¬ B256.RPowGuards scale half rate
        (sevm.benvStat.time -
          Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat)
    (post : Devm) (exc : Exec 0 sevm pre (.ok post)) : False := by
  rcases exec_enters_convertToUnits exc hcode hsel hnonempty with
    ⟨-, -, entry, hst, hmm, -, -, hbody⟩
  have hframe := entryFrame_of_canonical hmm hcanon
  rcases of_run_convertToUnits auxLookup_runtime hframe nil_pref hbody with
    ⟨hcap, hlower, hupper, hclock, helapsed, hguards, -, -⟩
  have hgv : ∀ k, Devm.getStorVal entry sevm.currentTarget k =
      Devm.getStorVal pre sevm.currentTarget k :=
    getStorVal_entry_of_pre hst
  simp only [hgv] at hcap hlower hupper hclock helapsed hguards
  rcases hbad with h|h|h|h|h|h
  · exact hcap h
  · exact hlower h
  · exact hupper h
  · exact hclock h
  · exact helapsed h
  · exact h hguards

/-! ## Failure paths, message altitude: settled-revert projections

A DRIP message that settles with an error rolls the world back to the
pre-state: state and transient storage come straight from
`ProcessMessage.rollback_of_error`, and the account projections follow.
Output and logs are raw-preserving (`settledRevert_output/_logs`), stated
here honestly as relations rather than emptiness: universal
raw-output-emptiness / logs-silence needs per-path occurrence work beyond
absence + rollback (the miss walk in `DripIngress` and the `Func.revert`
construction carry the per-path facts). -/

theorem drip_message_error_state {msg : Msg} {xl : Xlot} {out : Devm}
    (h : ProcessMessage msg xl (.ok out)) (herr : out.error.isSome)
    (_hcode : msg.code.toList = code) :
    out.state = msg.benv.state :=
  (ProcessMessage.rollback_of_error h herr).1

theorem drip_message_error_transient {msg : Msg} {xl : Xlot} {out : Devm}
    (h : ProcessMessage msg xl (.ok out)) (herr : out.error.isSome)
    (_hcode : msg.code.toList = code) :
    out.transientStorage = msg.tenv.transientStorage :=
  (ProcessMessage.rollback_of_error h herr).2

theorem drip_message_error_getStor {msg : Msg} {xl : Xlot} {out : Devm}
    (h : ProcessMessage msg xl (.ok out)) (herr : out.error.isSome)
    (_hcode : msg.code.toList = code) (a : Adr) :
    Devm.getStor out a = (msg.benv.state.get a).stor := by
  have hst := (ProcessMessage.rollback_of_error h herr).1
  unfold Devm.getStor Devm.getAcct
  rw [hst]

theorem drip_message_error_getBal {msg : Msg} {xl : Xlot} {out : Devm}
    (h : ProcessMessage msg xl (.ok out)) (herr : out.error.isSome)
    (_hcode : msg.code.toList = code) (a : Adr) :
    Devm.getBal out a = (msg.benv.state.get a).bal := by
  have hst := (ProcessMessage.rollback_of_error h herr).1
  unfold Devm.getBal Devm.getAcct
  rw [hst]

theorem drip_message_error_getCode {msg : Msg} {xl : Xlot} {out : Devm}
    (h : ProcessMessage msg xl (.ok out)) (herr : out.error.isSome)
    (_hcode : msg.code.toList = code) (a : Adr) :
    Devm.getCode out a = (msg.benv.state.get a).code := by
  have hst := (ProcessMessage.rollback_of_error h herr).1
  unfold Devm.getCode Devm.getAcct
  rw [hst]

theorem drip_settledRevert_projections (msg : Msg) (raw : Devm)
    (_hcode : msg.code.toList = code) :
    (MessageExecution.settledRevert msg raw).state = msg.benv.state ∧
      (MessageExecution.settledRevert msg raw).transientStorage =
        msg.tenv.transientStorage ∧
      (∀ a, Devm.getStor (MessageExecution.settledRevert msg raw) a =
        (msg.benv.state.get a).stor) ∧
      (∀ a, Devm.getBal (MessageExecution.settledRevert msg raw) a =
        (msg.benv.state.get a).bal) ∧
      (∀ a, Devm.getCode (MessageExecution.settledRevert msg raw) a =
        (msg.benv.state.get a).code) ∧
      (MessageExecution.settledRevert msg raw).output = raw.output ∧
      (MessageExecution.settledRevert msg raw).logs = raw.logs := by
  refine ⟨MessageExecution.settledRevert_state msg raw,
    MessageExecution.settledRevert_transientStorage msg raw, ?_, ?_, ?_,
    MessageExecution.settledRevert_output msg raw,
    MessageExecution.settledRevert_logs msg raw⟩
  · intro a
    unfold Devm.getStor Devm.getAcct
    rw [MessageExecution.settledRevert_state]
  · intro a
    unfold Devm.getBal Devm.getAcct
    rw [MessageExecution.settledRevert_state]
  · intro a
    unfold Devm.getCode Devm.getAcct
    rw [MessageExecution.settledRevert_state]

/-! ## Deployed-byte success-effect lifts

Each lift carries a G2 `of_run_*` success effect from the endpoint body to the
full deployed call: `exec_enters_*` supplies the body run with the frame
intact, the canonical-entry hypothesis builds the machine `Frame`, and the two
transport equations rewrite `entry` to `pre`. -/

/-- Deployed-byte `drip()`: a successful call settles the fresh index and the
timestamp into their frozen slots and returns the new index. -/
theorem drip_exec_effect {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = dripSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty) :
    ¬ Devm.getStorVal pre sevm.currentTarget chiSlot < scale ∧
      ¬ maxChi < Devm.getStorVal pre sevm.currentTarget chiSlot ∧
      ¬ sevm.benvStat.time < Devm.getStorVal pre sevm.currentTarget rhoSlot ∧
      ¬ maxElapsed <
        sevm.benvStat.time - Devm.getStorVal pre sevm.currentTarget rhoSlot ∧
      B256.RPowGuards scale half rate
        (sevm.benvStat.time -
          Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat ∧
      B256.Nofm (Devm.getStorVal pre sevm.currentTarget chiSlot)
        (B256.rpow scale half rate
          (sevm.benvStat.time -
            Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat) ∧
      ¬ maxChi <
        (B256.rpow scale half rate
              (sevm.benvStat.time -
                Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat *
            Devm.getStorVal pre sevm.currentTarget chiSlot) / scale ∧
      Devm.getStor post sevm.currentTarget =
        ((Devm.getStor pre sevm.currentTarget).set chiSlot
            ((B256.rpow scale half rate
                  (sevm.benvStat.time -
                    Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat *
                Devm.getStorVal pre sevm.currentTarget chiSlot) / scale)).set
          rhoSlot sevm.benvStat.time ∧
      ReturnsWord
        ((B256.rpow scale half rate
              (sevm.benvStat.time -
                Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat *
            Devm.getStorVal pre sevm.currentTarget chiSlot) / scale) post := by
  rcases exec_enters_drip exc hcode hsel hnonempty with
    ⟨-, -, entry, hst, hmm, -, -, hbody⟩
  have hframe := entryFrame_of_canonical hmm hcanon
  have heffect := of_run_drip auxLookup_runtime hframe nil_pref hbody
  have hgv : ∀ k, Devm.getStorVal entry sevm.currentTarget k =
      Devm.getStorVal pre sevm.currentTarget k :=
    getStorVal_entry_of_pre hst
  have hg : Devm.getStor entry sevm.currentTarget =
      Devm.getStor pre sevm.currentTarget :=
    getStor_eq_of_state_eq hst.symm sevm.currentTarget
  simp only [hgv, hg] at heffect
  exact heffect

end Drip

end Blanc
