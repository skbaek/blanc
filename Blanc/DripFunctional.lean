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

import Blanc.DripIngress
import Blanc.Ladder

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

end Drip

end Blanc
