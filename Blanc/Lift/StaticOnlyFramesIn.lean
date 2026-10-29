import Blanc.Lift.StaticOnlyFrames
import Blanc.LockExclusion

/-! Static-only descendant accounting under a selected historical fork domain.
The certificate restriction needs only stateGas = none; child domains inherit
the actual spawned environment, without identifying historical and modern runs. -/

namespace Blanc.Lift

open Jaune

/-- A checked static-only certificate restricts every actual same-frame spawn. -/
theorem parentPrefix_exec_staticcall_of_cert_noStateGas {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true)
    (only : ∀ f ∈ c.prog, f.execsSatisfy Xinst.isStaticcall = true)
    {root node : Exec.Deriv} (pc : root.pc = 0) (installed : root.sevm.code = code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    {x : Xinst} (instruction : Ninst.At node.sevm.code node.pc (.exec x)) :
    x = .staticcall := by
  obtain ⟨cursor, reachable, ok⟩ := cursor_of_parentPrefix_noStateGas checked pc installed hsg chain
  have allowed := ok.execsSatisfy
    (cursor.execsSatisfy_of_reachable only reachable) instruction
  cases x <;> simp_all only [Xinst.isStaticcall, Bool.false_eq_true]

end Blanc.Lift

namespace Blanc

open Jaune

/-- All retained descendants of static-only code have empty observations over F,
using the lower-depth static-frame accounting conclusion. -/
theorem Exec.staticOnly_descendantFrames_flatMap_eq_nilIn {F : Fork → Prop} {α : Type}
    (ca : Adr) (sem : CodeSem) (entry : Sevm → Devm → Prop)
    (obs : Exec.Frame → List α) (root : Exec.Deriv)
    (rootTarget : root.sevm.currentTarget = ca)
    (rootInstalled : some (root.devm.getCode ca).toList = sem.image)
    (rootFork : F root.sevm.benvStat.fork)
    (staticOnly : ∀ {node : Exec.Deriv} {x : Xinst},
      Exec.Deriv.ParentPrefix root node →
      Ninst.At node.sevm.code node.pc (.exec x) → x = .staticcall)
    (deeper : ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
      (run : Exec pc sevm pre out) (_committed : Execution.commits out = true),
      F sevm.benvStat.fork →
      sevm.depth < root.sevm.depth → sem.At ca pc sevm pre →
      Exec.FrameAdmitted ca entry run →
      sevm.isStatic = true →
      (Exec.committedFrames run).flatMap obs = []) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
      (run : Exec pc sevm pre out),
      Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, out, run⟩ →
      (∀ frameRoot ∈ Exec.rawFrameDescendants run,
        frameRoot.sevm.currentTarget = ca → entry frameRoot.sevm frameRoot.devm) →
      (Exec.descendantFrames run).flatMap obs = [] := by
  intro pc sevm pre out run
  induction run with
  | halt step => simp only [descendantFrames, List.flatMap_nil, implies_true]
  | cont step next ih =>
    intro chain entries
    simpa only [Exec.descendantFrames] using
      ih (chain.snoc (.cont step next)) (by
        simpa only [Exec.rawFrameDescendants] using entries)
  | doneErr step enter resume => simp only [descendantFrames, List.flatMap_nil, implies_true]
  | doneOk step enter resume next ih =>
    intro chain entries
    simpa only [Exec.descendantFrames] using
      ih (chain.snoc (.doneOk step enter resume next)) (by
        simpa only [Exec.rawFrameDescendants] using entries)
  | runErr step enter child resume ih => simp only [descendantFrames, List.flatMap_nil,
    implies_true]
  | runOk step enter child resume next childIH nextIH =>
    rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
    intro chain entries
    have sevmEq : nodeSevm = root.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
    obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
    have onlyStatic : x = .staticcall := staticOnly chain instruction
    subst x
    have codeNe : (root.devm.getCode ca).toList ≠ [] := fun empty =>
      sem.ne_nil (rootInstalled.symm.trans (congrArg some empty)) rfl
    have installed : some (nodePre.getCode ca).toList = sem.image := by
      rw [Blanc.Exec.Deriv.ParentPrefix.codePreserve chain ca codeNe]
      exact rootInstalled
    have childFork : F cevm.sta.benvStat.fork :=
      Blanc.LockExclusion.Evm.step_spawn_child_forkIn (F := F) step enter
        (by rw [sevmEq]; exact rootFork)
    have childStatic : cevm.sta.isStatic = true :=
      (Frame.enter_run_isStatic enter).trans (Xinst.step_staticcall_spawn_isStatic spawn)
    have childDepth : cevm.sta.depth < root.sevm.depth := by
      rw [Frame.enter_run_depth enter, ← sevmEq]
      exact Step.spawn_depth_lt step
    have childAt : sem.At ca cevm.pc cevm.sta cevm.dyna := by
      obtain ⟨pcZero, getCode, _⟩ := Evm.step_spawn_child step enter
      refine ⟨?_, fun selected => ⟨?_, pcZero⟩⟩
      · rw [getCode ca]
        exact installed
      · have sameTarget : frame.inner.currentTarget = nodeSevm.currentTarget := by
          rw [← Frame.enter_run_currentTarget enter, selected, sevmEq, rootTarget]
        have directCode := Xinst.step_staticcall_sameTarget_code spawn sameTarget (by
          rw [← Frame.enter_run_currentTarget enter, selected]
          exact sem.not_delegation installed)
        rw [Frame.enter_run_code enter, directCode,
          ← Frame.enter_run_currentTarget enter, selected]
        exact installed
    have childEntries : Exec.FrameAdmitted ca entry child := by
      intro childRoot member selected
      apply entries childRoot _ selected
      simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append]
      simp only [Exec.rawFrameRoots, List.mem_cons] at member
      rcases member with rfl | member
      · exact Or.inl rfl
      · exact Or.inr (Or.inl member)
    have nextNodes := nextIH (chain.snoc (.runOk step enter child resume next)) (by
      intro childRoot member selected
      exact entries childRoot (by
        simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr member)) selected)
    simp only [Exec.descendantFrames]
    split
    next settles =>
      have rawCommits := Frame.raw_commits_of_settlementCommits settles
      have childNodes := deeper child rawCommits childFork childDepth childAt childEntries childStatic
      simp only [Exec.committedFrames, dite_eq_left rawCommits] at childNodes
      rw [List.flatMap_append, childNodes, nextNodes]
      rfl
    next => simpa only [List.nil_append] using nextNodes

end Blanc
