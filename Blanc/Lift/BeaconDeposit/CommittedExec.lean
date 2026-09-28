import Blanc.Lift.BeaconDeposit.Refines
import Blanc.Lift.BeaconDeposit.Ladder
import Blanc.Lift.BeaconDeposit.CommittedReplay
import Blanc.ExecutionDirectCode
import Blanc.ExecutionNoninterference
import Blanc.Lift.CallRestriction
import Blanc.StaticStorage

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc.ExecutionTrace

private def onlyStaticcall : Xinst → Bool
  | .staticcall => true
  | _ => false

private theorem cert_onlyStaticcall :
    ∀ f ∈ cert.prog, f.execsSatisfy onlyStaticcall = true := by
  intro f member
  simp only [Cert.prog, cert, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

/-- The checked deployed certificate permits only STATICCALL at every actual
same-frame location, including internal jumps and returns. -/
theorem parentPrefix_exec_staticcall {root node : Exec.Deriv}
    (pc : root.pc = 0) (installed : root.sevm.code = code)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (chain : Exec.Deriv.ParentPrefix root node)
    {x : Xinst} (instruction : Ninst.At node.sevm.code node.pc (.exec x)) :
    x = .staticcall := by
  obtain ⟨cursor, reachable, checked⟩ :=
    cursor_of_parentPrefix cert_check pc installed fork chain
  have allowed := checked.execsSatisfy
    (cursor.execsSatisfy_of_reachable cert_onlyStaticcall reachable) instruction
  cases x <;> simp_all [onlyStaticcall]

private theorem event_suffix_not_static {sevm : Sevm} {pre : Devm} {out : Outcome}
    (static : sevm.isStatic = true)
    (run : SFunc.Run prog sevm pre t_071c_c4 out) : False := by
  unfold t_071c_c4 at run
  cases run with
  | dest burn run =>
    iterate 22 (cases run; rename_i _ step run)
    cases run with
    | next step run =>
      obtain ⟨pc, logRun⟩ := of_run_reg step
      exact Rinst.log_not_ok_of_static static logRun

/-- A successful deployed deposit cannot run in a static frame. This follows
from the mandatory event emission before the SHA and insertion segments. -/
theorem successful_deposit_not_static {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hsel : Sevm.selector sevm = BeaconDeposit.depositSelector)
    (run : Exec 0 sevm pre (.ok post)) : sevm.isStatic = false := by
  cases hs : sevm.isStatic with
  | false => rfl
  | true =>
    obtain ⟨f, hf, lifted⟩ := lift_sound cert_check hcode hfork run
    have hf0 : prog[0]? = some t_0000_c0 := rfl
    rw [hf0] at hf
    cases hf
    rw [St.self hstack hmem] at lifted
    obtain ⟨k, G1, g, _, hk32, hg, lifted⟩ := safe_dispatch lifted
    have hk : k = 32 := hk32.mpr hsel
    subst k
    have hg32 : g = t_00a4_c32 := by
      have heq : prog[32]? = some t_00a4_c32 := rfl
      rw [heq] at hg
      exact (Option.some.inj hg).symm
    subst g
    obtain ⟨_, G2, d, body, _, _⟩ := safe_decoder hcd lifted
    obtain ⟨_, _, _, _, _, _, b1, M1, G3, _, memory, body⟩ :=
      safe_guards hcd hfork body
    obtain ⟨b2, M2, G4, _, _, body⟩ := safe_event memory body
    exact (event_suffix_not_static hs body).elim

private theorem prefix_installed_image {root node : Exec.Deriv} {ca : Adr}
    (chain : Exec.Deriv.ParentPrefix root node)
    (installed : some (root.devm.getCode ca).toList = beaconSem.image) :
    some (node.devm.getCode ca).toList = beaconSem.image := by
  induction chain with
  | refl => exact installed
  | step edge _ ih =>
    apply ih
    have preserved := Blanc.Exec.Deriv.ParentStep.codePreserve edge ca (by
      intro empty
      exact beaconSem.ne_nil (installed.symm.trans (congrArg some empty)) rfl)
    rw [preserved]
    exact installed

/-- Static committed executions of the deployed deposit selector are impossible
even before imposing the storage invariant. -/
theorem frameAccepted_eq_nil_of_static {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (static : sevm.isStatic = true)
    (run : Exec 0 sevm pre (.ok post)) : frameAccepted sevm = [] := by
  unfold frameAccepted
  split
  next selected =>
    have impossible := successful_deposit_not_static hcode hfork hcd hstack hmem selected run
    rw [static] at impossible
    cases impossible
  next => rfl

private theorem target_descendants_eq_nil
    (ca : Adr) (root : Exec.Deriv)
    (rootPc : root.pc = 0) (rootCode : root.sevm.code = code)
    (rootTarget : root.sevm.currentTarget = ca)
    (rootInstalled : some (root.devm.getCode ca).toList = beaconSem.image)
    (rootFork : CoveredFork root.sevm.benvStat.fork)
    (deeper : ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
      (run : Exec pc sevm pre out) (_committed : Execution.commits out = true),
      CoveredFork sevm.benvStat.fork →
      sevm.depth < root.sevm.depth → beaconSem.At ca pc sevm pre →
      Exec.FrameAdmitted ca beaconFrameEntry run →
      sevm.isStatic = true →
      (Exec.committedFrames run).flatMap (committedFrameNodes ca) = []) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
      (run : Exec pc sevm pre out),
      Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, out, run⟩ →
      (∀ frameRoot ∈ Exec.rawFrameDescendants run,
        frameRoot.sevm.currentTarget = ca →
          beaconFrameEntry frameRoot.sevm frameRoot.devm) →
      (Exec.descendantFrames run).flatMap (committedFrameNodes ca) = [] := by
  intro pc sevm pre out run
  induction run with
  | halt step => simp [Exec.descendantFrames]
  | cont step next ih =>
    intro chain entries
    simpa only [Exec.descendantFrames] using
      ih (chain.snoc (.cont step next)) (by
        simpa only [Exec.rawFrameDescendants] using entries)
  | doneErr step enter resume => simp [Exec.descendantFrames]
  | doneOk step enter resume next ih =>
    intro chain entries
    simpa only [Exec.descendantFrames] using
      ih (chain.snoc (.doneOk step enter resume next)) (by
        simpa only [Exec.rawFrameDescendants] using entries)
  | runErr step enter child resume ih => simp [Exec.descendantFrames]
  | runOk step enter child resume next childIH nextIH =>
    rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
    intro chain entries
    have sevmEq : nodeSevm = root.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
    obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
    have onlyStatic : x = .staticcall :=
      parentPrefix_exec_staticcall rootPc rootCode rootFork chain instruction
    subst x
    have installed : some (nodePre.getCode ca).toList = beaconSem.image :=
      prefix_installed_image chain rootInstalled
    have childFork := Evm.step_spawn_child_fork step enter (by rw [sevmEq]; exact rootFork)
    have childStatic : cevm.sta.isStatic = true :=
      (Frame.enter_run_isStatic enter).trans (Xinst.step_staticcall_spawn_isStatic spawn)
    have childDepth : cevm.sta.depth < root.sevm.depth := by
      rw [Frame.enter_run_depth enter, ← sevmEq]
      exact Step.spawn_depth_lt step
    have childAt : beaconSem.At ca cevm.pc cevm.sta cevm.dyna := by
      obtain ⟨pcZero, getCode, _⟩ := Evm.step_spawn_child step enter
      refine ⟨?_, fun selected => ⟨?_, pcZero⟩⟩
      · rw [getCode ca]
        exact installed
      · have sameTarget : frame.inner.currentTarget = nodeSevm.currentTarget := by
          rw [← Frame.enter_run_currentTarget enter, selected, sevmEq, rootTarget]
        have directCode := Xinst.step_staticcall_sameTarget_code spawn sameTarget (by
          rw [← Frame.enter_run_currentTarget enter, selected]
          exact beaconSem.not_delegation installed)
        rw [Frame.enter_run_code enter, directCode,
          ← Frame.enter_run_currentTarget enter, selected]
        exact installed
    have childEntries : Exec.FrameAdmitted ca beaconFrameEntry child := by
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

/-- A selected committed frame contributes exactly its own accepted node.
The derived STATICCALL restriction makes every retained child static; the
lower-depth static-frame conclusion then removes its entire observation. -/
theorem target_committedFrameNodes {ca : Adr} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (hcode : sevm.code = code) (target : sevm.currentTarget = ca)
    (installed : beaconSem.At ca 0 sevm pre)
    (fork : CoveredFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted ca beaconFrameEntry run)
    (deeper : ∀ {pc : Nat} {s : Sevm} {d : Devm} {out : Execution}
      (child : Exec pc s d out) (_committed : Execution.commits out = true),
      CoveredFork s.benvStat.fork → s.depth < sevm.depth →
      beaconSem.At ca pc s d → Exec.FrameAdmitted ca beaconFrameEntry child →
      s.isStatic = true →
      (Exec.committedFrames child).flatMap (committedFrameNodes ca) = []) :
    (Exec.committedFrames run).flatMap (committedFrameNodes ca) =
      frameAccepted sevm := by
  have descendants := target_descendants_eq_nil ca ⟨0, sevm, pre, .ok post, run⟩
    rfl hcode target installed.1 fork (by exact deeper) run (.refl _) (by
      intro frameRoot member selected
      exact admitted frameRoot (List.mem_cons_of_mem _ member) selected)
  simp only [Exec.committedFrames, dite_eq_left committed, List.flatMap_cons,
    descendants, List.append_nil, committedFrameNodes, Exec.Frame.ofRun]
  simp only [ite_eq_left target]

end Blanc.Lift.BeaconDeposit
