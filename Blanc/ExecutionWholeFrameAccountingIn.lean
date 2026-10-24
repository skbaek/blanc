import Blanc.ExecutionAccountingCoreIn
import Blanc.ExecutionAccountingCore
import Blanc.ExecutionAccountingAdmissionIn
import Blanc.ExecutionEntryAccounting
import Blanc.ExecutionModelAccounting
import Blanc.LockExclusion
import Blanc.StaticStorage

/-!
# Whole-frame accounting over a selected fork domain

The modern whole-frame handler (`Blanc/ExecutionWholeFrameAccounting.lean`)
carries `CoveredFork` through the spawn-child transport, the static case and
the frame obligation. Its fork use is confined to those three leaves.

This module is the additive historical counterpart over a selected fork
domain `F`: `SpawnKindsIn F`, `spawnChildIn` (child transport via
`Evm.step_spawn_child_forkIn`), `staticObservedNilIn`/`staticFrameIn` (the
static storage seam via its `_noStateGas` twin), `WholeFrameReplayIn F`
(keeping the modern binder order exactly), `wholeFrameTargetIn`, and
`wholeFrameLadderIn` producing `AccountingLadderAdmittedIn` (`messageRoot_facts`
reused unchanged; `Exec.derivEntry` is fork-free and reused as is).
-/

namespace Blanc

open Jaune
open ExecutionAccountingReplay

/-- Every external instruction a successful target frame decodes along its own
chain is `CALL` or `STATICCALL`, over a selected fork domain `F`. -/
def SpawnKindsIn (F : Fork → Prop) (ca : Adr) (sem : CodeSem) : Prop :=
  ∀ {sevm pre post} (run : Exec 0 sevm pre (.ok post)),
    sem.Run sevm pre post → sevm.currentTarget = ca → F sevm.benvStat.fork →
    sem.At ca 0 sevm pre →
    ∀ node, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ node →
      ∀ x, Ninst.At node.sevm.code node.pc (.exec x) → x = .call ∨ x = .staticcall

namespace Exec.CoreAccountingIn

variable {F : Fork → Prop}
variable {ca : Adr} {sem : CodeSem} {entry : Sevm → Devm → Prop}
variable {C : ReplayCarrier ca} {V : ReplayObservation C}

/-- **The child of a spawning node over `F`.** The node's fork routes through
the chain's `sevm_eq`; the child's through `Evm.step_spawn_child_forkIn`. -/
theorem spawnChildIn
    (kinds : SpawnKindsIn F ca sem)
    {sevm₀ : Sevm} {pre₀ post₀ : Devm} (root : Exec 0 sevm₀ pre₀ (.ok post₀))
    (hrun : sem.Run sevm₀ pre₀ post₀) (target : sevm₀.currentTarget = ca)
    (hF : F sevm₀.benvStat.fork) (installed : sem.At ca 0 sevm₀ pre₀)
    (admitted : Exec.FrameAdmitted ca entry root)
    (deeper : ForallDeeperAtSem sevm₀.depth ca sem
      (fun pc s d e _ => Exec.CoreAccountingIn F ca sem entry C V pc s d e))
    {nodePc : Nat} {nodeSevm : Sevm} {nodePre : Devm} {out : Execution} {frame : Jaune.Frame}
    {rsm : Resume} {nextPc : Nat} {cevm : Evm} {raw : Execution} {inter : Devm}
    (step : Evm.step ⟨nodePc, nodeSevm, nodePre⟩ = .spawn frame rsm nextPc)
    (enter : frame.enter = .run cevm) (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (resume : rsm.run (frame.settle raw) = .ok inter) (next : Exec nextPc nodeSevm inter out)
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm₀, pre₀, .ok post₀, root⟩
      ⟨nodePc, nodeSevm, nodePre, out, .runOk step enter child resume next⟩) :
    ∃ x : Xinst, Ninst.At nodeSevm.code nodePc (.exec x) ∧
      F nodeSevm.benvStat.fork ∧ nodePre.getCode ca ≠ .empty ∧
      sum nodePre.state.bal ≤ sum pre₀.state.bal ∧ F cevm.sta.benvStat.fork ∧
      (nodeSevm.isStatic = true → cevm.sta.isStatic = true) ∧
      ∀ committed : Execution.commits raw = true,
        (cevm.sta.isStatic = true → (Exec.committedFrames child).flatMap V.frameObs = []) ∧
        (sum cevm.dyna.state.bal < 2 ^ 256 → ∃ steps,
          C.Replay (C.frameEntry cevm.sta cevm.dyna.state) steps
            (C.ofState (Execution.committedPost raw committed).state) ∧
          V.obs steps = (Exec.committedFrames child).flatMap V.frameObs) := by
  have sevmEq : nodeSevm = sevm₀ := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  obtain ⟨x, instruction, spawnStep, _⟩ := Evm.step_spawn_inv step
  have kind := kinds root hrun target hF installed _ chain x instruction
  obtain ⟨balLe, codeEq⟩ := Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain
  have codeNe : (pre₀.getCode ca).toList ≠ [] := fun empty =>
    sem.ne_nil (installed.1.symm.trans (congrArg some empty)) rfl
  have nodeInstalled : some (nodePre.getCode ca).toList = sem.image := by
    rw [show nodePre.getCode ca = pre₀.getCode ca from codeEq ca codeNe]
    exact installed.1
  have nodeCodeNe : nodePre.getCode ca ≠ .empty := fun empty => by
    rw [empty] at nodeInstalled
    exact sem.ne_nil nodeInstalled.symm (by simp only [ByteArray.toList_empty])
  have nodeFork : F nodeSevm.benvStat.fork := by rw [sevmEq]; exact hF
  have childFork := _root_.Blanc.LockExclusion.Evm.step_spawn_child_forkIn step enter nodeFork
  have childDepth : cevm.sta.depth < sevm₀.depth := by
    rw [Frame.enter_run_depth enter, ← sevmEq]
    exact Step.spawn_depth_lt step
  have childAt : sem.At ca cevm.pc cevm.sta cevm.dyna := by
    obtain ⟨pcZero, getCode, _⟩ := Evm.step_spawn_child step enter
    refine ⟨?_, fun selected => ⟨?_, pcZero⟩⟩
    · rw [getCode ca]
      exact nodeInstalled
    · have sameTarget : frame.inner.currentTarget = nodeSevm.currentTarget := by
        rw [← Frame.enter_run_currentTarget enter, selected, sevmEq, target]
      have notDel : ¬ isValidDelegation (nodePre.getCode frame.inner.currentTarget) := by
        rw [← Frame.enter_run_currentTarget enter, selected]
        exact sem.not_delegation nodeInstalled
      have directCode : frame.inner.code = nodePre.getCode frame.inner.currentTarget := by
        rcases kind with rfl | rfl
        · exact Xinst.step_call_sameTarget_code spawnStep sameTarget notDel
        · exact Xinst.step_staticcall_sameTarget_code spawnStep sameTarget notDel
      rw [Frame.enter_run_code enter, directCode, ← Frame.enter_run_currentTarget enter,
        selected]
      exact nodeInstalled
  have childAdmitted : Exec.FrameAdmitted ca entry child := by
    intro childRoot member selected
    apply admitted childRoot _ selected
    apply List.mem_cons_of_mem
    apply Exec.mem_rawFrameDescendants_of_parentPrefix chain
    simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append]
    simp only [Exec.rawFrameRoots, List.mem_cons] at member
    rcases member with rfl | member
    · exact Or.inl rfl
    · exact Or.inr (Or.inl member)
  have childCore := deeper cevm.pc cevm.sta cevm.dyna raw child childDepth childAt
  exact ⟨x, instruction, nodeFork, nodeCodeNe, balLe, childFork,
    fun static => (Frame.enter_run_isStatic enter).trans
      (Xinst.step_spawn_isStatic spawnStep static),
    fun committed => childCore child committed childFork childAt childAdmitted⟩

/-- **Below a static frame no committed frame is observed, over `F`.** The
induction is fork-free; the `runOk` arm routes through `spawnChildIn`. -/
theorem staticObservedNilIn (kinds : SpawnKindsIn F ca sem)
    {sevm₀ : Sevm} {pre₀ post₀ : Devm} (root : Exec 0 sevm₀ pre₀ (.ok post₀))
    (hrun : sem.Run sevm₀ pre₀ post₀) (target : sevm₀.currentTarget = ca)
    (hF : F sevm₀.benvStat.fork) (installed : sem.At ca 0 sevm₀ pre₀)
    (admitted : Exec.FrameAdmitted ca entry root)
    (deeper : ForallDeeperAtSem sevm₀.depth ca sem
      (fun pc s d e _ => Exec.CoreAccountingIn F ca sem entry C V pc s d e)) :
    ∀ {pc : Nat} {sevm : Sevm} {d : Devm} {out : Execution} (run : Exec pc sevm d out),
      Exec.Deriv.ParentPrefix ⟨0, sevm₀, pre₀, .ok post₀, root⟩ ⟨pc, sevm, d, out, run⟩ →
      sevm.isStatic = true → (Exec.descendantFrames run).flatMap V.frameObs = [] := by
  intro pc sevm d out run
  induction run with
  | halt step => intro _ _; simp only [descendantFrames, List.flatMap_nil]
  | cont step next ih =>
      intro chain hs
      simpa only [Exec.descendantFrames] using ih (chain.snoc (.cont step next)) hs
  | doneErr step enter resume => intro _ _; simp only [descendantFrames, List.flatMap_nil]
  | doneOk step enter resume next ih =>
      intro chain hs
      simpa only [Exec.descendantFrames] using
        ih (chain.snoc (.doneOk step enter resume next)) hs
  | runErr step enter child resume ih => intro _ _; simp only [descendantFrames, List.flatMap_nil]
  | runOk step enter child resume next childIH nextIH =>
      rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
      intro chain hs
      obtain ⟨x, instruction, nodeFork, nodeCodeNe, balLe, childFork, childStaticOf, childCore⟩ :=
        spawnChildIn kinds root hrun target hF installed admitted deeper step enter child resume
          next chain
      rw [_root_.Blanc.Exec.descendantFrames_flatMap_runOk,
        nextIH (chain.snoc (.runOk step enter child resume next)) hs, List.append_nil]
      split
      · rename_i settles
        exact (childCore (Frame.raw_commits_of_settlementCommits settles)).1 (childStaticOf hs)
      · rfl

/-- **A static frame's accounting over `F`**, given that nothing below it is
observed. The storage seam is the `_noStateGas` twin. -/
theorem staticFrameIn
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true) (hsg : sevm.benvStat.rules.stateGas = none)
    (codeNe : (pre.getCode ca).toList ≠ []) (hs : sevm.isStatic = true)
    (hdf : (Exec.descendantFrames run).flatMap V.frameObs = []) :
    (sevm.isStatic = true → (Exec.committedFrames run).flatMap V.frameObs = []) ∧
    (sum pre.state.bal < 2 ^ 256 → ∃ steps,
      C.Replay (C.frameEntry sevm pre.state) steps
        (C.ofState (Execution.committedPost (.ok post) committed).state) ∧
      V.obs steps = (Exec.committedFrames run).flatMap V.frameObs) := by
  have self : (Exec.committedFrames run).flatMap V.frameObs =
      V.frameObs (Exec.Frame.ofRun run committed) ++
        (Exec.descendantFrames run).flatMap V.frameObs := by
    rw [Exec.committedFrames, dite_eq_left committed, List.flatMap_cons]
  have hself : V.frameObs (Exec.Frame.ofRun run committed) = [] := obsStatic _ hs
  have hobs : (Exec.committedFrames run).flatMap V.frameObs = [] := by
    rw [self, hdf, hself]
    rfl
  refine ⟨fun _ => hobs, fun _ => ⟨[], ?_, ?_⟩⟩
  · have hview := Exec.getStor_committedPost_eq_of_static_protected_noStateGas run hs committed hsg ca
      (State.Protected.of_code_ne_nil codeNe)
    have heq : C.ofState (Execution.committedPost (.ok post) committed).state =
        C.ofState pre.state := ofStateGet fun k => congrArg (fun stor => stor.get k) hview
    rw [heq, entryOfState]
    exact C.nil _
  · rw [hobs]
    exact V.obs_nil

/-- **The contract's whole-frame obligation, over `F`.** Binder order matches
`WholeFrameReplay` exactly, so the Mac's `pair_wholeFrameReplayWithIn` fits. -/
def WholeFrameReplayIn (F : Fork → Prop) (ca : Adr) (sem : CodeSem) (entry : Sevm → Devm → Prop)
    (C : ReplayCarrier ca) (V : ReplayObservation C) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post)),
    Execution.commits (.ok post) = true →
    sem.Run sevm pre post → sevm.currentTarget = ca → F sevm.benvStat.fork →
    sem.At ca 0 sevm pre → Exec.FrameAdmitted ca entry run → sum pre.state.bal < 2 ^ 256 →
    sevm.isStatic = false →
    ∃ steps : List C.Step, C.Replay (C.frameEntry sevm pre.state) steps (C.ofState post.state) ∧
      V.obs steps = (Exec.committedFrames run).flatMap V.frameObs

/-- **The whole-frame target handler, over `F`.** The static arm uses
`staticFrameIn`/`staticObservedNilIn`; the live arm is the contract's own
`WholeFrameReplayIn`. -/
theorem wholeFrameTargetIn
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (kinds : SpawnKindsIn F ca sem) (whole : WholeFrameReplayIn F ca sem entry C V)
    (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none)
    {sevm : Sevm} {pre post : Devm} (hrun : sem.Run sevm pre post)
    (target : sevm.currentTarget = ca)
    (deeper : ForallDeeperAtSem sevm.depth ca sem
      (fun pc s d e _ => Exec.CoreAccountingIn F ca sem entry C V pc s d e)) :
    Exec.CoreAccountingIn F ca sem entry C V 0 sevm pre (.ok post) := by
  intro run committed hF installed admitted
  have hsg : sevm.benvStat.rules.stateGas = none := hsgF hF
  have rootNonempty : (pre.getCode ca).toList ≠ [] := fun empty =>
    sem.ne_nil (installed.1.symm.trans (congrArg some empty)) rfl
  by_cases hs : sevm.isStatic = true
  · exact staticFrameIn entryOfState ofStateGet obsStatic run committed hsg rootNonempty hs
      (staticObservedNilIn kinds run hrun target hF installed admitted deeper run (.refl _) hs)
  · have hs' : sevm.isStatic = false := by simpa only [Bool.not_eq_true] using hs
    exact ⟨fun h => absurd h hs, fun bound =>
      whole run committed hrun target hF installed admitted bound hs'⟩

end Exec.CoreAccountingIn

namespace ExecutionAccountingReplay

/-- **The accounting ladder of a whole-frame replay, over `F`.** The
contract's `PreservesAdmittedIn` and its `WholeFrameReplayIn` give the
observed accounting ladder; foreign frames, messages, transactions, blocks
and rollback are the generic ladder's. -/
def wholeFrameLadderIn {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}
    (C : ReplayCarrier ca) (V : ReplayObservation C)
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (tag : Nat → Option Nat → C.Tag) (frameTag : Sevm → Devm → C.Tag)
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none)
    (kinds : SpawnKindsIn F ca c.sem)
    (whole : Exec.CoreAccountingIn.WholeFrameReplayIn F ca c.sem entry C V)
    (preserves : c.PreservesAdmittedIn F ca entry) : AccountingLadderAdmittedIn F c ca entry where
  carrier := C
  append := append
  tag := tag
  preserves := preserves
  view := V
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ hF
      bound
    obtain ⟨installed, entryBound⟩ :=
      Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    have core := Exec.coreAccountingIn F ca c.sem entry C V append frameTag
      (fun sevm state _ => entryOfState sevm state) obsForeign hsgF
      (fun hrun target deeper =>
        Exec.CoreAccountingIn.wholeFrameTargetIn entryOfState ofStateGet obsStatic kinds whole
          hsgF hrun target deeper)
    exact (core pc sevm pre out run installed run committed hF installed admitted).2 entryBound

end ExecutionAccountingReplay

end Blanc