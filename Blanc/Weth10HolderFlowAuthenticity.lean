import Blanc.Weth10HolderFlow

/-!
Root-altitude facts for the retained execution ledger.

Every `Exec` admitted by a settled message trace starts at the initial machine
of an entered frame.  Recursive child derivations likewise start at their
frame entry.  This is the bridge from the structural committed-frame traversal
to the whole-program functional theorems, which require `pc = 0` and fresh
memory.
-/

namespace Blanc

open Jaune

namespace Weth10

/-- A retained frame is a whole entered code frame, rather than an arbitrary
mid-program continuation. -/
def Exec.Frame.IsRoot (frame : Exec.Frame) : Prop :=
  frame.pc = 0 ∧ frame.pre.memory = Mem.empty

theorem frame_enter_run_memory
    {frame : Frame} {child : Evm}
    (h : frame.enter = .run child) : child.dyna.memory = Mem.empty := by
  obtain ⟨benv, _, rfl⟩ := Frame.enter_run_inv h
  rfl

private theorem byteArray_eq_of_toList_eq {left right : ByteArray}
    (h : left.toList = right.toList) : left = right := by
  cases left with
  | mk leftData =>
      cases right with
      | mk rightData =>
          simp only [ByteArray.toList_eq_toList_data] at h
          cases Array.ext' h
          rfl

/-- The proof-only context required to turn an executable candidate into an
authentic whole-program action.  It adds the installed-code witness that is
deliberately absent from the decidable filter. -/
structure Exec.Frame.AuthenticContext
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame) : Prop where
  root : Blanc.Weth10.Exec.Frame.IsRoot frame
  invocation : Blanc.Weth10.Exec.Frame.exactInvocation dp ca frame
  installed : Prog.At (weth10 dp) ca frame.pc frame.sevm frame.pre
  /-- The frame runs on a covered fork; inherited from the root frame, since
  a spawned child keeps its parent's block environment. -/
  covered : CoveredFork frame.sevm.benvStat.fork

theorem Exec.Frame.AuthenticContext.memory_wf
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (h : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame) : Mem.Wf frame.pre.memory := by
  rw [h.root.2]
  exact Mem.wf_empty

theorem Exec.Frame.AuthenticContext.memory_reads_empty
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (h : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame) : Mem.Reads frame.pre.memory [] := by
  rw [h.root.2]
  exact Mem.reads_empty

theorem Exec.Frame.AuthenticContext.stateCode_eq
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (h : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame) :
    frame.pre.getCode ca = frame.sevm.code := by
  apply byteArray_eq_of_toList_eq
  exact Option.some.inj (h.installed.1.trans h.invocation.2.2.2.symm)

private theorem step_ok_getCode_eq
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre post : Devm} {xl : Xlot}
    (hxl : Xlot.Rel Devm.CodePreserve xl)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, pre⟩) xl (.ok post))
    (hcode : some (pre.getCode ca).toList = Prog.compile (weth10 dp)) :
    post.getCode ca = pre.getCode ca := by
  have hne : (pre.getCode ca).toList ≠ [] := fun hempty =>
    Prog.compile_ne_nil (hcode.symm.trans (congrArg some hempty))
  exact Evm.step_effect codePreserve_refl_trans.1
    Ninst.codePreserve_effectRec Jinst.codePreserve_effect
    Linst.codePreserve_effect hxl hrun ca hne

/-- Every successful descendant sees the same installed WETH10 code in the
world state, even when the descendant itself executes foreign callback code. -/
theorem Exec.mem_descendantFrames_installedCode
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hcode : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    {frame : Exec.Frame}
    (hmem : frame ∈ Blanc.Exec.descendantFrames run) :
    some (frame.pre.getCode ca).toList = Prog.compile (weth10 dp) := by
  revert hcode frame
  induction run with
  | halt hstep =>
      intro hcode frame hmem
      simp [Jaune.Exec.descendantFrames] at hmem
  | cont hstep next ih =>
      intro hcode frame hmem
      apply ih
      · rw [step_ok_getCode_eq (dp := dp) (ca := ca) (xl := .none) trivial
          (by rw [hstep]; exact ⟨rfl, rfl⟩) hcode]
        exact hcode
      · simpa only [Jaune.Exec.descendantFrames] using hmem
  | doneErr hstep henter hresume =>
      intro hcode frame hmem
      simp [Jaune.Exec.descendantFrames] at hmem
  | doneOk hstep henter hresume next ih =>
      intro hcode frame hmem
      apply ih
      · rw [step_ok_getCode_eq (dp := dp) (ca := ca) (xl := .none) trivial
          (by
            rw [hstep]
            exact ⟨_, RunFrame.of_done henter, hresume.symm⟩) hcode]
        exact hcode
      · simpa only [Jaune.Exec.descendantFrames] using hmem
  | runErr hstep henter child hresume ihChild =>
      intro hcode frame hmem
      simp [Jaune.Exec.descendantFrames] at hmem
  | @runOk pc sevm pre f rsm pc' cevm raw nextPre out hstep henter child
      hresume next ihChild ihNext =>
      intro hcode frame hmem
      have hchildCode :
          some (cevm.dyna.getCode ca).toList = Prog.compile (weth10 dp) := by
        rw [(Evm.step_spawn_child hstep henter).2.1 ca]
        exact hcode
      have hchildRel :
          Xlot.Rel Devm.CodePreserve (.some ⟨cevm, raw⟩) :=
        Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
          Ninst.codePreserve_effectRec Jinst.codePreserve_effect
          Linst.codePreserve_effect child
      have hnextCode :
          some (nextPre.getCode ca).toList = Prog.compile (weth10 dp) := by
        rw [step_ok_getCode_eq (dp := dp) (ca := ca) hchildRel
          (by
            rw [hstep]
            exact ⟨_, RunFrame.of_run henter, hresume.symm⟩) hcode]
        exact hcode
      simp only [Jaune.Exec.descendantFrames] at hmem
      split at hmem
      · simp only [List.mem_append, List.mem_cons] at hmem
        rcases hmem with (rfl | hchild) | hnext
        · exact hchildCode
        · exact ihChild hchildCode hchild
        · exact ihNext hnextCode hnext
      · exact ihNext hnextCode hmem

theorem Exec.committedFrames_installedCode
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hcode : some (pre.getCode ca).toList = Prog.compile (weth10 dp)) :
    ∀ frame ∈ Blanc.Exec.committedFrames run,
      some (frame.pre.getCode ca).toList = Prog.compile (weth10 dp) := by
  intro frame hframe
  unfold Jaune.Exec.committedFrames at hframe
  split at hframe
  · simp only [List.mem_cons] at hframe
    rcases hframe with rfl | hdesc
    · exact hcode
    · exact Blanc.Weth10.Exec.mem_descendantFrames_installedCode run hcode hdesc
  · cases hframe

/-- Every descendant retained by `Exec.descendantFrames` is the initial
machine of an actually entered child frame. -/
theorem Exec.mem_descendantFrames_isRoot
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) {frame : Exec.Frame}
    (hmem : frame ∈ Blanc.Exec.descendantFrames run) :
    Blanc.Weth10.Exec.Frame.IsRoot frame := by
  induction run with
  | halt hstep =>
      simp [Jaune.Exec.descendantFrames] at hmem
  | cont hstep next ih =>
      apply ih
      simpa only [Jaune.Exec.descendantFrames] using hmem
  | doneErr hstep henter hresume =>
      simp [Jaune.Exec.descendantFrames] at hmem
  | doneOk hstep henter hresume next ih =>
      apply ih
      simpa only [Jaune.Exec.descendantFrames] using hmem
  | runErr hstep henter child hresume ihChild =>
      simp [Jaune.Exec.descendantFrames] at hmem
  | runOk hstep henter child hresume next ihChild ihNext =>
      simp only [Jaune.Exec.descendantFrames] at hmem
      split at hmem
      · simp only [List.mem_append, List.mem_cons] at hmem
        rcases hmem with (rfl | hchild) | hnext
        · exact ⟨Frame.enter_run_pc henter,
            frame_enter_run_memory henter⟩
        · exact ihChild hchild
        · exact ihNext hnext
      · exact ihNext hmem

/-- Every descendant retained by `Exec.descendantFrames` runs on its root's
fork, so root coverage covers them all. -/
theorem Exec.mem_descendantFrames_covered
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hfork : CoveredFork sevm.benvStat.fork) {frame : Exec.Frame}
    (hmem : frame ∈ Blanc.Exec.descendantFrames run) :
    CoveredFork frame.sevm.benvStat.fork := by
  induction run with
  | halt hstep =>
      simp [Jaune.Exec.descendantFrames] at hmem
  | cont hstep next ih =>
      exact ih hfork (by simpa only [Jaune.Exec.descendantFrames] using hmem)
  | doneErr hstep henter hresume =>
      simp [Jaune.Exec.descendantFrames] at hmem
  | doneOk hstep henter hresume next ih =>
      exact ih hfork (by simpa only [Jaune.Exec.descendantFrames] using hmem)
  | runErr hstep henter child hresume ihChild =>
      simp [Jaune.Exec.descendantFrames] at hmem
  | runOk hstep henter child hresume next ihChild ihNext =>
      have hchildFork := Evm.step_spawn_child_fork hstep henter hfork
      simp only [Jaune.Exec.descendantFrames] at hmem
      split at hmem
      · simp only [List.mem_append, List.mem_cons] at hmem
        rcases hmem with (rfl | hchild) | hnext
        · exact hchildFork
        · exact ihChild hchildFork hchild
        · exact ihNext hfork hnext
      · exact ihNext hfork hmem

/-- Root coverage covers the complete committed-frame list. -/
theorem Exec.committedFrames_covered
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hfork : CoveredFork sevm.benvStat.fork) :
    ∀ frame ∈ Blanc.Exec.committedFrames run,
      CoveredFork frame.sevm.benvStat.fork := by
  intro frame hframe
  unfold Jaune.Exec.committedFrames at hframe
  split at hframe
  · simp only [List.mem_cons] at hframe
    rcases hframe with rfl | hdesc
    · exact hfork
    · exact Blanc.Weth10.Exec.mem_descendantFrames_covered run hfork hdesc
  · cases hframe

/-- Root freshness plus the structural child theorem covers the complete
committed-frame list. -/
theorem Exec.committedFrames_isRoot
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hpc : pc = 0) (hmemory : pre.memory = Mem.empty) :
    ∀ frame ∈ Blanc.Exec.committedFrames run, Blanc.Weth10.Exec.Frame.IsRoot frame := by
  intro frame hframe
  unfold Jaune.Exec.committedFrames at hframe
  split at hframe
  · simp only [List.mem_cons] at hframe
    rcases hframe with rfl | hdesc
    · exact ⟨hpc, hmemory⟩
    · exact Blanc.Weth10.Exec.mem_descendantFrames_isRoot run hdesc
  · cases hframe

/-- A retained numeric action can only come from the exact direct WETH10
invocation arm of the executable classifier. -/
theorem Exec.Frame.exactInvocation_of_flowAction?_eq_some
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.exactInvocation dp ca frame := by
  unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
  split at haction
  · assumption
  · simp at haction

/-- Any retained frame whose executable context already pins an exact direct
WETH10 invocation has the full compiled-functional context.  Unlike the
action-oriented adapter below, this form does not assume that the frame has
already been classified; it is the program-level entry point for reverse
balance-write completeness. -/
theorem Exec.Frame.authenticContext_of_mem_committedFrames_exactInvocation
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hcode : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (hpc : pc = 0) (hmemory : pre.memory = Mem.empty)
    (hfork : CoveredFork sevm.benvStat.fork)
    {frame : Exec.Frame}
    (hframe : frame ∈ Blanc.Exec.committedFrames run)
    (hinvocation : Blanc.Weth10.Exec.Frame.exactInvocation dp ca frame) :
    Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame := by
  refine ⟨Blanc.Weth10.Exec.committedFrames_isRoot run hpc hmemory frame hframe,
    hinvocation, ?_,
    Blanc.Weth10.Exec.committedFrames_covered run hfork frame hframe⟩
  refine ⟨Blanc.Weth10.Exec.committedFrames_installedCode run hcode frame hframe, ?_⟩
  intro _
  exact ⟨hinvocation.2.2.2, hinvocation.1⟩

/-- Every action selected from a committed execution frame has the complete
whole-program context needed by the compiled WETH10 functional theorems. -/
theorem Exec.Frame.authenticContext_of_mem_committedFrames
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hcode : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (hpc : pc = 0) (hmemory : pre.memory = Mem.empty)
    (hfork : CoveredFork sevm.benvStat.fork)
    {frame : Exec.Frame} {action : FlowAction}
    (hframe : frame ∈ Blanc.Exec.committedFrames run)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame := by
  have hinvocation :=
    Blanc.Weth10.Exec.Frame.exactInvocation_of_flowAction?_eq_some haction
  exact Blanc.Weth10.Exec.Frame.authenticContext_of_mem_committedFrames_exactInvocation
    run hcode hpc hmemory hfork hframe hinvocation

/-- All committed frames retained by one raw execution slot start at whole
frame altitude. -/
def RetainedXlot.AllFramesRoot :
    {xl : Xlot} → RetainedXlot xl → Prop
  | _, .none => True
  | _, .some run =>
      ∀ frame ∈ Jaune.Exec.committedFrames run, Blanc.Weth10.Exec.Frame.IsRoot frame

theorem ProcessMessageTrace.allFramesRoot
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) :
    Blanc.Weth10.RetainedXlot.AllFramesRoot trace.retained := by
  rcases trace with ⟨slot, retained, hrun⟩
  cases retained with
  | none => simp [RetainedXlot.AllFramesRoot]
  | @some pc sevm pre execution run =>
      have henter : (Frame.ofCall msg).enter =
          .run ⟨pc, sevm, pre⟩ :=
        (RunFrame.some_inv hrun).1
      exact Blanc.Weth10.Exec.committedFrames_isRoot run
        (Frame.enter_run_pc henter)
        (frame_enter_run_memory henter)

theorem ProcessCreateMessageTrace.allFramesRoot
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) :
    Blanc.Weth10.RetainedXlot.AllFramesRoot trace.retained := by
  rcases trace with ⟨slot, retained, hrun⟩
  cases retained with
  | none => simp [RetainedXlot.AllFramesRoot]
  | @some pc sevm pre execution run =>
      have henter : (Frame.ofCreate msg).enter =
          .run ⟨pc, sevm, pre⟩ :=
        (RunFrame.some_inv hrun).1
      exact Blanc.Weth10.Exec.committedFrames_isRoot run
        (Frame.enter_run_pc henter)
        (frame_enter_run_memory henter)

/-- One accounted block preserves stability at the covered fork its own
schedule selected. -/
private theorem AccountedBlock.stable
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain}
    (accounted : AccountedBlock cfg dp ca pre post)
    (hstable : Stable dp ca pre.state) :
    Stable dp ca post.state := by
  have hrun := accounted.transition
  rw [stateTransitionUsing] at hrun
  obtain ⟨_, _, hrun⟩ := Except.bind_eq_ok hrun
  obtain ⟨f, hf, hrun⟩ := Except.bind_eq_ok hrun
  have hfork : cfg.forkAt accounted.block.header.timestamp = .ok f :=
    Except.mapError_eq_ok_iff.mp hf
  rw [accounted.forkAt] at hfork
  cases hfork
  exact stateTransitionAt_preserves_stable dp ca accounted.fork _ _ _ hrun
    (by simpa using accounted.bound) hstable accounted.covered

/-- Accounted replay transports the checkpoint invariant to the endpoint; each
block carries the coverage of the fork its schedule selected, so no global
schedule premise is needed. -/
theorem AccountedHistory.future_stable
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future)
    (hstable : Stable dp ca checkpoint.state) :
    Stable dp ca future.state := by
  induction history with
  | refl => exact hstable
  | step _ accounted ih => exact accounted.stable ih

end Weth10

end Blanc
