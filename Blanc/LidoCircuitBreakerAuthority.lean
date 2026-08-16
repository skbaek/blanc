import Blanc.LidoCircuitBreakerSites
import Blanc.CycleWriteFree

/-!
Arbitrary-outcome runtime authority for Lido CircuitBreaker.

This module starts at canonical raw frame traversal.  Its structural theorem
does not assume that a store succeeds, commits, changes a cell, or survives
message settlement; guard and invocation-role refinements build on this exact
same-instance source cut.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

private theorem Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
    {root target : Exec.Deriv} {program : Prog}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {instruction targetInstruction : Ninst} {tail : Func}
    {initial : Exec.Deriv.SourceCursor root program
      initialPath initialSource}
    {cursor : Exec.Deriv.SourceCursor root program path
      (.next instruction tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target targetInstruction cursor)
    (instructionNe : instruction ≠ targetInstruction) :
    ∃ _chronology : Exec.Deriv.SourceCursor.Chronology
        initial cursor target,
      ∃ tailCursor : Exec.Deriv.SourceCursor root program
          ⟨path.functionIndex, path.steps ++ [.rest]⟩ tail,
        Exec.Deriv.ParentStep tailCursor.node cursor.node ∧
        Exec.Deriv.SourceCursor.Toward
          initial target targetInstruction tailCursor := by
  cases route with
  | atTarget cursor chronology site siteEq sourceMember targetEq instructionEq =>
      exact (instructionNe instructionEq).elim
  | next cursor chronology tailCursor edge rest =>
      exact ⟨chronology, tailCursor, edge, rest⟩

private theorem Exec.Deriv.SourceCursor.Toward.chronology
    {root target : Exec.Deriv} {program : Prog}
    {initialPath path : Prog.SourcePath} {initialSource source : Func}
    {targetInstruction : Ninst}
    {initial : Exec.Deriv.SourceCursor root program
      initialPath initialSource}
    {cursor : Exec.Deriv.SourceCursor root program path source}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target targetInstruction cursor) :
    Exec.Deriv.SourceCursor.Chronology initial cursor target := by
  cases route <;> assumption

private theorem Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
    {root : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {instruction : Ninst} {tail : Func}
    (cursor : Exec.Deriv.SourceCursor root program path
      (.next instruction tail))
    {tailCursor : Exec.Deriv.SourceCursor root program
      ⟨path.functionIndex, path.steps ++ [.rest]⟩ tail}
    (edge : Exec.Deriv.ParentStep tailCursor.node cursor.node) :
    Ninst.Run root.sevm cursor.pre instruction tailCursor.pre := by
  rcases cursor with
    ⟨cursorPc, cursorPre, current, parentPrefix, codeSlice,
      codeBoundary, sourceIncluded⟩
  rcases tailCursor with
    ⟨tailPc, tailPre, tailCurrent, tailPrefix, tailSlice,
      tailBoundary, tailIncluded⟩
  change Exec.Deriv.ParentStep
    ⟨tailPc, root.sevm, tailPre, root.exn, tailCurrent⟩
    ⟨cursorPc, root.sevm, cursorPre, root.exn, current⟩ at edge
  have sourceAt : Ninst.At root.sevm.code cursorPc instruction :=
    Func.sourceSites_sound codeSlice codeBoundary
      (functionIndex := path.functionIndex) (steps := path.steps)
      (site := { path := path, pc := cursorPc, instruction := instruction })
      (by rcases path with ⟨functionIndex, steps⟩
          simp [Func.sourceSites])
  cases edge with
  | cont hstep next =>
      have actual := (Evm.step_next sourceAt).symm.trans hstep
      refine ⟨.none, trivial, cursorPc, ?_⟩
      simp only [Ninst.StepRun, actual, Step.Run]
      exact ⟨trivial, trivial⟩
  | doneOk hstep henter hresume next =>
      have actual := (Evm.step_next sourceAt).symm.trans hstep
      refine ⟨.none, trivial, cursorPc, ?_⟩
      simp only [Ninst.StepRun, actual, Step.Run]
      exact ⟨_, RunFrame.of_done henter, hresume.symm⟩
  | runOk hstep henter child hresume next =>
      have actual := (Evm.step_next sourceAt).symm.trans hstep
      refine ⟨.some ⟨_, _⟩, ⟨child⟩, cursorPc, ?_⟩
      simp only [Ninst.StepRun, actual, Step.Run]
      exact ⟨_, RunFrame.of_run henter, hresume.symm⟩

private theorem Exec.Deriv.ParentPrefix.advance_pushTowardSstore
    {start target : Exec.Deriv} {xs : Bytes}
    (reached : Exec.Deriv.ParentPrefix start target)
    (pushAt : PushAt start.sevm.code start.pc xs)
    (hne : xs ≠ [])
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    ∃ (inter : Devm)
      (next : Exec (start.pc + xs.length + 1) start.sevm inter start.exn),
      Exec.Deriv.ParentStep
        ⟨start.pc + xs.length + 1, start.sevm, inter, start.exn, next⟩ start ∧
      Exec.Deriv.ParentPrefix
        ⟨start.pc + xs.length + 1, start.sevm, inter, start.exn, next⟩ target ∧
      Devm.PushBurn [xs.toB256] start.devm inter := by
  rcases start with ⟨pc, sevm, pre, out, run⟩
  rcases pushAt with ⟨le, pushAt⟩
  cases reached with
  | refl =>
      have impossible := Ninst.at_unique storeAt pushAt
      cases impossible
  | step edge rest =>
      cases edge with
      | cont hstep next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) :=
            Evm.step_next pushAt
          have sourceStep := hstatic.symm.trans hstep
          rw [Ninst.step_push, if_neg hne] at sourceStep
          obtain ⟨hpc, hrun⟩ := Step.ofExecution_cont sourceStep
          cases hpc
          exact ⟨_, next, .cont hstep next, rest,
            Devm.pushBurn_of_run hrun⟩
      | doneOk hstep henter hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) :=
            Evm.step_next pushAt
          exact (Step.ofExecution_ne_spawn (hstatic.symm.trans hstep)).elim
      | runOk hstep henter child hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) :=
            Evm.step_next pushAt
          exact (Step.ofExecution_ne_spawn (hstatic.symm.trans hstep)).elim

private theorem Exec.Deriv.ParentPrefix.advance_jumpTowardSstore
    {start target : Exec.Deriv} {instruction : Jinst}
    (reached : Exec.Deriv.ParentPrefix start target)
    (jumpAt : Jinst.At start.sevm.code start.pc instruction)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    ∃ (nextPc : Nat) (inter : Devm)
      (next : Exec nextPc start.sevm inter start.exn),
      Exec.Deriv.ParentStep
        ⟨nextPc, start.sevm, inter, start.exn, next⟩ start ∧
      Exec.Deriv.ParentPrefix
        ⟨nextPc, start.sevm, inter, start.exn, next⟩ target ∧
      Jinst.Run ⟨start.pc, start.sevm, start.devm⟩ instruction
        (.ok ⟨nextPc, inter⟩) := by
  rcases start with ⟨pc, sevm, pre, out, run⟩
  dsimp at reached storeAt jumpAt
  cases reached with
  | refl => exact (storeAt.false_of_jinstAt jumpAt).elim
  | step edge rest =>
      cases edge with
      | cont hstep next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨pc, sevm, pre⟩ instruction) :=
            Evm.step_jump jumpAt
          exact ⟨_, _, next, .cont hstep next, rest,
            Step.ofJump_cont (hstatic.symm.trans hstep)⟩
      | doneOk hstep henter hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨pc, sevm, pre⟩ instruction) :=
            Evm.step_jump jumpAt
          exact (Step.ofJump_ne_spawn (hstatic.symm.trans hstep)).elim
      | runOk hstep henter child hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨pc, sevm, pre⟩ instruction) :=
            Evm.step_jump jumpAt
          exact (Step.ofJump_ne_spawn (hstatic.symm.trans hstep)).elim

private theorem Exec.Deriv.SourceCursor.branchFlagTowardSstore
    {root target : Exec.Deriv} {program : Prog} {path : Prog.SourcePath}
    {left right : Func}
    (cursor : Exec.Deriv.SourceCursor root program path (.branch left right))
    (reached : Exec.Deriv.ParentPrefix cursor.node target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    (∃ arm : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left,
      Exec.Deriv.ParentPrefix arm.node target) ∨
    (∃ flag : B256, flag ≠ 0 ∧ [flag] <<+ cursor.pre.stack) := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, hlocEq, hloc, pushAt, jumpiAt, leftSlice, leftBoundary,
      jumpdestAt, jumpable, rightSlice, rightBoundary⟩
  rcases Exec.Deriv.ParentPrefix.advance_pushTowardSstore reached
      ⟨_, pushAt⟩ (by simp) storeAt with
    ⟨afterPushPre, afterPush, pushEdge, afterPushReached, pushBurn⟩
  rw [List.toB256_pair _ hloc] at pushBurn
  rcases Exec.Deriv.ParentPrefix.advance_jumpTowardSstore
      afterPushReached jumpiAt storeAt with
    ⟨nextPc, armPre, armExec, jumpEdge, armReached, jumpRun⟩
  rcases of_jumpi_run jumpRun with
    ⟨x, nextPcEq, popBurn⟩ | ⟨x, flag, nextPcEq, popBurn,
      actualJumpable, nonzero⟩
  · cases nextPcEq
    let armCursor : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left :=
      ⟨_, _, armExec, cursor.parentPrefix.snoc pushEdge |>.snoc jumpEdge,
        leftSlice, leftBoundary, by
          intro site member
          apply cursor.sourceIncluded
          simp only [Func.sourceSites, List.mem_append]
          exact Or.inl member⟩
    exact Or.inl ⟨armCursor, armReached⟩
  · rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
      ⟨hx, stack, pushBurn', popBurn'⟩
    have flagPop : Devm.PopBurn [flag] cursor.pre armPre :=
      Devm.popBurn_of_burn_of_popBurn
        (Devm.burn_of_pushBurn_nil pushBurn') popBurn'
    exact Or.inr ⟨flag, nonzero, pref_of_split flagPop.stack⟩

/-- A target-directed route through the heartbeat-interval setter retains the
actual `onlyAdmin` equality, its successful next edge, and the entry caller
fact.  This is deliberately local to the concrete Lido source body. -/
private theorem setHeartbeatIntervalBodyGuard
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource source : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (sourceEq : source = setHeartbeatInterval dp)
    (bodyCursor : Exec.Deriv.SourceCursor root (runtime dp) path source)
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) bodyCursor) :
    ∃ guardPath guardTail,
      ∃ guardCursor : Exec.Deriv.SourceCursor root (runtime dp)
          guardPath (.next (.reg .eq) guardTail),
        ∃ branchCursor : Exec.Deriv.SourceCursor root (runtime dp)
            ⟨guardPath.functionIndex,
              guardPath.steps ++ [.rest]⟩ guardTail,
          Exec.Deriv.SourceCursor.Chronology
              initial guardCursor target ∧
            Exec.Deriv.ParentStep branchCursor.node guardCursor.node ∧
            Ninst.Run root.sevm guardCursor.pre (.reg .eq)
              branchCursor.pre ∧
            Exec.Deriv.SourceCursor.Toward
              initial target (.reg .sstore) branchCursor ∧
            root.sevm.caller.toB256 = dp.admin := by
  subst source
  unfold setHeartbeatInterval requireStaticArgs at bodyCursor route
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
      (by intro h; cases h) with
    ⟨sizeChronology, sizeCursor, sizeEdge, sizeRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne sizeRoute
      (by intro h; cases h) with
    ⟨calldataChronology, calldataCursor, calldataEdge, calldataRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne calldataRoute
      (by intro h; cases h) with
    ⟨ltChronology, argsBranchCursor, ltEdge, argsBranchRoute⟩
  cases argsBranchRoute with
  | branchRight cursor chronology arm compilerPrefix rest =>
      exact (arm.noSstore_of_entrySstoreFree compiled [] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology rest).cursorToTarget
        targetAt).elim
  | branchLeft cursor chronology arm compilerPrefix rest =>
      unfold onlyAdmin at arm rest
      rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne rest
          (by intro h; cases h) with
        ⟨callerChronology, pushCursor, callerEdge, callerRoute⟩
      rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne callerRoute
          (by intro h; cases h) with
        ⟨pushChronology, eqCursor, pushEdge, eqRoute⟩
      rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne eqRoute
          (by intro h; cases h) with
        ⟨eqChronology, branchCursor, eqEdge, branchRoute⟩
      have callerRun :=
        Exec.Deriv.SourceCursor.ninstRun_of_nextEdge arm callerEdge
      have pushRun :=
        Exec.Deriv.SourceCursor.ninstRun_of_nextEdge pushCursor pushEdge
      have eqRun :=
        Exec.Deriv.SourceCursor.ninstRun_of_nextEdge eqCursor eqEdge
      have callerPrefix :
          [root.sevm.caller.toB256] <<+ pushCursor.pre.stack :=
        prefix_of_push (of_run_caller callerRun) nil_pref
      have adminPrefix :
          [dp.admin, root.sevm.caller.toB256] <<+ eqCursor.pre.stack := by
        simpa [pushDeployWord, B256.toB256_toBytes] using
          prefix_of_push (of_run_push pushRun) callerPrefix
      have eqPrefix :
          [(dp.admin =? root.sevm.caller.toB256)] <<+
            branchCursor.pre.stack :=
        prefix_of_eq eqRun adminPrefix
      rcases Exec.Deriv.SourceCursor.branchFlagTowardSstore branchCursor
          (Exec.Deriv.SourceCursor.Toward.chronology branchRoute).cursorToTarget
          targetAt with errorArm | ⟨flag, nonzero, flagPrefix⟩
      · rcases errorArm with ⟨errorCursor, errorReached⟩
        exact (errorCursor.noSstore_of_entrySstoreFree compiled
          [senderNotAdminErrorSlot] rfl errorReached targetAt).elim
      · have flagEq :
            (dp.admin =? root.sevm.caller.toB256) = flag :=
          pref_head_unique eqPrefix flagPrefix
        have callerEq : root.sevm.caller.toB256 = dp.admin := by
          by_contra different
          have checkZero :
              (dp.admin =? root.sevm.caller.toB256) = 0 := by
            simp [B256.eqCheck, Ne.symm different]
          exact nonzero (flagEq ▸ checkZero)
        exact ⟨_, _, eqCursor, branchCursor, eqChronology, eqEdge,
          eqRun, branchRoute, callerEq⟩

/-- Every nominated same-frame SSTORE occurrence in an exact selected runtime
frame has one unique typed source row.  The selected frame may be any raw
descendant root and may have any terminal outcome. -/
theorem Exec.NinstOccurrence.runtimePersistentWrite_of_rawFrameRoot
    {dp : DeployParams} {ca : Adr}
    {globalRoot frameRoot : Exec.Deriv}
    (occurrence : Exec.NinstOccurrence globalRoot)
    (instructionEq : occurrence.instruction = .reg .sstore)
    (selected : frameRoot ∈ Exec.rawFrameRoots globalRoot.exc)
    (invocation : frameRoot.exactInvocation (runtime dp) ca ca)
    (sameFrame : Exec.Deriv.ParentPrefix frameRoot occurrence.node) :
    ∃ row : RuntimePersistentWrite, ∃ site : Prog.SourceSite,
      row ∈ RuntimePersistentWrite.all ∧
      row.sourceSite? dp = some site ∧
      classifyRuntimePersistentWrite dp site.path site.pc = some row ∧
      site.pc = occurrence.node.pc ∧
      site.instruction = .reg .sstore ∧
      ∀ candidate : RuntimePersistentWrite,
        candidate.sourceSite? dp = some site → candidate = row := by
  rcases occurrence.sourceSite_of_rawFrameRoot instructionEq selected invocation
      sameFrame with ⟨site, sourceMember, pcEq, siteInstruction⟩
  have persistentMember : site ∈ runtimePersistentSourceSites dp := by
    unfold runtimePersistentSourceSites
    rw [List.mem_filter]
    exact ⟨sourceMember, by
      simp [siteInstruction, isPersistentWriteInstruction]⟩
  rcases runtimePersistentSourceSite_iff_row.mp persistentMember with
    ⟨row, rowMember, found⟩
  refine ⟨row, site, rowMember, found,
    classifyRuntimePersistentWrite_complete found, pcEq, siteInstruction, ?_⟩
  intro candidate candidateFound
  exact RuntimePersistentWrite.sourceSite?_injective candidateFound found

/-- Clean direct-message settlement preserves the exact committed raw world at
the CircuitBreaker owner.  This is the settlement-altitude bridge used before
retained-last-writer attribution; it does not claim raw log erasure. -/
theorem ProcessMessage.runtimeOwnerStorage_eq_committedPost
    {dp : DeployParams} {ca : Adr} {msg : Msg} {settled : Devm}
    {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out)
    (_invocation :
      (⟨0, sevm, pre, out, run⟩ : Exec.Deriv).exactInvocation
        (runtime dp) ca ca)
    (process : ProcessMessage msg
      (.some ⟨⟨0, sevm, pre⟩, out⟩) (.ok settled))
    (committed : Execution.commits out = true) :
    Devm.getStor settled ca =
      Devm.getStor (Execution.committedPost out committed) ca := by
  have stateEq :=
    ProcessMessage.ok_state_eq_committedPost process committed
  exact congrArg (fun state : State => state.getStor ca) stateEq

end Blanc.LidoCircuitBreaker
