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

/-- One actually executed nonterminal guard, retained at its exact place before
the nominated write in the selected runtime frame. -/
structure RuntimeGuardOccurrence
    (frameRoot write : Exec.Deriv) (instruction : Ninst) where
  guard : Exec.Deriv
  after : Exec.Deriv
  frameToGuard : Exec.Deriv.ParentPrefix frameRoot guard
  guardToWrite : Exec.Deriv.ParentPrefix guard write
  edge : Exec.Deriv.ParentStep after guard
  decoded : Ninst.At guard.sevm.code guard.pc instruction
  run : Ninst.Run frameRoot.sevm guard.devm instruction after.devm
  strictBefore : Exec.Deriv.lt write guard

/-- Actual selector/continuation evidence for the endpoint whose same-frame
execution reached the nominated write.  The cursor is compiler-structural and
the two prefixes are execution evidence, not a source-only path claim. -/
structure RuntimeEndpointOccurrence
    (dp : DeployParams) (frameRoot write : Exec.Deriv) (source : Func) where
  path : Prog.SourcePath
  cursor : Exec.Deriv.SourceCursor frameRoot (runtime dp) path source
  frameToCursor : Exec.Deriv.ParentPrefix frameRoot cursor.node
  cursorToWrite : Exec.Deriv.ParentPrefix cursor.node write

/-- The six runtime-accepted authority roles, each carrying its actual endpoint
and earlier guard occurrences together with the corresponding invocation-entry
fact.  The indexed role is later checked against the exact source row's
`permittedRoles`; this payload alone does not classify a source site. -/
inductive RuntimeWriteAuthority
    (dp : DeployParams) (frameRoot write : Exec.Deriv) :
    InvocationRole → Prop
  | setPauseDuration
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write
        (setPauseDuration dp))
      (guard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (callerEq : frameRoot.sevm.caller.toB256 = dp.admin) :
      RuntimeWriteAuthority dp frameRoot write .adminConfiguration
  | setHeartbeatInterval
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write
        (setHeartbeatInterval dp))
      (guard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (callerEq : frameRoot.sevm.caller.toB256 = dp.admin) :
      RuntimeWriteAuthority dp frameRoot write .adminConfiguration
  | adminRegistry
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write
        (registerPauser dp))
      (guard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (callerEq : frameRoot.sevm.caller.toB256 = dp.admin) :
      RuntimeWriteAuthority dp frameRoot write .adminRegistry
  | adminExpiry
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write
        (registerPauser dp))
      (guard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (callerEq : frameRoot.sevm.caller.toB256 = dp.admin) :
      RuntimeWriteAuthority dp frameRoot write .adminExpiry
  | heartbeatExpiry
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write heartbeat)
      (registeredGuard : RuntimeGuardOccurrence frameRoot write
        (.reg .iszero))
      (liveGuard : RuntimeGuardOccurrence frameRoot write (.reg .lt))
      (registered : frameRoot.devm.getStorVal
        frameRoot.sevm.currentTarget
        (countSlot frameRoot.sevm.caller.toB256) ≠ 0)
      (live : frameRoot.sevm.benvStat.time < frameRoot.devm.getStorVal
        frameRoot.sevm.currentTarget
        (expirySlot frameRoot.sevm.caller.toB256)) :
      RuntimeWriteAuthority dp frameRoot write .heartbeatExpiry
  | pauseRegistry
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write pause)
      (assignedGuard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (liveGuard : RuntimeGuardOccurrence frameRoot write (.reg .lt))
      (assigned : frameRoot.devm.getStorVal
        frameRoot.sevm.currentTarget
        (assignmentSlot (Sevm.dataWord frameRoot.sevm 4)) =
          frameRoot.sevm.caller.toB256)
      (live : frameRoot.sevm.benvStat.time < frameRoot.devm.getStorVal
        frameRoot.sevm.currentTarget
        (expirySlot frameRoot.sevm.caller.toB256)) :
      RuntimeWriteAuthority dp frameRoot write .pauseRegistry
  | pauseExpiry
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write pause)
      (assignedGuard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (liveGuard : RuntimeGuardOccurrence frameRoot write (.reg .lt))
      (assigned : frameRoot.devm.getStorVal
        frameRoot.sevm.currentTarget
        (assignmentSlot (Sevm.dataWord frameRoot.sevm 4)) =
          frameRoot.sevm.caller.toB256)
      (live : frameRoot.sevm.benvStat.time < frameRoot.devm.getStorVal
        frameRoot.sevm.currentTarget
        (expirySlot frameRoot.sevm.caller.toB256)) :
      RuntimeWriteAuthority dp frameRoot write .pauseExpiry

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

/-- An exact internal-call cut retained on the target-directed source route. -/
private inductive Exec.Deriv.SourceCursor.Toward.CallCut
    {root target : Exec.Deriv} {program : Prog}
    {initialPath : Prog.SourcePath} {initialSource : Func}
    {targetInstruction : Ninst}
    (initial : Exec.Deriv.SourceCursor root program
      initialPath initialSource)
    (functionIndex : Nat) : Prop
  | intro (path : Prog.SourcePath)
      (cursor : Exec.Deriv.SourceCursor root program path
        (.call functionIndex))
      (body : Func)
      (lookup : (program.main :: program.aux)[functionIndex]? = some body)
      (bodyCursor : Exec.Deriv.SourceCursor root program
        ⟨functionIndex, []⟩ body)
      (routeToCall : Exec.Deriv.SourceCursor.Toward
        initial target targetInstruction cursor)
      (routeFromBody : Exec.Deriv.SourceCursor.Toward
        initial target targetInstruction bodyCursor) :
      Exec.Deriv.SourceCursor.Toward.CallCut initial functionIndex

/-- The terminal source cursor of a target-directed route, together with an
exact call cut whenever its function differs from the current one. -/
private theorem Exec.Deriv.SourceCursor.Toward.atTargetData
    {root target : Exec.Deriv} {program : Prog}
    {initialPath path : Prog.SourcePath} {initialSource source : Func}
    {targetInstruction : Ninst}
    {initial : Exec.Deriv.SourceCursor root program
      initialPath initialSource}
    {cursor : Exec.Deriv.SourceCursor root program path source}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target targetInstruction cursor) :
    ∃ finalPath finalTail,
      ∃ finalCursor : Exec.Deriv.SourceCursor root program finalPath
          (.next targetInstruction finalTail),
        finalCursor.node = target ∧
        ({ path := finalPath, pc := finalCursor.pc,
            instruction := targetInstruction } : Prog.SourceSite) ∈
          program.sourceSites ∧
        (path.functionIndex = finalPath.functionIndex ∨
          Exec.Deriv.SourceCursor.Toward.CallCut
            (target := target) (targetInstruction := targetInstruction)
            initial finalPath.functionIndex) := by
  induction route with
  | atTarget cursor chronology site siteEq sourceMember targetEq instructionEq =>
      cases instructionEq
      exact ⟨_, _, cursor, targetEq,
        by simpa [siteEq] using sourceMember, Or.inl rfl⟩
  | next cursor chronology tailCursor edge rest ih => exact ih
  | branchLeft cursor chronology arm compilerPrefix rest ih => exact ih
  | branchRight cursor chronology arm compilerPrefix rest ih => exact ih
  | call cursor chronology lookup bodyCursor compilerPrefix rest ih =>
      rcases ih with
        ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
          sameFunction | deeperCut⟩
      · refine ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
          Or.inr ?_⟩
        rw [← sameFunction]
        exact .intro _ cursor _ lookup bodyCursor
          (.call cursor chronology lookup bodyCursor compilerPrefix rest) rest
      · exact ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
          Or.inr deeperCut⟩

/-- Either the target lies in a different function, or the route contains the
exact internal call to the nominated target function. -/
private theorem Exec.Deriv.SourceCursor.Toward.callCut_of_targetFunction
    {root target : Exec.Deriv} {program : Prog}
    {initialPath path : Prog.SourcePath} {initialSource source : Func}
    {targetInstruction : Ninst}
    {initial : Exec.Deriv.SourceCursor root program
      initialPath initialSource}
    {cursor : Exec.Deriv.SourceCursor root program path source}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target targetInstruction cursor)
    (targetFunction : Nat)
    (currentNe : path.functionIndex ≠ targetFunction) :
    (∃ finalPath finalTail,
      ∃ finalCursor : Exec.Deriv.SourceCursor root program finalPath
          (.next targetInstruction finalTail),
        finalCursor.node = target ∧
        ({ path := finalPath, pc := finalCursor.pc,
            instruction := targetInstruction } : Prog.SourceSite) ∈
          program.sourceSites ∧
        finalPath.functionIndex ≠ targetFunction) ∨
      Exec.Deriv.SourceCursor.Toward.CallCut
        (target := target) (targetInstruction := targetInstruction)
        initial targetFunction := by
  rcases Exec.Deriv.SourceCursor.Toward.atTargetData route with
    ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
      sameFunction | targetCut⟩
  · exact Or.inl ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
      fun finalEq => currentNe (sameFunction.trans finalEq)⟩
  · by_cases finalEq : finalPath.functionIndex = targetFunction
    · exact Or.inr (finalEq ▸ targetCut)
    · exact Or.inl ⟨finalPath, finalTail, finalCursor, targetEq,
        sourceMember, finalEq⟩

private def RuntimePersistentWrite.sourceFunctionIndex :
    RuntimePersistentWrite → Nat
  | .setPauseDurationConfig | .setHeartbeatIntervalConfig
  | .heartbeatExpiry => 0
  | .setPauserAssignment | .setPauserOldCount => 14
  | .appendArrayEntry | .appendReverseIndex | .appendArrayLength => 15
  | .afterOldNewCount => 16
  | .removeArrayHole | .removeMovedIndex | .removeClearTail
  | .removeArrayLength | .removeClearTargetIndex => 17
  | .registerFreshExpiry | .registerLastOldClear
  | .registerLastOldNewExpiry | .registerRetainedOldNewExpiry => 19
  | .pauseLastTargetExpiry | .pauseRetainedTargetExpiry => 20

private theorem RuntimePersistentWrite.sourceSite?_functionIndex
    {dp : DeployParams} {row : RuntimePersistentWrite}
    {site : Prog.SourceSite}
    (found : row.sourceSite? dp = some site) :
    site.path.functionIndex = row.sourceFunctionIndex := by
  have sitesEq := runtimePersistentSourceSites_eq_official dp
  unfold RuntimePersistentWrite.sourceSite? at found
  rw [sitesEq] at found
  cases row <;> decide +kernel +revert

private theorem runtimePersistentSourceSite_eq_of_pc
    {dp : DeployParams} {left right : Prog.SourceSite}
    (leftMem : left ∈ runtimePersistentSourceSites dp)
    (rightMem : right ∈ runtimePersistentSourceSites dp)
    (pcEq : left.pc = right.pc) :
    left = right := by
  have sitesNodup := runtimePersistentSourceSites_nodup dp
  have pcsNodup :
      ((runtimePersistentSourceSites dp).map fun site => site.pc).Nodup := by
    rw [runtimePersistentSourceSites_pcs]
    decide
  exact (List.nodup_map_iff_inj_on sitesNodup).mp pcsNodup
    left leftMem right rightMem pcEq

private theorem Exec.Deriv.SourceCursor.Toward.dropLine
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {line : Line} {tail : Func}
    {cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (line +++ tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (lineNe : ∀ instruction ∈ line,
      instruction ≠ (.reg .sstore)) :
    ∃ tailPath,
      ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
          tailPath tail,
        Exec.Deriv.SourceCursor.Chronology
            initial tailCursor target ∧
          Exec.Deriv.SourceCursor.Toward
            initial target (.reg .sstore) tailCursor := by
  induction line generalizing path with
  | nil => exact ⟨path, cursor,
      Exec.Deriv.SourceCursor.Toward.chronology route, route⟩
  | cons instruction rest ih =>
      change Exec.Deriv.SourceCursor root (runtime dp) path
        (.next instruction (rest +++ tail)) at cursor
      rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
          (lineNe instruction (by simp)) with
        ⟨chronology, restCursor, edge, restRoute⟩
      exact ih restRoute (fun candidate member =>
        lineNe candidate (by simp [member]))

/-- Drop a source line while retaining the exact structural path reached after
its sequence of `.rest` descents. -/
private theorem Exec.Deriv.SourceCursor.Toward.dropLineExact
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {line : Line} {tail : Func}
    {cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (line +++ tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (lineNe : ∀ instruction ∈ line,
      instruction ≠ (.reg .sstore)) :
    ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex,
          path.steps ++ List.replicate line.length .rest⟩ tail,
      Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) tailCursor := by
  induction line generalizing path with
  | nil =>
      have stepsEq : path.steps =
          path.steps ++ List.replicate ([] : Line).length .rest := by
        simp
      rw [← stepsEq]
      exact ⟨cursor, route⟩
  | cons instruction rest ih =>
      change Exec.Deriv.SourceCursor root (runtime dp) path
        (.next instruction (rest +++ tail)) at cursor
      rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
          (lineNe instruction (by simp)) with
        ⟨chronology, restCursor, edge, restRoute⟩
      rcases ih restRoute (fun candidate member =>
          lineNe candidate (by simp [member])) with
        ⟨tailCursor, tailRoute⟩
      have stepsEq :
          (path.steps ++ [.rest]) ++
              List.replicate rest.length .rest =
            path.steps ++
              List.replicate (instruction :: rest).length .rest := by
        simp [List.replicate_succ, List.append_assoc]
      rw [← stepsEq]
      exact ⟨tailCursor, tailRoute⟩

private theorem Exec.Deriv.SourceCursor.instructionAt
    {root : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {instruction : Ninst} {tail : Func}
    (cursor : Exec.Deriv.SourceCursor root program path
      (.next instruction tail)) :
    Ninst.At root.sevm.code cursor.pc instruction := by
  rcases cursor with
    ⟨cursorPc, cursorPre, current, parentPrefix, codeSlice,
      codeBoundary, sourceIncluded⟩
  exact Func.sourceSites_sound codeSlice codeBoundary
    (functionIndex := path.functionIndex) (steps := path.steps)
    (site := { path := path, pc := cursorPc, instruction := instruction })
    (by rcases path with ⟨functionIndex, steps⟩
        simp [Func.sourceSites])

private theorem parentPrefixTrans
    {root middle tail : Exec.Deriv}
    (left : Exec.Deriv.ParentPrefix root middle)
    (right : Exec.Deriv.ParentPrefix middle tail) :
    Exec.Deriv.ParentPrefix root tail := by
  induction left with
  | refl => exact right
  | step head rest ih => exact .step head (ih right)

/-- Rebase a target-directed route onto an earlier cursor in the same frame. -/
private theorem Exec.Deriv.SourceCursor.Toward.rebase
    {root target : Exec.Deriv} {program : Prog}
    {originPath basePath path : Prog.SourcePath}
    {originSource baseSource source : Func}
    {targetInstruction : Ninst}
    {origin : Exec.Deriv.SourceCursor root program originPath originSource}
    {base : Exec.Deriv.SourceCursor root program basePath baseSource}
    {cursor : Exec.Deriv.SourceCursor root program path source}
    (originToBase : Exec.Deriv.ParentPrefix origin.node base.node)
    (route : Exec.Deriv.SourceCursor.Toward
      base target targetInstruction cursor) :
    Exec.Deriv.SourceCursor.Toward
      origin target targetInstruction cursor := by
  induction route with
  | atTarget cursor chronology site siteEq sourceMember targetEq instructionEq =>
      exact .atTarget cursor
        ⟨parentPrefixTrans originToBase chronology.initialToCursor,
          chronology.cursorToTarget⟩
        site siteEq sourceMember targetEq instructionEq
  | next cursor chronology tailCursor edge rest ih =>
      exact .next cursor
        ⟨parentPrefixTrans originToBase chronology.initialToCursor,
          chronology.cursorToTarget⟩
        tailCursor edge ih
  | branchLeft cursor chronology arm compilerPrefix rest ih =>
      exact .branchLeft cursor
        ⟨parentPrefixTrans originToBase chronology.initialToCursor,
          chronology.cursorToTarget⟩
        arm compilerPrefix ih
  | branchRight cursor chronology arm compilerPrefix rest ih =>
      exact .branchRight cursor
        ⟨parentPrefixTrans originToBase chronology.initialToCursor,
          chronology.cursorToTarget⟩
        arm compilerPrefix ih
  | call cursor chronology lookup bodyCursor compilerPrefix rest ih =>
      exact .call cursor
        ⟨parentPrefixTrans originToBase chronology.initialToCursor,
          chronology.cursorToTarget⟩
        lookup bodyCursor compilerPrefix ih

private def RuntimeGuardOccurrence.ofCursor
    {frameRoot write : Exec.Deriv} {dp : DeployParams}
    {initialPath guardPath : Prog.SourcePath}
    {initialSource tail : Func} {instruction : Ninst}
    {initial : Exec.Deriv.SourceCursor frameRoot (runtime dp)
      initialPath initialSource}
    {guardCursor : Exec.Deriv.SourceCursor frameRoot (runtime dp)
      guardPath (.next instruction tail)}
    {afterCursor : Exec.Deriv.SourceCursor frameRoot (runtime dp)
      ⟨guardPath.functionIndex, guardPath.steps ++ [.rest]⟩ tail}
    (frameToInitial : Exec.Deriv.ParentPrefix frameRoot initial.node)
    (chronology : Exec.Deriv.SourceCursor.Chronology
      initial guardCursor write)
    (edge : Exec.Deriv.ParentStep afterCursor.node guardCursor.node)
    (run : Ninst.Run frameRoot.sevm guardCursor.pre instruction
      afterCursor.pre)
    (targetAt : Ninst.At write.sevm.code write.pc (.reg .sstore))
    (instructionNe : instruction ≠ (.reg .sstore)) :
    RuntimeGuardOccurrence frameRoot write instruction := by
  have decoded := Exec.Deriv.SourceCursor.instructionAt guardCursor
  have distinct : guardCursor.node ≠ write := by
    intro equal
    change Ninst.At guardCursor.node.sevm.code guardCursor.node.pc
      instruction at decoded
    rw [equal] at decoded
    exact instructionNe (Ninst.at_unique decoded targetAt)
  exact
    { guard := guardCursor.node
      after := afterCursor.node
      frameToGuard := parentPrefixTrans frameToInitial chronology.initialToCursor
      guardToWrite := chronology.cursorToTarget
      edge := edge
      decoded := decoded
      run := run
      strictBefore := chronology.strictBefore distinct }

private def RuntimeEndpointOccurrence.ofCursor
    {frameRoot write : Exec.Deriv} {dp : DeployParams}
    {initialPath endpointPath : Prog.SourcePath}
    {initialSource source : Func}
    {initial : Exec.Deriv.SourceCursor frameRoot (runtime dp)
      initialPath initialSource}
    (frameToInitial : Exec.Deriv.ParentPrefix frameRoot initial.node)
    (endpointCursor : Exec.Deriv.SourceCursor frameRoot (runtime dp)
      endpointPath source)
    (route : Exec.Deriv.SourceCursor.Toward
      initial write (.reg .sstore) endpointCursor) :
    RuntimeEndpointOccurrence dp frameRoot write source :=
  let chronology := Exec.Deriv.SourceCursor.Toward.chronology route
  { path := endpointPath
    cursor := endpointCursor
    frameToCursor := parentPrefixTrans frameToInitial chronology.initialToCursor
    cursorToWrite := chronology.cursorToTarget }

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

/-- Drop one source line while retaining its exact instruction run. -/
private theorem Exec.Deriv.SourceCursor.Toward.dropLineRun
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {line : Line} {tail : Func}
    {cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (line +++ tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (lineNe : ∀ instruction ∈ line,
      instruction ≠ (.reg .sstore)) :
    ∃ tailPath,
      ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
          tailPath tail,
        Line.Run root.sevm cursor.pre line tailCursor.pre ∧
          Exec.Deriv.SourceCursor.Chronology
              initial tailCursor target ∧
            Exec.Deriv.SourceCursor.Toward
              initial target (.reg .sstore) tailCursor := by
  induction line generalizing path with
  | nil =>
      exact ⟨path, cursor, Line.Run.nil,
        Exec.Deriv.SourceCursor.Toward.chronology route, route⟩
  | cons instruction rest ih =>
      change Exec.Deriv.SourceCursor root (runtime dp) path
        (.next instruction (rest +++ tail)) at cursor
      rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
          (lineNe instruction (by simp)) with
        ⟨chronology, restCursor, edge, restRoute⟩
      rcases ih restRoute (fun candidate member =>
          lineNe candidate (by simp [member])) with
        ⟨tailPath, tailCursor, lineRun, tailChronology, tailRoute⟩
      exact ⟨tailPath, tailCursor,
        Line.Run.cons
          (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge cursor edge)
          lineRun,
        tailChronology, tailRoute⟩

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
      Exec.Deriv.ParentPrefix cursor.node arm.node ∧
        Exec.Deriv.ParentPrefix arm.node target ∧
          [(0 : B256)] <<+ cursor.pre.stack ∧
            Devm.getStor cursor.pre = Devm.getStor arm.pre) ∨
    (∃ flag : B256, flag ≠ 0 ∧ [flag] <<+ cursor.pre.stack ∧
      ∃ arm : Exec.Deriv.SourceCursor root program
          ⟨path.functionIndex, path.steps ++ [.branchRight]⟩ right,
        Exec.Deriv.ParentPrefix cursor.node arm.node ∧
          Exec.Deriv.ParentPrefix arm.node target ∧
            Devm.getStor cursor.pre = Devm.getStor arm.pre) := by
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
    rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
      ⟨hx, stack, pushBurn', popBurn'⟩
    have zeroPop : Devm.PopBurn [(0 : B256)] cursor.pre armPre :=
      Devm.popBurn_of_burn_of_popBurn
        (Devm.burn_of_pushBurn_nil pushBurn') popBurn'
    exact Or.inl ⟨armCursor,
      .step pushEdge (.step jumpEdge (.refl _)), armReached,
      pref_of_split zeroPop.stack, PopBurn.Inv.inv zeroPop⟩
  · have hloc256 : loc < 2 ^ 256 := by
      apply Nat.lt_trans hloc
      rw [Nat.pow_lt_pow_iff_right] <;> omega
    have hxeq : loc = x.toNat := by
      rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
        ⟨hx, stack, pushBurn', popBurn'⟩
      have hlocToNat : loc.toB256.toNat = loc :=
        B256.toNat_toB256_of_lt hloc256
      rw [← congrArg B256.toNat hx, hlocToNat]
    have nextPcLoc : nextPc = loc := nextPcEq.trans hxeq.symm
    cases nextPcLoc
    rcases Exec.Deriv.ParentPrefix.advance_jumpTowardSstore
        armReached jumpdestAt storeAt with
      ⟨bodyPc, bodyPre, bodyExec, jumpdestEdge, bodyReached,
        jumpdestRun⟩
    rcases of_jumpdest_run jumpdestRun with ⟨bodyPcEq, jumpdestBurn⟩
    subst bodyPc
    let armCursor : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.branchRight]⟩ right :=
      ⟨_, _, bodyExec,
        cursor.parentPrefix.snoc pushEdge |>.snoc jumpEdge
          |>.snoc jumpdestEdge,
        rightSlice, rightBoundary, by
          intro site member
          apply cursor.sourceIncluded
          simp only [Func.sourceSites, List.mem_append]
          apply Or.inr
          have hrightPc : loc + 1 = cursor.pc + compsize left + 5 := by
            omega
          rw [← hrightPc]
          exact member⟩
    rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
      ⟨hx, stack, pushBurn', popBurn'⟩
    have flagPop : Devm.PopBurn [flag] cursor.pre armPre :=
      Devm.popBurn_of_burn_of_popBurn
        (Devm.burn_of_pushBurn_nil pushBurn') popBurn'
    exact Or.inr ⟨flag, nonzero, pref_of_split flagPop.stack,
      armCursor,
      .step pushEdge (.step jumpEdge (.step jumpdestEdge (.refl _))),
      bodyReached,
      (PopBurn.Inv.inv flagPop).trans (Burn.Inv.inv jumpdestBurn)⟩

/-- Select the actually executed branch arm, preserving both its rebased route
and the storage equality across compiler glue. -/
private theorem Exec.Deriv.SourceCursor.Toward.branchArmStorage
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource left right : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (.branch left right))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    (∃ arm : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left,
      Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) arm ∧
        Devm.getStor cursor.pre = Devm.getStor arm.pre ∧
          [(0 : B256)] <<+ cursor.pre.stack) ∨
    (∃ flag : B256, flag ≠ 0 ∧ [flag] <<+ cursor.pre.stack ∧
      ∃ arm : Exec.Deriv.SourceCursor root (runtime dp)
          ⟨path.functionIndex, path.steps ++ [.branchRight]⟩ right,
        Exec.Deriv.SourceCursor.Toward
            initial target (.reg .sstore) arm ∧
          Devm.getStor cursor.pre = Devm.getStor arm.pre) := by
  let chronology := Exec.Deriv.SourceCursor.Toward.chronology route
  rcases Exec.Deriv.SourceCursor.branchFlagTowardSstore cursor
      chronology.cursorToTarget targetAt with
    ⟨arm, branchToArm, armReached, zeroPrefix, storage⟩ |
      ⟨flag, nonzero, flagPrefix, arm, branchToArm, armReached, storage⟩
  · have localRoute := arm.toward compiled armReached (by trivial) targetAt
    exact Or.inl ⟨arm,
      Exec.Deriv.SourceCursor.Toward.rebase
        (parentPrefixTrans chronology.initialToCursor branchToArm) localRoute,
      storage, zeroPrefix⟩
  · have localRoute := arm.toward compiled armReached (by trivial) targetAt
    exact Or.inr ⟨flag, nonzero, flagPrefix, arm,
      Exec.Deriv.SourceCursor.Toward.rebase
        (parentPrefixTrans chronology.initialToCursor branchToArm) localRoute,
      storage⟩

private theorem linearDispatchWith_bodyCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (entries : List (B256 × Func)) {path : Prog.SourcePath}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (linearDispatchWith fallbackSlot entries))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ word body,
      (word, body) ∈ entries ∧
        ∃ bodyPath,
          ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
              bodyPath body,
            Exec.Deriv.SourceCursor.Toward
              initial target (.reg .sstore) bodyCursor := by
  induction entries generalizing path with
  | nil =>
      exact (cursor.noSstore_of_entrySstoreFree compiled
        [fallbackSlot] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology route).cursorToTarget
        targetAt).elim
  | cons head tail ih =>
      rcases head with ⟨word, body⟩
      cases tail with
      | nil =>
          unfold linearDispatchWith at cursor
          rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
              (by intro h; cases h) with
            ⟨pushChronology, eqCursor, pushEdge, eqRoute⟩
          rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne eqRoute
              (by intro h; cases h) with
            ⟨eqChronology, branchCursor, eqEdge, branchRoute⟩
          cases branchRoute with
          | branchLeft branchCursor chronology arm compilerPrefix rest =>
              exact (arm.noSstore_of_entrySstoreFree compiled
                [fallbackSlot] rfl
                (Exec.Deriv.SourceCursor.Toward.chronology rest).cursorToTarget
                targetAt).elim
          | branchRight branchCursor chronology arm compilerPrefix rest =>
              exact ⟨word, body, by simp, _, arm, rest⟩
      | cons next rest =>
          unfold linearDispatchWith at cursor
          rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
              (by intro h; cases h) with
            ⟨dupChronology, pushCursor, dupEdge, pushRoute⟩
          rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne pushRoute
              (by intro h; cases h) with
            ⟨pushChronology, eqCursor, pushEdge, eqRoute⟩
          rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne eqRoute
              (by intro h; cases h) with
            ⟨eqChronology, branchCursor, eqEdge, branchRoute⟩
          cases branchRoute with
          | branchLeft branchCursor chronology arm compilerPrefix tailRoute =>
              rcases ih arm tailRoute with
                ⟨selectedWord, selectedBody, member, cut⟩
              exact ⟨selectedWord, selectedBody, by simp [member], cut⟩
          | branchRight branchCursor chronology arm compilerPrefix bodyRoute =>
              rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
                  bodyRoute (by intro h; cases h) with
                ⟨popChronology, bodyCursor, popEdge, restRoute⟩
              exact ⟨word, body, by simp, _, bodyCursor, restRoute⟩

private theorem linearDispatchWith_bodyCutStorage
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (entries : List (B256 × Func)) {path : Prog.SourcePath}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (linearDispatchWith fallbackSlot entries))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ word body,
      (word, body) ∈ entries ∧
        ∃ bodyPath,
          ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
              bodyPath body,
            Exec.Deriv.SourceCursor.Toward
                initial target (.reg .sstore) bodyCursor ∧
              Devm.getStor cursor.pre = Devm.getStor bodyCursor.pre := by
  induction entries generalizing path with
  | nil =>
      exact (cursor.noSstore_of_entrySstoreFree compiled
        [fallbackSlot] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology route).cursorToTarget
        targetAt).elim
  | cons head tail ih =>
      rcases head with ⟨word, body⟩
      cases tail with
      | nil =>
          let entryCursor := cursor
          rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
              (by intro h; cases h) with
            ⟨pushChronology, eqCursor, pushEdge, eqRoute⟩
          rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne eqRoute
              (by intro h; cases h) with
            ⟨eqChronology, branchCursor, eqEdge, branchRoute⟩
          have pushRun :=
            Exec.Deriv.SourceCursor.ninstRun_of_nextEdge entryCursor pushEdge
          have eqRun :=
            Exec.Deriv.SourceCursor.ninstRun_of_nextEdge eqCursor eqEdge
          have prefixStorage :
              Devm.getStor entryCursor.pre = Devm.getStor branchCursor.pre :=
            Line.of_inv Devm.getStor (by line_inv)
              (Line.Run.cons pushRun (Line.Run.cons eqRun Line.Run.nil))
          rcases Exec.Deriv.SourceCursor.Toward.branchArmStorage
              branchCursor compiled targetAt branchRoute with
            ⟨fallbackCursor, fallbackRoute, branchStorage, zeroPrefix⟩ |
              ⟨flag, nonzero, flagPrefix, bodyCursor, bodyRoute,
                branchStorage⟩
          · exact (fallbackCursor.noSstore_of_entrySstoreFree compiled
              [fallbackSlot] rfl
              (Exec.Deriv.SourceCursor.Toward.chronology
                fallbackRoute).cursorToTarget targetAt).elim
          · exact ⟨word, body, by simp, _, bodyCursor, bodyRoute,
              prefixStorage.trans branchStorage⟩
      | cons next rest =>
          let entryCursor := cursor
          rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
              (by intro h; cases h) with
            ⟨dupChronology, pushCursor, dupEdge, pushRoute⟩
          rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne pushRoute
              (by intro h; cases h) with
            ⟨pushChronology, eqCursor, pushEdge, eqRoute⟩
          rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne eqRoute
              (by intro h; cases h) with
            ⟨eqChronology, branchCursor, eqEdge, branchRoute⟩
          have dupRun :=
            Exec.Deriv.SourceCursor.ninstRun_of_nextEdge entryCursor dupEdge
          have pushRun :=
            Exec.Deriv.SourceCursor.ninstRun_of_nextEdge pushCursor pushEdge
          have eqRun :=
            Exec.Deriv.SourceCursor.ninstRun_of_nextEdge eqCursor eqEdge
          have prefixStorage :
              Devm.getStor entryCursor.pre = Devm.getStor branchCursor.pre :=
            Line.of_inv Devm.getStor (by line_inv)
              (Line.Run.cons dupRun
                (Line.Run.cons pushRun (Line.Run.cons eqRun Line.Run.nil)))
          rcases Exec.Deriv.SourceCursor.Toward.branchArmStorage
              branchCursor compiled targetAt branchRoute with
            ⟨tailCursor, tailRoute, branchStorage, zeroPrefix⟩ |
              ⟨flag, nonzero, flagPrefix, selectedCursor, selectedRoute,
                branchStorage⟩
          · rcases ih tailCursor tailRoute with
              ⟨selectedWord, selectedBody, member, bodyPath, bodyCursor,
                bodyRoute, tailStorage⟩
            exact ⟨selectedWord, selectedBody, by simp [member], bodyPath,
              bodyCursor, bodyRoute,
              prefixStorage.trans (branchStorage.trans tailStorage)⟩
          · rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
                selectedRoute (by intro h; cases h) with
              ⟨popChronology, bodyCursor, popEdge, bodyRoute⟩
            have popRun :=
              Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
                selectedCursor popEdge
            have popStorage : Devm.getStor selectedCursor.pre =
                Devm.getStor bodyCursor.pre :=
              Line.of_inv Devm.getStor (by line_inv)
                (Line.Run.cons popRun Line.Run.nil)
            exact ⟨word, body, by simp, _, bodyCursor, bodyRoute,
              prefixStorage.trans (branchStorage.trans popStorage)⟩

private theorem splitDispatch_bodyCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {pivot : B256} {left right : Func}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (splitDispatch pivot left right))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    (∃ leftPath,
      ∃ leftCursor : Exec.Deriv.SourceCursor root (runtime dp)
          leftPath left,
        Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) leftCursor) ∨
    (∃ rightPath,
      ∃ rightCursor : Exec.Deriv.SourceCursor root (runtime dp)
          rightPath right,
        Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) rightCursor) := by
  unfold splitDispatch at cursor
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
      (by intro h; cases h) with
    ⟨dupChronology, pushCursor, dupEdge, pushRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne pushRoute
      (by intro h; cases h) with
    ⟨pushChronology, gtCursor, pushEdge, gtRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne gtRoute
      (by intro h; cases h) with
    ⟨gtChronology, branchCursor, gtEdge, branchRoute⟩
  cases branchRoute with
  | branchLeft branchCursor chronology arm compilerPrefix rest =>
      exact Or.inr ⟨_, arm, rest⟩
  | branchRight branchCursor chronology arm compilerPrefix rest =>
      exact Or.inl ⟨_, arm, rest⟩

private theorem splitDispatch_bodyCutStorage
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {pivot : B256} {left right : Func}
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (splitDispatch pivot left right))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    (∃ leftPath,
      ∃ leftCursor : Exec.Deriv.SourceCursor root (runtime dp)
          leftPath left,
        Exec.Deriv.SourceCursor.Toward
            initial target (.reg .sstore) leftCursor ∧
          Devm.getStor cursor.pre = Devm.getStor leftCursor.pre) ∨
    (∃ rightPath,
      ∃ rightCursor : Exec.Deriv.SourceCursor root (runtime dp)
          rightPath right,
        Exec.Deriv.SourceCursor.Toward
            initial target (.reg .sstore) rightCursor ∧
          Devm.getStor cursor.pre = Devm.getStor rightCursor.pre) := by
  let entryCursor := cursor
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
      (by intro h; cases h) with
    ⟨dupChronology, pushCursor, dupEdge, pushRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne pushRoute
      (by intro h; cases h) with
    ⟨pushChronology, gtCursor, pushEdge, gtRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne gtRoute
      (by intro h; cases h) with
    ⟨gtChronology, branchCursor, gtEdge, branchRoute⟩
  have dupRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge entryCursor dupEdge
  have pushRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge pushCursor pushEdge
  have gtRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge gtCursor gtEdge
  have prefixStorage :
      Devm.getStor entryCursor.pre = Devm.getStor branchCursor.pre :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons dupRun
        (Line.Run.cons pushRun (Line.Run.cons gtRun Line.Run.nil)))
  rcases Exec.Deriv.SourceCursor.Toward.branchArmStorage
      branchCursor compiled targetAt branchRoute with
    ⟨rightCursor, rightRoute, branchStorage, zeroPrefix⟩ |
      ⟨flag, nonzero, flagPrefix, leftCursor, leftRoute, branchStorage⟩
  · exact Or.inr ⟨_, rightCursor, rightRoute,
      prefixStorage.trans branchStorage⟩
  · exact Or.inl ⟨_, leftCursor, leftRoute,
      prefixStorage.trans branchStorage⟩

private theorem hybridDispatchWith_bodyCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (hybridDispatchWith fallbackSlot (funcs dp)))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ word body,
      (word, body) ∈ funcs dp ∧
        ∃ bodyPath,
          ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
              bodyPath body,
            Exec.Deriv.SourceCursor.Toward
              initial target (.reg .sstore) bodyCursor := by
  unfold hybridDispatchWith at cursor
  rcases splitDispatch_bodyCut cursor route with
    ⟨leftPath, leftCursor, leftRoute⟩ |
      ⟨rightPath, rightCursor, rightRoute⟩
  · rcases splitDispatch_bodyCut leftCursor leftRoute with
      ⟨firstPath, firstCursor, firstRoute⟩ |
        ⟨secondPath, secondCursor, secondRoute⟩
    · rcases linearDispatchWith_bodyCut compiled targetAt
          ((funcs dp).take 5) firstCursor firstRoute with
        ⟨word, body, member, bodyPath, bodyCursor, bodyRoute⟩
      exact ⟨word, body, List.mem_of_mem_take member,
        bodyPath, bodyCursor, bodyRoute⟩
    · rcases linearDispatchWith_bodyCut compiled targetAt
          ((funcs dp).drop 5 |>.take 4) secondCursor secondRoute with
        ⟨word, body, member, bodyPath, bodyCursor, bodyRoute⟩
      have memberDrop : (word, body) ∈ (funcs dp).drop 5 :=
        List.mem_of_mem_take member
      exact ⟨word, body, List.mem_of_mem_drop memberDrop,
        bodyPath, bodyCursor, bodyRoute⟩
  · rcases splitDispatch_bodyCut rightCursor rightRoute with
      ⟨thirdPath, thirdCursor, thirdRoute⟩ |
        ⟨fourthPath, fourthCursor, fourthRoute⟩
    · rcases linearDispatchWith_bodyCut compiled targetAt
          ((funcs dp).drop 9 |>.take 4) thirdCursor thirdRoute with
        ⟨word, body, member, bodyPath, bodyCursor, bodyRoute⟩
      have memberDrop : (word, body) ∈ (funcs dp).drop 9 :=
        List.mem_of_mem_take member
      exact ⟨word, body, List.mem_of_mem_drop memberDrop,
        bodyPath, bodyCursor, bodyRoute⟩
    · rcases linearDispatchWith_bodyCut compiled targetAt
          ((funcs dp).drop 13) fourthCursor fourthRoute with
        ⟨word, body, member, bodyPath, bodyCursor, bodyRoute⟩
      exact ⟨word, body, List.mem_of_mem_drop member,
        bodyPath, bodyCursor, bodyRoute⟩

private theorem hybridDispatchWith_bodyCutStorage
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (hybridDispatchWith fallbackSlot (funcs dp)))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ word body,
      (word, body) ∈ funcs dp ∧
        ∃ bodyPath,
          ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
              bodyPath body,
            Exec.Deriv.SourceCursor.Toward
                initial target (.reg .sstore) bodyCursor ∧
              Devm.getStor cursor.pre = Devm.getStor bodyCursor.pre := by
  rcases splitDispatch_bodyCutStorage compiled targetAt cursor route with
    ⟨leftPath, leftCursor, leftRoute, rootToLeft⟩ |
      ⟨rightPath, rightCursor, rightRoute, rootToRight⟩
  · rcases splitDispatch_bodyCutStorage compiled targetAt
        leftCursor leftRoute with
      ⟨firstPath, firstCursor, firstRoute, leftToFirst⟩ |
        ⟨secondPath, secondCursor, secondRoute, leftToSecond⟩
    · rcases linearDispatchWith_bodyCutStorage compiled targetAt
          ((funcs dp).take 5) firstCursor firstRoute with
        ⟨word, body, member, bodyPath, bodyCursor, bodyRoute,
          firstToBody⟩
      exact ⟨word, body, List.mem_of_mem_take member,
        bodyPath, bodyCursor, bodyRoute,
        rootToLeft.trans (leftToFirst.trans firstToBody)⟩
    · rcases linearDispatchWith_bodyCutStorage compiled targetAt
          ((funcs dp).drop 5 |>.take 4) secondCursor secondRoute with
        ⟨word, body, member, bodyPath, bodyCursor, bodyRoute,
          secondToBody⟩
      have memberDrop : (word, body) ∈ (funcs dp).drop 5 :=
        List.mem_of_mem_take member
      exact ⟨word, body, List.mem_of_mem_drop memberDrop,
        bodyPath, bodyCursor, bodyRoute,
        rootToLeft.trans (leftToSecond.trans secondToBody)⟩
  · rcases splitDispatch_bodyCutStorage compiled targetAt
        rightCursor rightRoute with
      ⟨thirdPath, thirdCursor, thirdRoute, rightToThird⟩ |
        ⟨fourthPath, fourthCursor, fourthRoute, rightToFourth⟩
    · rcases linearDispatchWith_bodyCutStorage compiled targetAt
          ((funcs dp).drop 9 |>.take 4) thirdCursor thirdRoute with
        ⟨word, body, member, bodyPath, bodyCursor, bodyRoute,
          thirdToBody⟩
      have memberDrop : (word, body) ∈ (funcs dp).drop 9 :=
        List.mem_of_mem_take member
      exact ⟨word, body, List.mem_of_mem_drop memberDrop,
        bodyPath, bodyCursor, bodyRoute,
        rootToRight.trans (rightToThird.trans thirdToBody)⟩
    · rcases linearDispatchWith_bodyCutStorage compiled targetAt
          ((funcs dp).drop 13) fourthCursor fourthRoute with
        ⟨word, body, member, bodyPath, bodyCursor, bodyRoute,
          fourthToBody⟩
      exact ⟨word, body, List.mem_of_mem_drop member,
        bodyPath, bodyCursor, bodyRoute,
        rootToRight.trans (rightToFourth.trans fourthToBody)⟩

private def runtimeViewSstoreFreeSlots : List Nat :=
  [emptyRevertSlot, bubbleRevertSlot, enumLoopSlot]

private inductive RuntimeDispatchCut
    {dp : DeployParams} {root target : Exec.Deriv}
    (initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)) : Prop
  | setPauseDuration {path : Prog.SourcePath}
      (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
        (setPauseDuration dp))
      (route : Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) cursor)
      (entryStorage : Devm.getStor cursor.pre = Devm.getStor initial.pre)
  | setHeartbeatInterval {path : Prog.SourcePath}
      (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
        (setHeartbeatInterval dp))
      (route : Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) cursor)
      (entryStorage : Devm.getStor cursor.pre = Devm.getStor initial.pre)
  | registerPauser {path : Prog.SourcePath}
      (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
        (registerPauser dp))
      (route : Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) cursor)
      (entryStorage : Devm.getStor cursor.pre = Devm.getStor initial.pre)
  | heartbeat {path : Prog.SourcePath}
      (cursor : Exec.Deriv.SourceCursor root (runtime dp) path heartbeat)
      (route : Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) cursor)
      (entryStorage : Devm.getStor cursor.pre = Devm.getStor initial.pre)
  | pause {path : Prog.SourcePath}
      (cursor : Exec.Deriv.SourceCursor root (runtime dp) path pause)
      (route : Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) cursor)
      (entryStorage : Devm.getStor cursor.pre = Devm.getStor initial.pre)

private theorem runtimeMain_writeEndpointCut
    {dp : DeployParams} {root target : Exec.Deriv}
    (mainCursor : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      mainCursor target (.reg .sstore) mainCursor) :
    RuntimeDispatchCut (target := target) mainCursor := by
  rcases Exec.Deriv.SourceCursor.Toward.dropLineRun route
      (line := [Ninst.callvalue, Ninst.pushB256 4,
        Ninst.calldatasize, Ninst.lt, Ninst.or])
      (by
        intro instruction member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl <;>
          intro h <;> cases h) with
    ⟨entryPath, entryCursor, entryRun, entryChronology, entryRoute⟩
  have mainToEntry :
      Devm.getStor mainCursor.pre = Devm.getStor entryCursor.pre :=
    Line.of_inv Devm.getStor (by line_inv) entryRun
  rcases Exec.Deriv.SourceCursor.Toward.branchArmStorage
      entryCursor compiled targetAt entryRoute with
    ⟨dispatchEntry, dispatchEntryRoute, entryToDispatchEntry, zeroPrefix⟩ |
      ⟨flag, nonzero, flagPrefix, errorCursor, errorRoute,
        entryToError⟩
  ·
    rcases Exec.Deriv.SourceCursor.Toward.dropLineRun dispatchEntryRoute
          (line := fsig) (by
            intro instruction member
            simp only [fsig, cdl, shiftRight, List.mem_append,
              List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with (rfl | rfl) | (rfl | rfl) <;>
              intro h <;> cases h) with
        ⟨dispatchPath, dispatchCursor, fsigRun, dispatchChronology,
          dispatchRoute⟩
    have dispatchEntryToDispatch :
          Devm.getStor dispatchEntry.pre = Devm.getStor dispatchCursor.pre :=
        Line.of_inv Devm.getStor (by line_inv) fsigRun
    rcases hybridDispatchWith_bodyCutStorage compiled targetAt
          dispatchCursor dispatchRoute with
        ⟨word, body, member, bodyPath, bodyCursor, bodyRoute,
          dispatchToBody⟩
    have mainToBody :
          Devm.getStor mainCursor.pre = Devm.getStor bodyCursor.pre :=
        mainToEntry.trans
          (entryToDispatchEntry.trans
            (dispatchEntryToDispatch.trans dispatchToBody))
    simp only [funcs, List.mem_cons,
        List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim

    · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
    · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
    · exact .registerPauser bodyCursor bodyRoute mainToBody.symm
    · exact .heartbeat bodyCursor bodyRoute mainToBody.symm
    · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
    · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
    · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
    · exact .setHeartbeatInterval bodyCursor bodyRoute mainToBody.symm
    · exact .pause bodyCursor bodyRoute mainToBody.symm
    · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
    · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
    · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
    · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
    · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
    · exact .setPauseDuration bodyCursor bodyRoute mainToBody.symm
    · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
  · exact (errorCursor.noSstore_of_entrySstoreFree compiled [] rfl
      (Exec.Deriv.SourceCursor.Toward.chronology
        errorRoute).cursorToTarget targetAt).elim

private theorem onlyAdminGuard
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource tail : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (onlyAdmin dp tail))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
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
  unfold onlyAdmin at cursor route
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
      (by intro h; cases h) with
    ⟨callerChronology, pushCursor, callerEdge, callerRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne callerRoute
      (by intro h; cases h) with
    ⟨pushChronology, eqCursor, pushEdge, eqRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne eqRoute
      (by intro h; cases h) with
    ⟨eqChronology, branchCursor, eqEdge, branchRoute⟩
  have callerRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge cursor callerEdge
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
      targetAt with errorArm |
        ⟨flag, nonzero, flagPrefix, successCursor, branchToSuccess,
          successReached, successStorage⟩
  · rcases errorArm with
      ⟨errorCursor, branchToError, errorReached, zeroPrefix, errorStorage⟩
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

private theorem onlyAdminToward
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource body : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (onlyAdmin dp body))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ bodyPath,
      ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
          bodyPath body,
        Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) bodyCursor := by
  unfold onlyAdmin at cursor route
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
      (by intro h; cases h) with
    ⟨callerChronology, pushCursor, callerEdge, callerRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne callerRoute
      (by intro h; cases h) with
    ⟨pushChronology, eqCursor, pushEdge, eqRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne eqRoute
      (by intro h; cases h) with
    ⟨eqChronology, branchCursor, eqEdge, branchRoute⟩
  cases branchRoute with
  | branchLeft branchCursor chronology arm compilerPrefix rest =>
      exact (arm.noSstore_of_entrySstoreFree compiled
        [senderNotAdminErrorSlot] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology rest).cursorToTarget
        targetAt).elim
  | branchRight branchCursor chronology arm compilerPrefix rest =>
      exact ⟨_, arm, rest⟩

private theorem configurationSetterTarget
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (minimum maximum event slot : B256)
    (belowErrorSlot aboveErrorSlot : Nat)
    (belowFree : (runtime dp).entrySstoreFree
      (.call belowErrorSlot) [belowErrorSlot] = true)
    (aboveFree : (runtime dp).entrySstoreFree
      (.call aboveErrorSlot) [aboveErrorSlot] = true)
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (pushDeployWord minimum ::: arg 0 +++ Ninst.lt :::
        ((.call belowErrorSlot) <?>
          (pushDeployWord maximum ::: arg 0 +++ Ninst.gt :::
            ((.call aboveErrorSlot) <?>
              (Ninst.pushB256 slot ::: Ninst.sload ::: mstoreAt 0 +++
                arg 0 +++ mstoreAt 1 +++
                Ninst.pushB256 event ::: logWith 0 0 2 +++
                arg 0 +++ Ninst.pushB256 slot ::: Ninst.sstore ::: Func.stop))))))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ finalPath finalTail,
      ∃ finalCursor : Exec.Deriv.SourceCursor root (runtime dp)
          finalPath (.next (.reg .sstore) finalTail),
        finalCursor.node = target ∧
          ({ path := finalPath, pc := finalCursor.pc,
              instruction := (.reg .sstore) } : Prog.SourceSite) ∈
            (runtime dp).sourceSites ∧
          finalPath.functionIndex = path.functionIndex ∧
          ∃ suffixSteps : List Prog.SourceStep,
            finalPath.steps = path.steps ++ suffixSteps ∧
            suffixSteps =
              List.replicate 4 .rest ++ [.branchLeft] ++
              List.replicate 4 .rest ++ [.branchLeft] ++
              List.replicate 15 .rest := by
  let minimumLine : Line :=
    [pushDeployWord minimum] ++ arg 0 ++ [Ninst.lt]
  let maximumLine : Line :=
    [pushDeployWord maximum] ++ arg 0 ++ [Ninst.gt]
  let storeLine : Line :=
    [Ninst.pushB256 slot, Ninst.sload] ++ mstoreAt 0 ++
      arg 0 ++ mstoreAt 1 ++ [Ninst.pushB256 event] ++
      logWith 0 0 2 ++ arg 0 ++ [Ninst.pushB256 slot]
  dsimp [minimumLine, maximumLine, storeLine, arg, cdl, mstoreAt,
    logWith] at cursor route
  rcases Exec.Deriv.SourceCursor.Toward.dropLineExact
      (cursor := cursor) (line := minimumLine) route (by
        intro instruction member
        simp [minimumLine, arg, cdl] at member
        rcases member with rfl | rfl | rfl | rfl <;>
          intro h <;> cases h) with
    ⟨minimumBranch, minimumRoute⟩
  cases minimumRoute with
  | branchRight branchCursor chronology errorCursor compilerPrefix errorRoute =>
      exact (errorCursor.noSstore_of_entrySstoreFree compiled
        [belowErrorSlot] belowFree
        (Exec.Deriv.SourceCursor.Toward.chronology
          errorRoute).cursorToTarget targetAt).elim
  | branchLeft branchCursor chronology maximumCursor compilerPrefix maximumRoute =>
      rcases Exec.Deriv.SourceCursor.Toward.dropLineExact maximumRoute
          (line := maximumLine) (by
            intro instruction member
            simp [maximumLine, arg, cdl] at member
            rcases member with rfl | rfl | rfl | rfl <;>
              intro h <;> cases h) with
        ⟨maximumBranch, maximumBranchRoute⟩
      cases maximumBranchRoute with
      | branchRight branchCursor chronology errorCursor compilerPrefix errorRoute =>
          exact (errorCursor.noSstore_of_entrySstoreFree compiled
            [aboveErrorSlot] aboveFree
            (Exec.Deriv.SourceCursor.Toward.chronology
              errorRoute).cursorToTarget targetAt).elim
      | branchLeft branchCursor chronology storeCursor compilerPrefix storeRoute =>
          rcases Exec.Deriv.SourceCursor.Toward.dropLineExact storeRoute
              (line := storeLine) (by
                intro instruction member
                simp [storeLine, mstoreAt, arg, cdl, logWith] at member
                rcases member with
                    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                  intro h <;> cases h) with
            ⟨finalCursor, finalRoute⟩
          cases finalRoute with
          | atTarget finalCursor chronology site siteEq sourceMember targetEq
              instructionEq =>
              refine ⟨_, _, finalCursor, targetEq, ?_, rfl, ?_⟩
              · simpa [siteEq] using sourceMember
              · refine ⟨
                  List.replicate 4 .rest ++ [.branchLeft] ++
                    List.replicate 4 .rest ++ [.branchLeft] ++
                    List.replicate 15 .rest, ?_, rfl⟩
                simp [minimumLine, maximumLine, storeLine,
                  arg, cdl, mstoreAt, logWith, List.append_assoc]
          | next finalCursor chronology tailCursor edge rest =>
              cases rest

private def configurationStoreSuffix : List Prog.SourceStep :=
  List.replicate 4 .rest ++ [.branchLeft] ++
    List.replicate 4 .rest ++ [.branchLeft] ++
    List.replicate 15 .rest

private def RuntimePersistentWrite.hasConfigurationStoreSuffix
    (row : RuntimePersistentWrite) : Bool :=
  match row.sourceSite? officialParams with
  | some site => decide (configurationStoreSuffix <:+ site.path.steps)
  | none => false

private theorem RuntimePersistentWrite.configuration_of_storeSuffix
    {row : RuntimePersistentWrite}
    (hasSuffix : row.hasConfigurationStoreSuffix = true) :
    row = .setPauseDurationConfig ∨
      row = .setHeartbeatIntervalConfig := by
  cases row
  case setPauseDurationConfig => exact Or.inl rfl
  case setHeartbeatIntervalConfig => exact Or.inr rfl
  all_goals
    exfalso
    revert hasSuffix
    decide +kernel

private theorem configurationRow_of_terminal
    {dp : DeployParams} {root target : Exec.Deriv}
    {row : RuntimePersistentWrite} {site : Prog.SourceSite}
    {path finalPath : Prog.SourcePath} {finalTail : Func}
    (finalCursor : Exec.Deriv.SourceCursor root (runtime dp)
      finalPath (.next (.reg .sstore) finalTail))
    (found : row.sourceSite? dp = some site)
    (sitePc : site.pc = target.pc)
    (targetEq : finalCursor.node = target)
    (sourceMember :
      ({ path := finalPath, pc := finalCursor.pc,
          instruction := (.reg .sstore) } : Prog.SourceSite) ∈
        (runtime dp).sourceSites)
    (finalSteps : finalPath.steps =
      path.steps ++ configurationStoreSuffix) :
    row = .setPauseDurationConfig ∨
      row = .setHeartbeatIntervalConfig := by
  let terminalSite : Prog.SourceSite :=
    { path := finalPath, pc := finalCursor.pc,
      instruction := (.reg .sstore) }
  have siteSound := row.sourceSite?_sound found
  have siteMember : site ∈ runtimePersistentSourceSites dp := by
    apply List.mem_filter.mpr
    refine ⟨siteSound.1, ?_⟩
    rw [siteSound.2]
    rfl
  have terminalMember : terminalSite ∈ runtimePersistentSourceSites dp := by
    exact List.mem_filter.mpr ⟨sourceMember, rfl⟩
  have terminalPc : finalCursor.pc = target.pc := by
    have nodePc := congrArg Exec.Deriv.pc targetEq
    simpa [Exec.Deriv.SourceCursor.node] using nodePc
  have siteEq : site = terminalSite :=
    runtimePersistentSourceSite_eq_of_pc siteMember terminalMember
      (sitePc.trans terminalPc.symm)
  have siteSteps : site.path.steps =
      path.steps ++ configurationStoreSuffix := by
    rw [siteEq]
    exact finalSteps
  have sitesEq := runtimePersistentSourceSites_eq_official dp
  unfold RuntimePersistentWrite.sourceSite? at found
  rw [sitesEq] at found
  have foundOfficial : row.sourceSite? officialParams = some site := by
    exact found
  have suffixFact : configurationStoreSuffix <:+ site.path.steps :=
    ⟨path.steps, siteSteps.symm⟩
  have hasSuffix : row.hasConfigurationStoreSuffix = true := by
    simp [RuntimePersistentWrite.hasConfigurationStoreSuffix, foundOfficial,
      suffixFact]
  exact row.configuration_of_storeSuffix hasSuffix

private def heartbeatStoreSuffix : List Prog.SourceStep :=
  List.replicate 5 .rest ++ [.branchLeft] ++
    List.replicate 6 .rest ++ [.branchRight] ++
    List.replicate 8 .rest ++ [.branchLeft] ++
    List.replicate 6 .rest

private theorem heartbeatTarget
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path heartbeat)
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ finalPath finalTail,
      ∃ finalCursor : Exec.Deriv.SourceCursor root (runtime dp)
          finalPath (.next (.reg .sstore) finalTail),
        finalCursor.node = target ∧
          ({ path := finalPath, pc := finalCursor.pc,
              instruction := (.reg .sstore) } : Prog.SourceSite) ∈
            (runtime dp).sourceSites ∧
          finalPath.steps = path.steps ++ heartbeatStoreSuffix := by
  unfold heartbeat at cursor
  let registeredLine : Line :=
    [Ninst.caller] ++ tagTop countRegion ++ [Ninst.sload, Ninst.iszero]
  let liveLine : Line :=
    [Ninst.caller] ++ tagTop expiryRegion ++
      [Ninst.sload, Ninst.timestamp, Ninst.lt]
  let checkedLine : Line :=
    [Ninst.timestamp, Ninst.pushB256 heartbeatIntervalSlot,
      Ninst.sload, Ninst.add, Ninst.dup 0, Ninst.timestamp,
      Ninst.swap 0, Ninst.lt]
  let storeLine : Line :=
    [Ninst.dup 0] ++ mstoreAt 0 ++
      [Ninst.caller] ++ tagTop expiryRegion
  dsimp [registeredLine, liveLine, checkedLine, storeLine,
    tagTop, mstoreAt] at cursor route
  rcases Exec.Deriv.SourceCursor.Toward.dropLineExact
      (cursor := cursor) (line := registeredLine) route (by
        intro instruction member
        simp [registeredLine, tagTop] at member
        rcases member with rfl | rfl | rfl | rfl | rfl <;>
          intro h <;> cases h) with
    ⟨registeredBranch, registeredRoute⟩
  cases registeredRoute with
  | branchRight branchCursor chronology errorCursor compilerPrefix errorRoute =>
      exact (errorCursor.noSstore_of_entrySstoreFree compiled
        [senderNotPauserErrorSlot] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology
          errorRoute).cursorToTarget targetAt).elim
  | branchLeft branchCursor chronology liveCursor compilerPrefix liveRoute =>
      rcases Exec.Deriv.SourceCursor.Toward.dropLineExact liveRoute
          (line := liveLine) (by
            intro instruction member
            simp [liveLine, tagTop] at member
            rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
              intro h <;> cases h) with
        ⟨liveBranch, liveBranchRoute⟩
      cases liveBranchRoute with
      | branchLeft branchCursor chronology errorCursor compilerPrefix errorRoute =>
          exact (errorCursor.noSstore_of_entrySstoreFree compiled
            [heartbeatExpiredErrorSlot] rfl
            (Exec.Deriv.SourceCursor.Toward.chronology
              errorRoute).cursorToTarget targetAt).elim
      | branchRight branchCursor chronology checkedCursor compilerPrefix checkedRoute =>
          rcases Exec.Deriv.SourceCursor.Toward.dropLineExact checkedRoute
              (line := checkedLine) (by
                intro instruction member
                simp [checkedLine] at member
                rcases member with
                    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                  intro h <;> cases h) with
            ⟨checkedBranch, checkedBranchRoute⟩
          cases checkedBranchRoute with
          | branchRight branchCursor chronology errorCursor compilerPrefix errorRoute =>
              exact (errorCursor.noSstore_of_entrySstoreFree compiled
                [arithmeticPanicSlot] (by
                  simp [Prog.entrySstoreFree, Prog.componentSstoreFree,
                    Prog.function?, runtime, aux, arithmeticPanicSlot,
                    Func.revData, Func.localSstoreFree, Func.callsIn]
                  decide +kernel)
                (Exec.Deriv.SourceCursor.Toward.chronology
                  errorRoute).cursorToTarget targetAt).elim
          | branchLeft branchCursor chronology storeCursor compilerPrefix storeRoute =>
              rcases Exec.Deriv.SourceCursor.Toward.dropLineExact storeRoute
                  (line := storeLine) (by
                    intro instruction member
                    simp [storeLine, tagTop, mstoreAt] at member
                    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
                      intro h <;> cases h) with
                ⟨finalCursor, finalRoute⟩
              cases finalRoute with
              | atTarget finalCursor chronology site siteEq sourceMember
                  targetEq instructionEq =>
                  refine ⟨_, _, finalCursor, targetEq, ?_, ?_⟩
                  · simpa [siteEq] using sourceMember
                  · simp [heartbeatStoreSuffix, registeredLine, liveLine,
                      checkedLine, storeLine, tagTop, mstoreAt,
                      List.append_assoc]
              | next finalCursor chronology tailCursor edge rest =>
                  exact (tailCursor.noSstore_of_entrySstoreFree compiled
                    [] rfl
                    (Exec.Deriv.SourceCursor.Toward.chronology
                      rest).cursorToTarget targetAt).elim

private def RuntimePersistentWrite.hasHeartbeatStoreSuffix
    (row : RuntimePersistentWrite) : Bool :=
  match row.sourceSite? officialParams with
  | some site => decide (heartbeatStoreSuffix <:+ site.path.steps)
  | none => false

private theorem RuntimePersistentWrite.heartbeat_of_storeSuffix
    {row : RuntimePersistentWrite}
    (hasSuffix : row.hasHeartbeatStoreSuffix = true) :
    row = .heartbeatExpiry := by
  cases row
  case heartbeatExpiry => rfl
  all_goals
    exfalso
    revert hasSuffix
    decide +kernel

private theorem heartbeatRow_of_terminal
    {dp : DeployParams} {root target : Exec.Deriv}
    {row : RuntimePersistentWrite} {site : Prog.SourceSite}
    {path finalPath : Prog.SourcePath} {finalTail : Func}
    (finalCursor : Exec.Deriv.SourceCursor root (runtime dp)
      finalPath (.next (.reg .sstore) finalTail))
    (found : row.sourceSite? dp = some site)
    (sitePc : site.pc = target.pc)
    (targetEq : finalCursor.node = target)
    (sourceMember :
      ({ path := finalPath, pc := finalCursor.pc,
          instruction := (.reg .sstore) } : Prog.SourceSite) ∈
        (runtime dp).sourceSites)
    (finalSteps : finalPath.steps =
      path.steps ++ heartbeatStoreSuffix) :
    row = .heartbeatExpiry := by
  let terminalSite : Prog.SourceSite :=
    { path := finalPath, pc := finalCursor.pc,
      instruction := (.reg .sstore) }
  have siteSound := row.sourceSite?_sound found
  have siteMember : site ∈ runtimePersistentSourceSites dp := by
    apply List.mem_filter.mpr
    refine ⟨siteSound.1, ?_⟩
    rw [siteSound.2]
    rfl
  have terminalMember : terminalSite ∈ runtimePersistentSourceSites dp := by
    exact List.mem_filter.mpr ⟨sourceMember, rfl⟩
  have terminalPc : finalCursor.pc = target.pc := by
    have nodePc := congrArg Exec.Deriv.pc targetEq
    simpa [Exec.Deriv.SourceCursor.node] using nodePc
  have siteEq : site = terminalSite :=
    runtimePersistentSourceSite_eq_of_pc siteMember terminalMember
      (sitePc.trans terminalPc.symm)
  have siteSteps : site.path.steps =
      path.steps ++ heartbeatStoreSuffix := by
    rw [siteEq]
    exact finalSteps
  have sitesEq := runtimePersistentSourceSites_eq_official dp
  unfold RuntimePersistentWrite.sourceSite? at found
  rw [sitesEq] at found
  have foundOfficial : row.sourceSite? officialParams = some site := by
    exact found
  have suffixFact : heartbeatStoreSuffix <:+ site.path.steps :=
    ⟨path.steps, siteSteps.symm⟩
  have hasSuffix : row.hasHeartbeatStoreSuffix = true := by
    simp [RuntimePersistentWrite.hasHeartbeatStoreSuffix, foundOfficial,
      suffixFact]
  exact row.heartbeat_of_storeSuffix hasSuffix

private theorem requireStaticOnlyAdminGuard
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource tail : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (argCount : Nat)
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (requireStaticArgs argCount (onlyAdmin dp tail)))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
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
  unfold requireStaticArgs at cursor route
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
  | branchRight branchCursor chronology arm compilerPrefix rest =>
      exact (arm.noSstore_of_entrySstoreFree compiled [] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology rest).cursorToTarget
        targetAt).elim
  | branchLeft branchCursor chronology arm compilerPrefix rest =>
      exact onlyAdminGuard arm compiled targetAt rest

private theorem requireStaticArgsToward
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource body : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (words : Nat)
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (requireStaticArgs words body))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ bodyPath,
      ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
          bodyPath body,
        Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) bodyCursor := by
  unfold requireStaticArgs at cursor route
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
      (by intro h; cases h) with
    ⟨sizeChronology, sizeCursor, sizeEdge, sizeRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne sizeRoute
      (by intro h; cases h) with
    ⟨calldataChronology, calldataCursor, calldataEdge, calldataRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne calldataRoute
      (by intro h; cases h) with
    ⟨ltChronology, branchCursor, ltEdge, branchRoute⟩
  cases branchRoute with
  | branchRight branchCursor chronology arm compilerPrefix rest =>
      exact (arm.noSstore_of_entrySstoreFree compiled [] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology rest).cursorToTarget
        targetAt).elim
  | branchLeft branchCursor chronology arm compilerPrefix rest =>
      exact ⟨_, arm, rest⟩

private theorem canonicalAddressArgToward
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource body : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (index : B256)
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (canonicalAddressArg index body))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ bodyPath,
      ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
          bodyPath body,
        Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) bodyCursor := by
  unfold canonicalAddressArg at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropLine route
      (line := arg index ++ checkNonAddress)
      (by simp [arg, checkNonAddress, cdl, pushAddressMask,
        Ninst.pushB256]) with
    ⟨branchPath, branchCursor, branchChronology, branchRoute⟩
  cases branchRoute with
  | branchRight branchCursor chronology arm compilerPrefix rest =>
      exact (arm.noSstore_of_entrySstoreFree compiled
        [emptyRevertSlot] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology rest).cursorToTarget
        targetAt).elim
  | branchLeft branchCursor chronology arm compilerPrefix rest =>
      exact ⟨_, arm, rest⟩

private theorem requireStaticArgsTowardStorage
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource body : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (words : Nat)
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (requireStaticArgs words body))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ bodyPath,
      ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
          bodyPath body,
        Exec.Deriv.SourceCursor.Toward
            initial target (.reg .sstore) bodyCursor ∧
          Devm.getStor cursor.pre = Devm.getStor bodyCursor.pre := by
  unfold requireStaticArgs at cursor route
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
      (by intro h; cases h) with
    ⟨sizeChronology, calldataCursor, sizeEdge, calldataRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne calldataRoute
      (by intro h; cases h) with
    ⟨calldataChronology, ltCursor, calldataEdge, ltRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne ltRoute
      (by intro h; cases h) with
    ⟨ltChronology, branchCursor, ltEdge, branchRoute⟩
  have sizeRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge cursor sizeEdge
  have calldataRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge calldataCursor calldataEdge
  have ltRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge ltCursor ltEdge
  have prefixStorage :
      Devm.getStor cursor.pre = Devm.getStor branchCursor.pre :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons sizeRun
        (Line.Run.cons calldataRun (Line.Run.cons ltRun Line.Run.nil)))
  rcases Exec.Deriv.SourceCursor.Toward.branchArmStorage
      branchCursor compiled targetAt branchRoute with
    ⟨bodyCursor, bodyRoute, branchStorage, zeroPrefix⟩ |
      ⟨flag, nonzero, flagPrefix, errorCursor, errorRoute,
        branchStorage⟩
  · exact ⟨_, bodyCursor, bodyRoute,
      prefixStorage.trans branchStorage⟩
  · exact (errorCursor.noSstore_of_entrySstoreFree compiled [] rfl
      (Exec.Deriv.SourceCursor.Toward.chronology
        errorRoute).cursorToTarget targetAt).elim

private theorem canonicalAddressArgTowardStorage
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource body : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (index : B256)
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (canonicalAddressArg index body))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ bodyPath,
      ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
          bodyPath body,
        Exec.Deriv.SourceCursor.Toward
            initial target (.reg .sstore) bodyCursor ∧
          Devm.getStor cursor.pre = Devm.getStor bodyCursor.pre := by
  unfold canonicalAddressArg at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropLineRun route
      (line := arg index ++ checkNonAddress)
      (by simp [arg, checkNonAddress, cdl, pushAddressMask,
        Ninst.pushB256]) with
    ⟨branchPath, branchCursor, prefixRun, branchChronology,
      branchRoute⟩
  have prefixStorage :
      Devm.getStor cursor.pre = Devm.getStor branchCursor.pre :=
    Line.of_inv Devm.getStor (by line_inv) prefixRun
  rcases Exec.Deriv.SourceCursor.Toward.branchArmStorage
      branchCursor compiled targetAt branchRoute with
    ⟨bodyCursor, bodyRoute, branchStorage, zeroPrefix⟩ |
      ⟨flag, nonzero, flagPrefix, errorCursor, errorRoute,
        branchStorage⟩
  · exact ⟨_, bodyCursor, bodyRoute,
      prefixStorage.trans branchStorage⟩
  · exact (errorCursor.noSstore_of_entrySstoreFree compiled
      [emptyRevertSlot] rfl
      (Exec.Deriv.SourceCursor.Toward.chronology
        errorRoute).cursorToTarget targetAt).elim

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
  exact requireStaticOnlyAdminGuard 1 bodyCursor compiled targetAt route

private theorem registerPauserBodyGuard
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource source : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (sourceEq : source = registerPauser dp)
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
  rcases requireStaticArgsToward 2 bodyCursor compiled targetAt route with
    ⟨firstPath, firstCursor, firstRoute⟩
  rcases canonicalAddressArgToward 0 firstCursor compiled targetAt firstRoute with
    ⟨secondPath, secondCursor, secondRoute⟩
  rcases canonicalAddressArgToward 1 secondCursor compiled targetAt secondRoute with
    ⟨adminPath, adminCursor, adminRoute⟩
  exact onlyAdminGuard adminCursor compiled targetAt adminRoute

private def continuationOffset : Nat :=
  (continuationWord * 32).toNat

/-- The register entry overwrites the continuation word completely.  Retaining
both byte coverage bounds makes subsequent disjoint scratch writes safe even
when nothing is assumed about the memory that preceded that overwrite. -/
private def RegisterContinuationZero (memory : Mem) : Prop :=
  (memory.read continuationOffset 32).1 = (0 : B256).toBytes ∧
    continuationOffset + 32 ≤ memory.data.size ∧
    continuationOffset + 32 ≤ memory.size

private theorem RegisterContinuationZero.of_write (memory : Mem) :
    RegisterContinuationZero
      (memory.write continuationOffset (0 : B256).toBytes) := by
  have hne : (0 : B256).toBytes ≠ [] := by
    intro empty
    have lengthEq := B256.length_toBytes (0 : B256)
    rw [empty] at lengthEq
    simp at lengthEq
  rcases bytesEq : (0 : B256).toBytes with _ | ⟨byte, bytes⟩
  · exact (hne bytesEq).elim
  · have lengthEq : (byte :: bytes).length = 32 := by
      rw [← bytesEq]
      exact B256.length_toBytes _
    have hread :
        ((memory.write continuationOffset (byte :: bytes)).read
          continuationOffset 32).1 = (0 : B256).toBytes := by
      rw [bytesEq]
      simp only [Mem.write]
      split
      · split
        · simp only [Mem.read, Array.sliceD_eq_map]
          apply List.ext_get
          · simp [lengthEq]
          · intro index hindex hbound
            simp only [List.length_map, List.length_range] at hindex
            simp only [List.get_eq_getElem, List.getElem_map,
              List.getElem_range]
            rw [Array.getD_writeD 0 (byte :: bytes) memory.data
              continuationOffset (continuationOffset + index) (by omega),
              if_pos (by omega)]
            simp [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem hbound]
        · simp only [Mem.read, Array.sliceD_eq_map]
          apply List.ext_get
          · simp [lengthEq]
          · intro index hindex hbound
            simp only [List.length_map, List.length_range] at hindex
            simp only [List.get_eq_getElem, List.getElem_map,
              List.getElem_range]
            rw [Array.getD_writeD 0 (byte :: bytes)
              (Array.copyD memory.data
                (Array.replicate
                  (continuationOffset + (byte :: bytes).length) 0x00))
              continuationOffset (continuationOffset + index)
              (by rw [Array.size_copyD, Array.size_replicate]),
              if_pos (by omega)]
            simp [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem hbound]
      · simp only [Mem.read, Array.sliceD_eq_map]
        apply List.ext_get
        · simp [lengthEq]
        · intro index hindex hbound
          simp only [List.length_map, List.length_range] at hindex
          simp only [List.get_eq_getElem, List.getElem_map,
            List.getElem_range]
          rw [Array.getD_writeD 0 (byte :: bytes)
            (Array.copyD memory.data
              (Array.replicate
                (ceil32
                  (continuationOffset + (byte :: bytes).length)) 0x00))
            continuationOffset (continuationOffset + index)
            (by
              rw [Array.size_copyD, Array.size_replicate]
              exact Nat.le_ceil32 _),
            if_pos (by omega)]
          simp [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hbound]
    refine ⟨hread, ?_, ?_⟩
    · simp only [Mem.write]
      split
      case isTrue sizeCovered =>
        split
        · rw [Array.size_writeD]
          omega
        · rw [Array.size_writeD, Array.size_copyD,
            Array.size_replicate]
          omega
      case isFalse sizeShort =>
        rw [Array.size_writeD, Array.size_copyD,
          Array.size_replicate]
        exact lengthEq ▸ Nat.le_ceil32 _
    · simp only [Mem.write]
      split
      · split <;> simp_all
      · exact lengthEq ▸ Nat.le_ceil32 _

private theorem RegisterContinuationZero.writeBefore
    {memory : Mem} (zero : RegisterContinuationZero memory)
    (offset : Nat) (before : offset + 32 ≤ continuationOffset)
    (value : B256) :
    RegisterContinuationZero (memory.write offset value.toBytes) := by
  rcases zero with ⟨readZero, dataCovered, sizeCovered⟩
  rcases bytesEq : value.toBytes with _ | ⟨byte, bytes⟩
  · have impossible := B256.length_toBytes value
    rw [bytesEq] at impossible
    simp at impossible
  · have lengthEq : (byte :: bytes).length = 32 := by
      rw [← bytesEq]
      exact B256.length_toBytes _
    have writeSize :
        offset + (byte :: bytes).length ≤ memory.size := by
      omega
    have writeData :
        offset + (byte :: bytes).length ≤ memory.data.size := by
      omega
    have memoryEq : memory.write offset (byte :: bytes) =
        { data := Array.writeD memory.data offset (byte :: bytes),
          size := memory.size } := by
      simp only [Mem.write]
      rw [if_pos writeSize, if_pos writeData]
    rw [memoryEq]
    refine ⟨?_, ?_, sizeCovered⟩
    · change Array.sliceD
        (Array.writeD memory.data offset (byte :: bytes))
        continuationOffset 32 0 = (0 : B256).toBytes
      rw [Array.sliceD_eq_map]
      rw [show (memory.read continuationOffset 32).1 =
          (List.range 32).map
            (fun index =>
              memory.data.getD (continuationOffset + index) 0) by
        simp [Mem.read, Array.sliceD_eq_map]] at readZero
      rw [← readZero]
      apply List.map_congr_left
      intro index member
      rw [Array.getD_writeD 0 (byte :: bytes) memory.data offset
        (continuationOffset + index) writeData, if_neg]
      have indexLt := List.mem_range.mp member
      omega
    · change continuationOffset + 32 ≤
        (Array.writeD memory.data offset (byte :: bytes)).size
      simpa [Array.size_writeD] using dataCovered

private theorem RegisterContinuationZero.foldPreservesBefore
    {ξ : Type} (default : ξ) :
    ∀ (values : List ξ) (array : Array ξ) (offset index : Nat),
      index < offset →
      (List.foldl (fun (state : Array ξ × Nat) value =>
        (state.fst.setIfInBounds state.snd value, state.snd + 1))
        (array, offset) values).fst.getD index default =
          array.getD index default := by
  intro values
  induction values with
  | nil => intro array offset index before; rfl
  | cons value rest ih =>
      intro array offset index before
      simp only [List.foldl_cons]
      rw [ih _ _ _ (by omega)]
      by_cases offsetInBounds : offset < array.size
      · rw [Array.getD_setIfInBounds _ _ _ offsetInBounds,
          if_neg (by omega)]
      · simp [Array.setIfInBounds, offsetInBounds]

private theorem RegisterContinuationZero.foldReadsMember
    {ξ : Type} (default : ξ) :
    ∀ (values : List ξ) (array : Array ξ) (offset index : Nat),
      index < array.size → offset ≤ index →
      index < offset + values.length →
      (List.foldl (fun (state : Array ξ × Nat) value =>
        (state.fst.setIfInBounds state.snd value, state.snd + 1))
        (array, offset) values).fst.getD index default =
          values.getD (index - offset) default := by
  intro values
  induction values with
  | nil =>
      intro array offset index inBounds after before
      simp only [List.length_nil, Nat.add_zero] at before
      omega
  | cons value rest ih =>
      intro array offset index inBounds after before
      simp only [List.foldl_cons]
      by_cases atOffset : index = offset
      · subst index
        rw [RegisterContinuationZero.foldPreservesBefore default
          _ _ _ _ (by omega)]
        rw [Array.getD_setIfInBounds _ _ _ inBounds, if_pos rfl]
        simp
      · have afterNext : offset + 1 ≤ index := by omega
        rw [ih _ _ _ (by rw [Array.size_setIfInBounds]; exact inBounds)
          afterNext (by simp at before ⊢; omega)]
        have subEq : index - offset =
            (index - (offset + 1)) + 1 := by
          omega
        rw [subEq]
        rfl

private theorem RegisterContinuationZero.getD_copyD_of_lt
    {ξ : Type} (source target : Array ξ) (default : ξ) (index : Nat)
    (sourceBound : index < source.size)
    (targetBound : index < target.size) :
    (Array.copyD source target).getD index default =
      source.getD index default := by
  unfold Array.copyD
  change (Array.foldl (fun (state : Array ξ × Nat) value =>
    (state.fst.setIfInBounds state.snd value, state.snd + 1))
    (target, 0) source).fst.getD index default =
      source.getD index default
  rw [← Array.foldl_toList]
  rw [RegisterContinuationZero.foldReadsMember default source.toList
    target 0 index targetBound (by omega) (by simpa using sourceBound)]
  simp [Array.getD, sourceBound]

private theorem RegisterContinuationZero.writeAfter
    {memory : Mem} (zero : RegisterContinuationZero memory)
    (offset : Nat) (after : continuationOffset + 32 ≤ offset)
    (value : B256) :
    RegisterContinuationZero (memory.write offset value.toBytes) := by
  rcases zero with ⟨readZero, dataCovered, sizeCovered⟩
  have readZeroMap :
      (List.range 32).map
        (fun index => memory.data.getD (continuationOffset + index) 0) =
          (0 : B256).toBytes := by
    simpa [Mem.read, Array.sliceD_eq_map] using readZero
  rcases bytesEq : value.toBytes with _ | ⟨byte, bytes⟩
  · have impossible := B256.length_toBytes value
    rw [bytesEq] at impossible
    simp at impossible
  · have bytesLength : (byte :: bytes).length = 32 := by
      rw [← bytesEq]
      exact B256.length_toBytes _
    simp only [Mem.write]
    split
    case isTrue sizeEnough =>
      split
      case isTrue dataEnough =>
        refine ⟨?_, ?_, sizeCovered⟩
        · change Array.sliceD
            (Array.writeD memory.data offset (byte :: bytes))
            continuationOffset 32 0 = (0 : B256).toBytes
          rw [Array.sliceD_eq_map, ← readZeroMap]
          apply List.map_congr_left
          intro index member
          rw [Array.getD_writeD 0 (byte :: bytes) memory.data offset
            (continuationOffset + index) dataEnough, if_neg]
          have indexLt := List.mem_range.mp member
          omega
        · change continuationOffset + 32 ≤
            (Array.writeD memory.data offset (byte :: bytes)).size
          simpa [Array.size_writeD] using dataCovered
      case isFalse dataShort =>
        let copied := Array.copyD memory.data
          (Array.replicate (offset + (byte :: bytes).length) 0)
        have copiedSize : offset + (byte :: bytes).length ≤ copied.size := by
          change offset + (byte :: bytes).length ≤
            (Array.copyD memory.data
              (Array.replicate (offset + (byte :: bytes).length) 0)).size
          rw [Array.size_copyD, Array.size_replicate]
        refine ⟨?_, ?_, sizeCovered⟩
        · change Array.sliceD
            (Array.writeD copied offset (byte :: bytes))
            continuationOffset 32 0 = (0 : B256).toBytes
          rw [Array.sliceD_eq_map, ← readZeroMap]
          apply List.map_congr_left
          intro index member
          have indexLt := List.mem_range.mp member
          rw [Array.getD_writeD 0 (byte :: bytes) copied offset
            (continuationOffset + index) copiedSize,
            if_neg (by omega)]
          rw [RegisterContinuationZero.getD_copyD_of_lt
            memory.data
            (Array.replicate (offset + (byte :: bytes).length) 0)
            0 (continuationOffset + index) (by omega) (by
              rw [Array.size_replicate]
              omega)]
        · change continuationOffset + 32 ≤
            (Array.writeD copied offset (byte :: bytes)).size
          rw [Array.size_writeD]
          exact Nat.le_trans (by omega) copiedSize
    case isFalse sizeShort =>
      let copied := Array.copyD memory.data
        (Array.replicate
          (ceil32 (offset + (byte :: bytes).length)) 0)
      have copiedSize : offset + (byte :: bytes).length ≤ copied.size := by
        change offset + (byte :: bytes).length ≤
          (Array.copyD memory.data
            (Array.replicate
              (ceil32 (offset + (byte :: bytes).length)) 0)).size
        rw [Array.size_copyD, Array.size_replicate]
        exact Nat.le_ceil32 _
      refine ⟨?_, ?_, ?_⟩
      · change Array.sliceD
          (Array.writeD copied offset (byte :: bytes))
          continuationOffset 32 0 = (0 : B256).toBytes
        rw [Array.sliceD_eq_map, ← readZeroMap]
        apply List.map_congr_left
        intro index member
        have indexLt := List.mem_range.mp member
        rw [Array.getD_writeD 0 (byte :: bytes) copied offset
          (continuationOffset + index) copiedSize,
          if_neg (by omega)]
        rw [RegisterContinuationZero.getD_copyD_of_lt
          memory.data
          (Array.replicate
            (ceil32 (offset + (byte :: bytes).length)) 0)
          0 (continuationOffset + index) (by omega) (by
            rw [Array.size_replicate]
            apply Nat.lt_of_lt_of_le
              (show continuationOffset + index < offset by omega)
            exact Nat.le_trans (Nat.le_add_right _ _)
              (Nat.le_ceil32 _))]
      · change continuationOffset + 32 ≤
          (Array.writeD copied offset (byte :: bytes)).size
        rw [Array.size_writeD]
        exact Nat.le_trans (by omega) copiedSize
      · exact Nat.le_trans (by omega) (Nat.le_ceil32 _)

private theorem RegisterContinuationZero.extend
    {memory : Mem} (zero : RegisterContinuationZero memory)
    (offset size : Nat) :
    RegisterContinuationZero (memory.extend offset size) := by
  rcases zero with ⟨readZero, dataCovered, sizeCovered⟩
  refine ⟨readZero, dataCovered, ?_⟩
  simp only [Mem.extend, memExtSize]
  split
  · exact sizeCovered
  · exact Nat.le_trans sizeCovered <|
      Nat.le_trans (Nat.le_mul_ceilDiv memory.size 32 (by omega)) <|
        Nat.mul_le_mul_left 32 (Nat.le_max_left _ _)

private theorem RegisterContinuationZero.prefix_of_loadWord
    {sevm : Sevm} {pre post : Devm} {xs : Stack}
    (zero : RegisterContinuationZero pre.memory)
    (stackPrefix : xs <<+ pre.stack)
    (run : Line.Run sevm pre (loadWord continuationWord) post) :
    (0 : B256) :: xs <<+ post.stack ∧
      RegisterContinuationZero post.memory := by
  unfold loadWord at run
  rcases Line.of_run_cons run with ⟨pushed, pushRun, rest⟩
  rcases Line.of_run_cons rest with ⟨loaded, loadRun, nilRun⟩
  cases nilRun
  have pushInv := of_run_pushB256 pushRun
  have pushedPrefix :
      (continuationWord * 32) :: xs <<+ pushed.stack :=
    prefix_of_push pushInv stackPrefix
  have pushedZero : RegisterContinuationZero pushed.memory := by
    rw [← pushInv.memory]
    exact zero
  have reads : Mem.Reads pushed.memory pushed.memory.data.toList := by
    intro index
    by_cases bound : index < pushed.memory.data.size <;>
      simp [Array.getD, bound, List.getD_eq_getElem?_getD]
  rcases prefix_of_mload_val loadRun pushedPrefix reads with
    ⟨loadedPrefix, loadedMemory, loadedReturnData⟩
  have valueEq : Bytes.toB256
      (pushed.memory.data.toList.sliceD continuationOffset 32 0) = 0 := by
    rw [← Mem.Reads.read reads continuationOffset 32, pushedZero.1]
    rw [B256.toB256_toBytes]
  have offsetEq : (continuationWord * 32).toNat =
      continuationOffset := rfl
  rw [offsetEq, valueEq] at loadedPrefix
  refine ⟨loadedPrefix, ?_⟩
  rw [loadedMemory, offsetEq]
  exact RegisterContinuationZero.extend pushedZero _ _

private theorem prefix_of_timestamp
    {sevm : Sevm} {pre post : Devm} {xs : Stack}
    (stackPrefix : xs <<+ pre.stack)
    (run : Ninst.Run sevm pre Ninst.timestamp post) :
    sevm.benvStat.time :: xs <<+ post.stack := by
  change Ninst.Run sevm pre (.reg .timestamp) post at run
  rcases of_run_reg run with ⟨pc, instructionRun⟩
  simp only [Rinst.run, Rinst.runCore] at instructionRun
  exact prefix_of_push (Devm.pushBurn_of_pushItem instructionRun) stackPrefix

private theorem heartbeatBodyAuthority
    {dp : DeployParams} {frameRoot write : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor frameRoot (runtime dp)
      initialPath initialSource}
    (bodyCursor : Exec.Deriv.SourceCursor frameRoot (runtime dp) path heartbeat)
    (frameToInitial : Exec.Deriv.ParentPrefix frameRoot initial.node)
    (bodyStorage :
      Devm.getStor bodyCursor.pre = Devm.getStor frameRoot.devm)
    (compiled : some frameRoot.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At write.sevm.code write.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial write (.reg .sstore) bodyCursor) :
    RuntimeWriteAuthority dp frameRoot write .heartbeatExpiry := by
  let endpoint := RuntimeEndpointOccurrence.ofCursor
    frameToInitial bodyCursor route
  unfold heartbeat at bodyCursor route
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
      (by intro h; cases h) with
    ⟨callerChronology, countPushCursor, callerEdge, countPushRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne countPushRoute
      (by intro h; cases h) with
    ⟨countPushChronology, countOrCursor, countPushEdge, countOrRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne countOrRoute
      (by intro h; cases h) with
    ⟨countOrChronology, countLoadCursor, countOrEdge, countLoadRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne countLoadRoute
      (by intro h; cases h) with
    ⟨countLoadChronology, registeredCursor, countLoadEdge,
      registeredRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne registeredRoute
      (by intro h; cases h) with
    ⟨registeredChronology, registeredBranchCursor, registeredEdge,
      registeredBranchRoute⟩
  have callerRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge bodyCursor callerEdge
  have countPushRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
      countPushCursor countPushEdge
  have countOrRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge countOrCursor countOrEdge
  have countLoadRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
      countLoadCursor countLoadEdge
  have registeredRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
      registeredCursor registeredEdge
  have callerPrefix :
      [frameRoot.sevm.caller.toB256] <<+ countPushCursor.pre.stack :=
    prefix_of_push (of_run_caller callerRun) nil_pref
  have countRegionPrefix :
      [regionWord countRegion, frameRoot.sevm.caller.toB256] <<+
        countOrCursor.pre.stack := by
    simpa [Ninst.pushB256] using
      prefix_of_push (of_run_pushB256 countPushRun) callerPrefix
  have countKeyPrefix :
      [countSlot frameRoot.sevm.caller.toB256] <<+
        countLoadCursor.pre.stack := by
    change [(regionWord countRegion ||| frameRoot.sevm.caller.toB256)] <<+
      countLoadCursor.pre.stack
    exact prefix_of_or countOrRun countRegionPrefix
  rcases prefix_of_sload countLoadRun countKeyPrefix with
    ⟨count, countPrefix, countEq⟩
  have registeredPrefix :
      [(count =? 0)] <<+ registeredBranchCursor.pre.stack :=
    prefix_of_iszero registeredRun countPrefix
  have countPrefixStorage :
      Devm.getStor bodyCursor.pre = Devm.getStor countLoadCursor.pre :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons callerRun
        (Line.Run.cons countPushRun
          (Line.Run.cons countOrRun Line.Run.nil)))
  have countRootEq :
      count = frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
        (countSlot frameRoot.sevm.caller.toB256) := by
    rw [countEq]
    show (Devm.getStor countLoadCursor.pre frameRoot.sevm.currentTarget).get
        (countSlot frameRoot.sevm.caller.toB256) =
      (Devm.getStor frameRoot.devm frameRoot.sevm.currentTarget).get
        (countSlot frameRoot.sevm.caller.toB256)
    rw [countPrefixStorage.symm.trans bodyStorage]
  rcases Exec.Deriv.SourceCursor.Toward.branchArmStorage
      registeredBranchCursor compiled targetAt registeredBranchRoute with
    ⟨liveArmCursor, liveArmRoute, registeredBranchStorage, zeroPrefix⟩ |
      ⟨registeredFlag, registeredNonzero, registeredFlagPrefix,
        errorCursor, errorRoute, registeredBranchStorage⟩
  · have registeredFlagEq : (count =? 0) = 0 :=
      pref_head_unique registeredPrefix zeroPrefix
    have countNe :
        frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
          (countSlot frameRoot.sevm.caller.toB256) ≠ 0 := by
      rw [← countRootEq]
      intro countZero
      rw [countZero] at registeredFlagEq
      have oneZero : (1 : B256) = 0 := by
        simpa [B256.eqCheck] using registeredFlagEq
      exact B256.zero_ne_one oneZero.symm
    have countFullStorage :
        Devm.getStor bodyCursor.pre =
          Devm.getStor registeredBranchCursor.pre :=
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons callerRun
          (Line.Run.cons countPushRun
            (Line.Run.cons countOrRun
              (Line.Run.cons countLoadRun
                (Line.Run.cons registeredRun Line.Run.nil)))))
    rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne liveArmRoute
        (by intro h; cases h) with
      ⟨expiryCallerChronology, expiryPushCursor, expiryCallerEdge,
        expiryPushRoute⟩
    rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
        expiryPushRoute (by intro h; cases h) with
      ⟨expiryPushChronology, expiryOrCursor, expiryPushEdge,
        expiryOrRoute⟩
    rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne expiryOrRoute
        (by intro h; cases h) with
      ⟨expiryOrChronology, expiryLoadCursor, expiryOrEdge,
        expiryLoadRoute⟩
    rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
        expiryLoadRoute (by intro h; cases h) with
      ⟨expiryLoadChronology, timestampCursor, expiryLoadEdge,
        timestampRoute⟩
    rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne timestampRoute
        (by intro h; cases h) with
      ⟨timestampChronology, liveCursor, timestampEdge, liveRoute⟩
    rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne liveRoute
        (by intro h; cases h) with
      ⟨liveChronology, liveBranchCursor, liveEdge, liveBranchRoute⟩
    have expiryCallerRun :=
      Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        liveArmCursor expiryCallerEdge
    have expiryPushRun :=
      Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        expiryPushCursor expiryPushEdge
    have expiryOrRun :=
      Exec.Deriv.SourceCursor.ninstRun_of_nextEdge expiryOrCursor expiryOrEdge
    have expiryLoadRun :=
      Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        expiryLoadCursor expiryLoadEdge
    have timestampRun :=
      Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        timestampCursor timestampEdge
    have liveRun :=
      Exec.Deriv.SourceCursor.ninstRun_of_nextEdge liveCursor liveEdge
    have expiryCallerPrefix :
        [frameRoot.sevm.caller.toB256] <<+ expiryPushCursor.pre.stack :=
      prefix_of_push (of_run_caller expiryCallerRun) nil_pref
    have expiryRegionPrefix :
        [regionWord expiryRegion, frameRoot.sevm.caller.toB256] <<+
          expiryOrCursor.pre.stack := by
      simpa [Ninst.pushB256] using
        prefix_of_push (of_run_pushB256 expiryPushRun) expiryCallerPrefix
    have expiryKeyPrefix :
        [expirySlot frameRoot.sevm.caller.toB256] <<+
          expiryLoadCursor.pre.stack := by
      change [(regionWord expiryRegion ||| frameRoot.sevm.caller.toB256)] <<+
        expiryLoadCursor.pre.stack
      exact prefix_of_or expiryOrRun expiryRegionPrefix
    rcases prefix_of_sload expiryLoadRun expiryKeyPrefix with
      ⟨expiry, expiryPrefix, expiryEq⟩
    have timestampPrefix :
        [frameRoot.sevm.benvStat.time, expiry] <<+
          liveCursor.pre.stack :=
      prefix_of_timestamp expiryPrefix timestampRun
    have livePrefix :
        [(frameRoot.sevm.benvStat.time <? expiry)] <<+
          liveBranchCursor.pre.stack :=
      prefix_of_lt liveRun timestampPrefix
    have expiryPrefixStorage :
        Devm.getStor liveArmCursor.pre =
          Devm.getStor expiryLoadCursor.pre :=
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons expiryCallerRun
          (Line.Run.cons expiryPushRun
            (Line.Run.cons expiryOrRun Line.Run.nil)))
    have expiryRootEq :
        expiry = frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
          (expirySlot frameRoot.sevm.caller.toB256) := by
      rw [expiryEq]
      show (Devm.getStor expiryLoadCursor.pre frameRoot.sevm.currentTarget).get
          (expirySlot frameRoot.sevm.caller.toB256) =
        (Devm.getStor frameRoot.devm frameRoot.sevm.currentTarget).get
          (expirySlot frameRoot.sevm.caller.toB256)
      rw [expiryPrefixStorage.symm, registeredBranchStorage.symm,
        countFullStorage.symm, bodyStorage]
    rcases Exec.Deriv.SourceCursor.Toward.branchArmStorage
        liveBranchCursor compiled targetAt liveBranchRoute with
      ⟨expiredCursor, expiredRoute, liveBranchStorage, zeroPrefix⟩ |
        ⟨liveFlag, liveNonzero, liveFlagPrefix, successCursor,
          successRoute, liveBranchStorage⟩
    · exact (expiredCursor.noSstore_of_entrySstoreFree compiled
        [heartbeatExpiredErrorSlot] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology
          expiredRoute).cursorToTarget targetAt).elim
    · have liveFlagEq :
          (frameRoot.sevm.benvStat.time <? expiry) = liveFlag :=
        pref_head_unique livePrefix liveFlagPrefix
      have liveLt : frameRoot.sevm.benvStat.time <
          frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
            (expirySlot frameRoot.sevm.caller.toB256) := by
        rw [← expiryRootEq]
        by_contra notLt
        have zero : (frameRoot.sevm.benvStat.time <? expiry) = 0 := by
          simp [B256.ltCheck, notLt]
        exact liveNonzero (liveFlagEq ▸ zero)
      let registeredOccurrence := RuntimeGuardOccurrence.ofCursor
        frameToInitial registeredChronology registeredEdge registeredRun
          targetAt (by intro h; cases h)
      let liveOccurrence := RuntimeGuardOccurrence.ofCursor
        frameToInitial liveChronology liveEdge liveRun targetAt
          (by intro h; cases h)
      exact .heartbeatExpiry endpoint registeredOccurrence liveOccurrence
        countNe liveLt
  · exact (errorCursor.noSstore_of_entrySstoreFree compiled
      [senderNotPauserErrorSlot] rfl
      (Exec.Deriv.SourceCursor.Toward.chronology
        errorRoute).cursorToTarget targetAt).elim

private inductive RuntimeDispatchCut.ConfigurationOrHeartbeat
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)} : RuntimeDispatchCut initial → Prop
  | setPauseDuration {path : Prog.SourcePath}
      (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
        (Blanc.LidoCircuitBreaker.setPauseDuration dp))
      (route : Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) cursor)
      (entryStorage : Devm.getStor cursor.pre = Devm.getStor initial.pre) :
      ConfigurationOrHeartbeat
        (RuntimeDispatchCut.setPauseDuration cursor route entryStorage)
  | setHeartbeatInterval {path : Prog.SourcePath}
      (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
        (Blanc.LidoCircuitBreaker.setHeartbeatInterval dp))
      (route : Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) cursor)
      (entryStorage : Devm.getStor cursor.pre = Devm.getStor initial.pre) :
      ConfigurationOrHeartbeat
        (RuntimeDispatchCut.setHeartbeatInterval cursor route entryStorage)
  | heartbeat {path : Prog.SourcePath}
      (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
        Blanc.LidoCircuitBreaker.heartbeat)
      (route : Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) cursor)
      (entryStorage : Devm.getStor cursor.pre = Devm.getStor initial.pre) :
      ConfigurationOrHeartbeat
        (RuntimeDispatchCut.heartbeat cursor route entryStorage)

private theorem runtimeDispatchCut_configurationOrHeartbeatAuthority
    {dp : DeployParams} {frameRoot write : Exec.Deriv}
    (mainCursor : Exec.Deriv.SourceCursor frameRoot (runtime dp)
      ⟨0, []⟩ (runtimeMain dp))
    (frameToMain : Exec.Deriv.ParentPrefix frameRoot mainCursor.node)
    (mainStorage :
      Devm.getStor mainCursor.pre = Devm.getStor frameRoot.devm)
    (compiled : some frameRoot.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At write.sevm.code write.pc (.reg .sstore))
    (row : RuntimePersistentWrite) (site : Prog.SourceSite)
    (found : row.sourceSite? dp = some site)
    (sitePc : site.pc = write.pc)
    (cut : RuntimeDispatchCut (target := write) mainCursor)
    (selected : RuntimeDispatchCut.ConfigurationOrHeartbeat cut) :
    ∃ role : InvocationRole,
      role ∈ row.permittedRoles ∧
        RuntimeWriteAuthority dp frameRoot write role := by
  cases selected with
  | setPauseDuration cursor route entryStorage =>
      let endpoint := RuntimeEndpointOccurrence.ofCursor
        frameToMain cursor route
      rcases requireStaticOnlyAdminGuard 1 cursor compiled targetAt route with
        ⟨guardPath, guardTail, guardCursor, branchCursor,
          guardChronology, guardEdge, guardRun, branchRoute, callerEq⟩
      let guard := RuntimeGuardOccurrence.ofCursor frameToMain
        guardChronology guardEdge guardRun targetAt (by intro h; cases h)
      rcases requireStaticArgsToward 1 cursor compiled targetAt route with
        ⟨adminPath, adminCursor, adminRoute⟩
      rcases onlyAdminToward adminCursor compiled targetAt adminRoute with
        ⟨tailPath, tailCursor, tailRoute⟩
      rcases configurationSetterTarget
          dp.minPauseDuration dp.maxPauseDuration
          pauseDurationUpdatedEvent pauseDurationSlot
          pauseBelowMinErrorSlot pauseAboveMaxErrorSlot rfl rfl
          tailCursor compiled targetAt tailRoute with
        ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
          functionEq, suffixSteps, finalSteps, suffixEq⟩
      have exactSteps : finalPath.steps =
          tailPath.steps ++ configurationStoreSuffix := by
        rw [finalSteps, suffixEq]
        rfl
      have rowEq := configurationRow_of_terminal finalCursor found sitePc
        targetEq sourceMember exactSteps
      refine ⟨.adminConfiguration, ?_,
        .setPauseDuration endpoint guard callerEq⟩
      rcases rowEq with rfl | rfl <;>
        simp [RuntimePersistentWrite.permittedRoles]
  | setHeartbeatInterval cursor route entryStorage =>
      let endpoint := RuntimeEndpointOccurrence.ofCursor
        frameToMain cursor route
      rcases setHeartbeatIntervalBodyGuard rfl cursor compiled targetAt route with
        ⟨guardPath, guardTail, guardCursor, branchCursor,
          guardChronology, guardEdge, guardRun, branchRoute, callerEq⟩
      let guard := RuntimeGuardOccurrence.ofCursor frameToMain
        guardChronology guardEdge guardRun targetAt (by intro h; cases h)
      rcases requireStaticArgsToward 1 cursor compiled targetAt route with
        ⟨adminPath, adminCursor, adminRoute⟩
      rcases onlyAdminToward adminCursor compiled targetAt adminRoute with
        ⟨tailPath, tailCursor, tailRoute⟩
      rcases configurationSetterTarget
          dp.minHeartbeatInterval dp.maxHeartbeatInterval
          heartbeatIntervalUpdatedEvent heartbeatIntervalSlot
          heartbeatBelowMinErrorSlot heartbeatAboveMaxErrorSlot rfl rfl
          tailCursor compiled targetAt tailRoute with
        ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
          functionEq, suffixSteps, finalSteps, suffixEq⟩
      have exactSteps : finalPath.steps =
          tailPath.steps ++ configurationStoreSuffix := by
        rw [finalSteps, suffixEq]
        rfl
      have rowEq := configurationRow_of_terminal finalCursor found sitePc
        targetEq sourceMember exactSteps
      refine ⟨.adminConfiguration, ?_,
        .setHeartbeatInterval endpoint guard callerEq⟩
      rcases rowEq with rfl | rfl <;>
        simp [RuntimePersistentWrite.permittedRoles]
  | heartbeat cursor route entryStorage =>
      rcases heartbeatTarget cursor compiled targetAt route with
        ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
          finalSteps⟩
      have rowEq := heartbeatRow_of_terminal finalCursor found sitePc
        targetEq sourceMember finalSteps
      subst row
      exact ⟨.heartbeatExpiry, by
          simp [RuntimePersistentWrite.permittedRoles],
        heartbeatBodyAuthority cursor frameToMain
          (entryStorage.trans mainStorage) compiled targetAt route⟩

private inductive PauseAuthorityEvidence
    (dp : DeployParams) (frameRoot write : Exec.Deriv) : Prop
  | intro
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write pause)
      (assignedGuard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (liveGuard : RuntimeGuardOccurrence frameRoot write (.reg .lt))
      (assigned : frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
        (assignmentSlot (Sevm.dataWord frameRoot.sevm 4)) =
          frameRoot.sevm.caller.toB256)
      (live : frameRoot.sevm.benvStat.time < frameRoot.devm.getStorVal
        frameRoot.sevm.currentTarget
        (expirySlot frameRoot.sevm.caller.toB256)) :
      PauseAuthorityEvidence dp frameRoot write

private theorem pauseBodyAuthorityEvidence
    {dp : DeployParams} {frameRoot write : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor frameRoot (runtime dp)
      initialPath initialSource}
    (bodyCursor : Exec.Deriv.SourceCursor frameRoot (runtime dp) path pause)
    (frameToInitial : Exec.Deriv.ParentPrefix frameRoot initial.node)
    (bodyStorage :
      Devm.getStor bodyCursor.pre = Devm.getStor frameRoot.devm)
    (compiled : some frameRoot.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At write.sevm.code write.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial write (.reg .sstore) bodyCursor) :
    PauseAuthorityEvidence dp frameRoot write := by
  let endpoint := RuntimeEndpointOccurrence.ofCursor
    frameToInitial bodyCursor route
  rcases requireStaticArgsTowardStorage 1 bodyCursor compiled targetAt route with
    ⟨canonicalPath, canonicalCursor, canonicalRoute, bodyToCanonical⟩
  rcases canonicalAddressArgTowardStorage 0 canonicalCursor compiled targetAt
      canonicalRoute with
    ⟨corePath, coreCursor, coreRoute, canonicalToCore⟩
  have coreStorage :
      Devm.getStor coreCursor.pre = Devm.getStor frameRoot.devm :=
    canonicalToCore.symm.trans (bodyToCanonical.symm.trans bodyStorage)
  unfold pause at bodyCursor
  change Exec.Deriv.SourceCursor frameRoot (runtime dp) corePath
    (Ninst.pushB256 lockKey ::: Ninst.tload ::: Ninst.iszero :::
      ((Ninst.pushB256 1 ::: Ninst.pushB256 lockKey ::: Ninst.tstore :::
        arg 0 +++ tagTop assignmentRegion +++ Ninst.sload :::
          Ninst.caller ::: Ninst.eq :::
        ((Ninst.caller ::: tagTop expiryRegion +++ Ninst.sload :::
          Ninst.timestamp ::: Ninst.lt :::
          ((Ninst.pushB256 pauseDurationSlot ::: Ninst.sload :::
            mstoreAt durationWord +++
            arg 0 +++ mstoreAt targetWord +++
            Ninst.pushB256 0 ::: mstoreAt newPauserWord +++
            Ninst.pushB256 0 ::: mstoreAt previousPauserWord +++
            Ninst.pushB256 1 ::: mstoreAt continuationWord +++
            .call setPauserSlot) <?> (.call heartbeatExpiredErrorSlot))) <?>
          (.call senderNotPauserErrorSlot))) <?>
        (.call reentrantCallErrorSlot))) at coreCursor
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne coreRoute
      (by intro h; cases h) with
    ⟨lockPushChronology, lockLoadCursor, lockPushEdge, lockLoadRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne lockLoadRoute
      (by intro h; cases h) with
    ⟨lockLoadChronology, lockZeroCursor, lockLoadEdge, lockZeroRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne lockZeroRoute
      (by intro h; cases h) with
    ⟨lockZeroChronology, lockBranchCursor, lockZeroEdge, lockBranchRoute⟩
  have lockPushRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge coreCursor lockPushEdge
  have lockLoadRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge lockLoadCursor lockLoadEdge
  have lockZeroRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge lockZeroCursor lockZeroEdge
  have lockPrefixStorage :
      Devm.getStor coreCursor.pre = Devm.getStor lockBranchCursor.pre :=
    Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons lockPushRun
        (Line.Run.cons lockLoadRun
          (Line.Run.cons lockZeroRun Line.Run.nil)))
  rcases Exec.Deriv.SourceCursor.Toward.branchArmStorage
      lockBranchCursor compiled targetAt lockBranchRoute with
    ⟨reentrantCursor, reentrantRoute, lockBranchStorage, zeroPrefix⟩ |
      ⟨lockFlag, lockNonzero, lockFlagPrefix, unlockedCursor,
        unlockedRoute, lockBranchStorage⟩
  · exact (reentrantCursor.noSstore_of_entrySstoreFree compiled
      [reentrantCallErrorSlot] rfl
      (Exec.Deriv.SourceCursor.Toward.chronology
        reentrantRoute).cursorToTarget targetAt).elim
  · rcases Exec.Deriv.SourceCursor.Toward.dropLineRun unlockedRoute
        (line := [Ninst.pushB256 1, Ninst.pushB256 lockKey, Ninst.tstore])
        (by
          intro instruction member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl <;> intro h <;> cases h) with
      ⟨argPath, argCursor, setupRun, argChronology, argRoute⟩
    have setupStorage :
        Devm.getStor unlockedCursor.pre = Devm.getStor argCursor.pre :=
      Line.of_inv Devm.getStor (by line_inv) setupRun
    rcases Exec.Deriv.SourceCursor.Toward.dropLineRun argRoute
        (line := arg 0) (by simp [arg, cdl, Ninst.pushB256]) with
      ⟨assignmentPushPath, assignmentPushCursor, argRun,
        assignmentPushChronology, assignmentPushRoute⟩
    have argumentPrefix :
        [Sevm.dataWord frameRoot.sevm 4] <<+
          assignmentPushCursor.pre.stack := by
      have hzero : (32 : B256) * 0 + 4 = 4 := by rfl
      simpa [Sevm.argWord, hzero] using
        prefix_of_arg (e := frameRoot.sevm) nil_pref argRun
    have argStorage :
        Devm.getStor argCursor.pre =
          Devm.getStor assignmentPushCursor.pre :=
      Line.of_inv Devm.getStor (by line_inv) argRun
    rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
        assignmentPushRoute (by intro h; cases h) with
      ⟨assignmentPushChronology, assignmentOrCursor, assignmentPushEdge,
        assignmentOrRoute⟩
    rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
        assignmentOrRoute (by intro h; cases h) with
      ⟨assignmentOrChronology, assignmentLoadCursor, assignmentOrEdge,
        assignmentLoadRoute⟩
    rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
        assignmentLoadRoute (by intro h; cases h) with
      ⟨assignmentLoadChronology, assignmentCallerCursor,
        assignmentLoadEdge, assignmentCallerRoute⟩
    rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
        assignmentCallerRoute (by intro h; cases h) with
      ⟨assignmentCallerChronology, assignmentEqCursor,
        assignmentCallerEdge, assignmentEqRoute⟩
    rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
        assignmentEqRoute (by intro h; cases h) with
      ⟨assignmentEqChronology, assignmentBranchCursor, assignmentEqEdge,
        assignmentBranchRoute⟩
    have assignmentPushRun :=
      Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        assignmentPushCursor assignmentPushEdge
    have assignmentOrRun :=
      Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        assignmentOrCursor assignmentOrEdge
    have assignmentLoadRun :=
      Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        assignmentLoadCursor assignmentLoadEdge
    have assignmentCallerRun :=
      Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        assignmentCallerCursor assignmentCallerEdge
    have assignmentEqRun :=
      Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        assignmentEqCursor assignmentEqEdge
    have assignmentRegionPrefix :
        [regionWord assignmentRegion, Sevm.dataWord frameRoot.sevm 4] <<+
          assignmentOrCursor.pre.stack := by
      simpa [Ninst.pushB256] using
        prefix_of_push (of_run_pushB256 assignmentPushRun) argumentPrefix
    have assignmentKeyPrefix :
        [assignmentSlot (Sevm.dataWord frameRoot.sevm 4)] <<+
          assignmentLoadCursor.pre.stack := by
      change [(regionWord assignmentRegion |||
        Sevm.dataWord frameRoot.sevm 4)] <<+
          assignmentLoadCursor.pre.stack
      exact prefix_of_or assignmentOrRun assignmentRegionPrefix
    rcases prefix_of_sload assignmentLoadRun assignmentKeyPrefix with
      ⟨assigned, assignedPrefix, assignedEq⟩
    have assignmentCallerPrefix :
        [frameRoot.sevm.caller.toB256, assigned] <<+
          assignmentEqCursor.pre.stack :=
      prefix_of_push (of_run_caller assignmentCallerRun) assignedPrefix
    have assignmentEqPrefix :
        [(frameRoot.sevm.caller.toB256 =? assigned)] <<+
          assignmentBranchCursor.pre.stack :=
      prefix_of_eq assignmentEqRun assignmentCallerPrefix
    have assignmentKeyStorage :
        Devm.getStor assignmentPushCursor.pre =
          Devm.getStor assignmentLoadCursor.pre :=
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons assignmentPushRun
          (Line.Run.cons assignmentOrRun Line.Run.nil))
    have assignedRootEq : assigned =
        frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
          (assignmentSlot (Sevm.dataWord frameRoot.sevm 4)) := by
      rw [assignedEq]
      show (Devm.getStor assignmentLoadCursor.pre
          frameRoot.sevm.currentTarget).get
            (assignmentSlot (Sevm.dataWord frameRoot.sevm 4)) =
        (Devm.getStor frameRoot.devm frameRoot.sevm.currentTarget).get
          (assignmentSlot (Sevm.dataWord frameRoot.sevm 4))
      rw [assignmentKeyStorage.symm, argStorage.symm, setupStorage.symm,
        lockBranchStorage.symm, lockPrefixStorage.symm, coreStorage]
    have assignmentGuardStorage :
        Devm.getStor assignmentLoadCursor.pre =
          Devm.getStor assignmentBranchCursor.pre :=
      Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons assignmentLoadRun
          (Line.Run.cons assignmentCallerRun
            (Line.Run.cons assignmentEqRun Line.Run.nil)))
    rcases Exec.Deriv.SourceCursor.Toward.branchArmStorage
        assignmentBranchCursor compiled targetAt assignmentBranchRoute with
      ⟨senderErrorCursor, senderErrorRoute, assignmentBranchStorage,
        zeroPrefix⟩ |
        ⟨assignmentFlag, assignmentNonzero, assignmentFlagPrefix,
          liveArmCursor, liveArmRoute, assignmentBranchStorage⟩
    · exact (senderErrorCursor.noSstore_of_entrySstoreFree compiled
        [senderNotPauserErrorSlot] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology
          senderErrorRoute).cursorToTarget targetAt).elim
    · have assignmentFlagEq :
          (frameRoot.sevm.caller.toB256 =? assigned) = assignmentFlag :=
        pref_head_unique assignmentEqPrefix assignmentFlagPrefix
      have assignedCaller : assigned = frameRoot.sevm.caller.toB256 := by
        by_contra different
        have checkZero :
            (frameRoot.sevm.caller.toB256 =? assigned) = 0 := by
          simp [B256.eqCheck, Ne.symm different]
        exact assignmentNonzero (assignmentFlagEq ▸ checkZero)
      have assignedAtEntry :
          frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
              (assignmentSlot (Sevm.dataWord frameRoot.sevm 4)) =
            frameRoot.sevm.caller.toB256 := by
        rw [← assignedRootEq, assignedCaller]
      rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
          liveArmRoute (by intro h; cases h) with
        ⟨expiryCallerChronology, expiryPushCursor, expiryCallerEdge,
          expiryPushRoute⟩
      rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
          expiryPushRoute (by intro h; cases h) with
        ⟨expiryPushChronology, expiryOrCursor, expiryPushEdge,
          expiryOrRoute⟩
      rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
          expiryOrRoute (by intro h; cases h) with
        ⟨expiryOrChronology, expiryLoadCursor, expiryOrEdge,
          expiryLoadRoute⟩
      rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
          expiryLoadRoute (by intro h; cases h) with
        ⟨expiryLoadChronology, timestampCursor, expiryLoadEdge,
          timestampRoute⟩
      rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
          timestampRoute (by intro h; cases h) with
        ⟨timestampChronology, liveCursor, timestampEdge, liveRoute⟩
      rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne liveRoute
          (by intro h; cases h) with
        ⟨liveChronology, liveBranchCursor, liveEdge, liveBranchRoute⟩
      have expiryCallerRun :=
        Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
          liveArmCursor expiryCallerEdge
      have expiryPushRun :=
        Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
          expiryPushCursor expiryPushEdge
      have expiryOrRun :=
        Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
          expiryOrCursor expiryOrEdge
      have expiryLoadRun :=
        Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
          expiryLoadCursor expiryLoadEdge
      have timestampRun :=
        Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
          timestampCursor timestampEdge
      have liveRun :=
        Exec.Deriv.SourceCursor.ninstRun_of_nextEdge liveCursor liveEdge
      have expiryCallerPrefix :
          [frameRoot.sevm.caller.toB256] <<+ expiryPushCursor.pre.stack :=
        prefix_of_push (of_run_caller expiryCallerRun) nil_pref
      have expiryRegionPrefix :
          [regionWord expiryRegion, frameRoot.sevm.caller.toB256] <<+
            expiryOrCursor.pre.stack := by
        simpa [Ninst.pushB256] using
          prefix_of_push (of_run_pushB256 expiryPushRun) expiryCallerPrefix
      have expiryKeyPrefix :
          [expirySlot frameRoot.sevm.caller.toB256] <<+
            expiryLoadCursor.pre.stack := by
        change [(regionWord expiryRegion |||
          frameRoot.sevm.caller.toB256)] <<+ expiryLoadCursor.pre.stack
        exact prefix_of_or expiryOrRun expiryRegionPrefix
      rcases prefix_of_sload expiryLoadRun expiryKeyPrefix with
        ⟨expiry, expiryPrefix, expiryEq⟩
      have timestampPrefix :
          [frameRoot.sevm.benvStat.time, expiry] <<+ liveCursor.pre.stack :=
        prefix_of_timestamp expiryPrefix timestampRun
      have livePrefix :
          [(frameRoot.sevm.benvStat.time <? expiry)] <<+
            liveBranchCursor.pre.stack :=
        prefix_of_lt liveRun timestampPrefix
      have expiryPrefixStorage :
          Devm.getStor liveArmCursor.pre =
            Devm.getStor expiryLoadCursor.pre :=
        Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons expiryCallerRun
            (Line.Run.cons expiryPushRun
              (Line.Run.cons expiryOrRun Line.Run.nil)))
      have expiryRootEq : expiry =
          frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
            (expirySlot frameRoot.sevm.caller.toB256) := by
        rw [expiryEq]
        show (Devm.getStor expiryLoadCursor.pre
            frameRoot.sevm.currentTarget).get
              (expirySlot frameRoot.sevm.caller.toB256) =
          (Devm.getStor frameRoot.devm frameRoot.sevm.currentTarget).get
            (expirySlot frameRoot.sevm.caller.toB256)
        rw [expiryPrefixStorage.symm, assignmentBranchStorage.symm,
          assignmentGuardStorage.symm, assignmentKeyStorage.symm,
          argStorage.symm, setupStorage.symm, lockBranchStorage.symm,
          lockPrefixStorage.symm, coreStorage]
      rcases Exec.Deriv.SourceCursor.Toward.branchArmStorage
          liveBranchCursor compiled targetAt liveBranchRoute with
        ⟨expiredCursor, expiredRoute, liveBranchStorage, zeroPrefix⟩ |
          ⟨liveFlag, liveNonzero, liveFlagPrefix, successCursor,
            successRoute, liveBranchStorage⟩
      · exact (expiredCursor.noSstore_of_entrySstoreFree compiled
          [heartbeatExpiredErrorSlot] rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            expiredRoute).cursorToTarget targetAt).elim
      · have liveFlagEq :
            (frameRoot.sevm.benvStat.time <? expiry) = liveFlag :=
          pref_head_unique livePrefix liveFlagPrefix
        have liveAtEntry : frameRoot.sevm.benvStat.time <
            frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
              (expirySlot frameRoot.sevm.caller.toB256) := by
          rw [← expiryRootEq]
          by_contra notLt
          have zero : (frameRoot.sevm.benvStat.time <? expiry) = 0 := by
            simp [B256.ltCheck, notLt]
          exact liveNonzero (liveFlagEq ▸ zero)
        let assignedOccurrence := RuntimeGuardOccurrence.ofCursor
          frameToInitial assignmentEqChronology assignmentEqEdge
            assignmentEqRun targetAt (by intro h; cases h)
        let liveOccurrence := RuntimeGuardOccurrence.ofCursor
          frameToInitial liveChronology liveEdge liveRun targetAt
            (by intro h; cases h)
        exact .intro endpoint assignedOccurrence liveOccurrence
          assignedAtEntry liveAtEntry

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
