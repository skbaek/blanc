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
`permittedRoles`; this payload alone does not classify a source site.

**Every** constructor also pins its own write's persistent source site into a
set of source function indices — `writeSite` below.  That conjunct is what lets
a consumer refute a `permittedRoles` widening without constructing an
execution: compiled PCs identify persistent source sites
(`runtimePersistentSourceSite_eq_of_pc`), so a role whose `writeSite` misses the
row's frozen `sourceFunctionIndex` cannot hold at that row.  The pin is a
function-index pin and nothing finer, so it separates the configuration/
heartbeat functions (index `0`) from the registry functions (`14`, `15`, `16`,
`17`) and from the two expiry functions (`registerAfterSetSlot`,
`pauseAfterSetSlot`), but it does *not* separate two roles that live in the
same compiled function — `.adminConfiguration` and `.heartbeatExpiry` both sit
in the main function and are not told apart here. -/
inductive RuntimeWriteAuthority
    (dp : DeployParams) (frameRoot write : Exec.Deriv) :
    InvocationRole → Prop
  | setPauseDuration
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write
        (setPauseDuration dp))
      (guard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (callerEq : frameRoot.sevm.caller.toB256 = dp.admin)
      (writeSite : ∃ site ∈ runtimePersistentSourceSites dp,
        site.pc = write.pc ∧ site.path.functionIndex = 0) :
      RuntimeWriteAuthority dp frameRoot write .adminConfiguration
  | setHeartbeatInterval
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write
        (setHeartbeatInterval dp))
      (guard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (callerEq : frameRoot.sevm.caller.toB256 = dp.admin)
      (writeSite : ∃ site ∈ runtimePersistentSourceSites dp,
        site.pc = write.pc ∧ site.path.functionIndex = 0) :
      RuntimeWriteAuthority dp frameRoot write .adminConfiguration
  | adminRegistry
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write
        (registerPauser dp))
      (guard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (callerEq : frameRoot.sevm.caller.toB256 = dp.admin)
      (writeSite : ∃ site ∈ runtimePersistentSourceSites dp,
        site.pc = write.pc ∧ site.path.functionIndex ∈ [14, 15, 16, 17]) :
      RuntimeWriteAuthority dp frameRoot write .adminRegistry
  | adminExpiry
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write
        (registerPauser dp))
      (guard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (callerEq : frameRoot.sevm.caller.toB256 = dp.admin)
      (writeSite : ∃ site ∈ runtimePersistentSourceSites dp,
        site.pc = write.pc ∧ site.path.functionIndex = registerAfterSetSlot) :
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
        (expirySlot frameRoot.sevm.caller.toB256))
      (writeSite : ∃ site ∈ runtimePersistentSourceSites dp,
        site.pc = write.pc ∧ site.path.functionIndex = 0) :
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
        (expirySlot frameRoot.sevm.caller.toB256))
      (writeSite : ∃ site ∈ runtimePersistentSourceSites dp,
        site.pc = write.pc ∧ site.path.functionIndex ∈ [14, 15, 17]) :
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
        (expirySlot frameRoot.sevm.caller.toB256))
      (writeSite : ∃ site ∈ runtimePersistentSourceSites dp,
        site.pc = write.pc ∧ site.path.functionIndex = pauseAfterSetSlot) :
      RuntimeWriteAuthority dp frameRoot write .pauseExpiry

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

/-- Frozen source function index per row.  Public because the attainment
consumers need it to refute a role at a row whose write sits in a different
compiled function; see `RuntimeWriteAuthority`'s `writeSite` conjuncts. -/
def RuntimePersistentWrite.sourceFunctionIndex :
    RuntimePersistentWrite → Nat
  | .setPauseDurationConfig | .setHeartbeatIntervalConfig
  | .heartbeatExpiry => 0
  | .setPauserAssignment | .setPauserOldCount => 14
  | .appendArrayEntry | .appendReverseIndex | .appendArrayLength => 15
  | .afterOldNewCount => 16
  | .removeArrayHole | .removeMovedIndex | .removeClearTail
  | .removeArrayLength | .removeClearTargetIndex => 17
  | .registerRetainedOldNewExpiry | .registerLastOldClear
  | .registerLastOldNewExpiry | .registerFreshExpiry => 19
  | .pauseRetainedTargetExpiry | .pauseLastTargetExpiry => 20

/-- A row's nominated site sits in the row's frozen source function. -/
theorem RuntimePersistentWrite.sourceSite?_functionIndex
    {dp : DeployParams} {row : RuntimePersistentWrite}
    {site : Prog.SourceSite}
    (found : row.sourceSite? dp = some site) :
    site.path.functionIndex = row.sourceFunctionIndex := by
  have sitesEq := runtimePersistentSourceSites_eq_official dp
  unfold RuntimePersistentWrite.sourceSite? at found
  rw [sitesEq] at found
  cases row <;> decide +kernel +revert

/-- Compiled PCs identify persistent source sites: the twenty PCs are `Nodup`,
so two listed sites sharing one PC are the same site.  This is what turns a
role's `writeSite` index constraint into a refutation at a row in a different
compiled function. -/
theorem runtimePersistentSourceSite_eq_of_pc
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

/-- Admin registry authority and admin expiry authority can never both hold at
one runtime write.  Each role pins the write's own persistent source site to a
disjoint set of source function indices, so a registry witness cannot be
repacked as an expiry witness — which is exactly what makes an admin role-swap
mutant fail rather than typecheck. -/
theorem RuntimeWriteAuthority.adminRegistry_not_adminExpiry
    {dp : DeployParams} {frameRoot write : Exec.Deriv} :
    RuntimeWriteAuthority dp frameRoot write .adminRegistry →
      ¬ RuntimeWriteAuthority dp frameRoot write .adminExpiry := by
  intro registry expiry
  cases registry with
  | adminRegistry _ _ _ registrySite =>
      cases expiry with
      | adminExpiry _ _ _ expirySite =>
          rcases registrySite with
            ⟨registryWrite, registryMem, registryPc, registryIndex⟩
          rcases expirySite with
            ⟨expiryWrite, expiryMem, expiryPc, expiryIndex⟩
          have siteEq : registryWrite = expiryWrite :=
            runtimePersistentSourceSite_eq_of_pc registryMem expiryMem
              (registryPc.trans expiryPc.symm)
          rw [siteEq, expiryIndex] at registryIndex
          exact absurd registryIndex (by decide)

/-- Pause registry authority and pause expiry authority can never both hold at
one runtime write.  Each role pins the write's own persistent source site to a
disjoint set of source function indices, so a registry witness cannot be
repacked as an expiry witness — which is exactly what makes a pause role-swap
mutant fail rather than typecheck. -/
theorem RuntimeWriteAuthority.pauseRegistry_not_pauseExpiry
    {dp : DeployParams} {frameRoot write : Exec.Deriv} :
    RuntimeWriteAuthority dp frameRoot write .pauseRegistry →
      ¬ RuntimeWriteAuthority dp frameRoot write .pauseExpiry := by
  intro registry expiry
  cases registry with
  | pauseRegistry _ _ _ _ _ registrySite =>
      cases expiry with
      | pauseExpiry _ _ _ _ _ expirySite =>
          rcases registrySite with
            ⟨registryWrite, registryMem, registryPc, registryIndex⟩
          rcases expirySite with
            ⟨expiryWrite, expiryMem, expiryPc, expiryIndex⟩
          have siteEq : registryWrite = expiryWrite :=
            runtimePersistentSourceSite_eq_of_pc registryMem expiryMem
              (registryPc.trans expiryPc.symm)
          rw [siteEq, expiryIndex] at registryIndex
          exact absurd registryIndex (by decide)

/-- A row's nominated source site is one of the runtime's persistent write
sites.  This is the site-level fact the role-pinning authority fields carry. -/
private theorem RuntimePersistentWrite.sourceSite?_mem
    {dp : DeployParams} {row : RuntimePersistentWrite}
    {site : Prog.SourceSite}
    (found : row.sourceSite? dp = some site) :
    site ∈ runtimePersistentSourceSites dp := by
  have siteSound := row.sourceSite?_sound found
  exact List.mem_filter.mpr ⟨siteSound.1, by rw [siteSound.2]; rfl⟩

private theorem RuntimePersistentWrite.sourceFunctionIndex_of_terminal
    {dp : DeployParams} {root target : Exec.Deriv}
    {row : RuntimePersistentWrite} {site : Prog.SourceSite}
    {finalPath : Prog.SourcePath} {finalTail : Func}
    (finalCursor : Exec.Deriv.SourceCursor root (runtime dp)
      finalPath (.next (.reg .sstore) finalTail))
    (found : row.sourceSite? dp = some site)
    (sitePc : site.pc = target.pc)
    (targetEq : finalCursor.node = target)
    (sourceMember :
      ({ path := finalPath, pc := finalCursor.pc,
          instruction := (.reg .sstore) } : Prog.SourceSite) ∈
        (runtime dp).sourceSites) :
    row.sourceFunctionIndex = finalPath.functionIndex := by
  let terminalSite : Prog.SourceSite :=
    { path := finalPath, pc := finalCursor.pc,
      instruction := (.reg .sstore) }
  have siteMember : site ∈ runtimePersistentSourceSites dp :=
    RuntimePersistentWrite.sourceSite?_mem found
  have terminalMember : terminalSite ∈ runtimePersistentSourceSites dp :=
    List.mem_filter.mpr ⟨sourceMember, rfl⟩
  have terminalPc : finalCursor.pc = target.pc := by
    have nodePc := congrArg Exec.Deriv.pc targetEq
    simpa [Exec.Deriv.SourceCursor.node] using nodePc
  have siteEq : site = terminalSite :=
    runtimePersistentSourceSite_eq_of_pc siteMember terminalMember
      (sitePc.trans terminalPc.symm)
  have functionIndex := row.sourceSite?_functionIndex found
  rw [siteEq] at functionIndex
  exact functionIndex.symm

private theorem RuntimePersistentWrite.adminRegistry_mem_of_functionIndex
    {row : RuntimePersistentWrite}
    (functionIndex : row.sourceFunctionIndex ∈ [14, 15, 16, 17]) :
    InvocationRole.adminRegistry ∈ row.permittedRoles := by
  cases row <;> simp_all [RuntimePersistentWrite.sourceFunctionIndex,
    RuntimePersistentWrite.permittedRoles]

private theorem RuntimePersistentWrite.adminExpiry_mem_of_functionIndex
    {row : RuntimePersistentWrite}
    (functionIndex : row.sourceFunctionIndex = registerAfterSetSlot) :
    InvocationRole.adminExpiry ∈ row.permittedRoles := by
  cases row <;> simp_all [RuntimePersistentWrite.sourceFunctionIndex,
    RuntimePersistentWrite.permittedRoles, registerAfterSetSlot]

private theorem RuntimePersistentWrite.pauseRegistry_mem_of_functionIndex
    {row : RuntimePersistentWrite}
    (functionIndex : row.sourceFunctionIndex ∈ [14, 15, 17]) :
    InvocationRole.pauseRegistry ∈ row.permittedRoles := by
  cases row <;> simp_all [RuntimePersistentWrite.sourceFunctionIndex,
    RuntimePersistentWrite.permittedRoles]

private theorem RuntimePersistentWrite.pauseExpiry_mem_of_functionIndex
    {row : RuntimePersistentWrite}
    (functionIndex : row.sourceFunctionIndex = pauseAfterSetSlot) :
    InvocationRole.pauseExpiry ∈ row.permittedRoles := by
  cases row <;> simp_all [RuntimePersistentWrite.sourceFunctionIndex,
    RuntimePersistentWrite.permittedRoles, pauseAfterSetSlot]

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
      frameToGuard := frameToInitial.trans chronology.initialToCursor
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
    frameToCursor := frameToInitial.trans chronology.initialToCursor
    cursorToWrite := chronology.cursorToTarget }

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
  rcases cursor.branchFlagToward reached (by trivial) storeAt with
    ⟨arm, branchToArm, armReached, zeroPop⟩ |
      ⟨flag, nonzero, arm, branchToArm, armReached, flagPop⟩
  · exact Or.inl ⟨arm, branchToArm, armReached,
      pref_of_split zeroPop.stack, PopBurn.Inv.inv zeroPop⟩
  · exact Or.inr ⟨flag, nonzero, pref_of_split flagPop.stack,
      arm, branchToArm, armReached, PopBurn.Inv.inv flagPop⟩

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
        (chronology.initialToCursor.trans branchToArm) localRoute,
      storage, zeroPrefix⟩
  · have localRoute := arm.toward compiled armReached (by trivial) targetAt
    exact Or.inr ⟨flag, nonzero, flagPrefix, arm,
      Exec.Deriv.SourceCursor.Toward.rebase
        (chronology.initialToCursor.trans branchToArm) localRoute,
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
                    Func.revertData, Func.localSstoreFree, Func.callsIn]
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

private abbrev scratchOffset (word : B256) : Nat :=
  (word * 32).toNat

private abbrev continuationOffset : Nat :=
  scratchOffset continuationWord

/-- The register entry overwrites the continuation word completely.  Retaining
both byte coverage bounds makes subsequent disjoint scratch writes safe even
when nothing is assumed about the memory that preceded that overwrite. -/
private def ScratchWord (word value : B256) (memory : Mem) : Prop :=
  (memory.read (scratchOffset word) 32).1 = value.toBytes ∧
    scratchOffset word + 32 ≤ memory.data.size ∧
    scratchOffset word + 32 ≤ memory.size

private abbrev RegisterContinuationZero (memory : Mem) : Prop :=
  ScratchWord continuationWord 0 memory

private theorem ScratchWord.of_write
    (word value : B256) (memory : Mem) :
    ScratchWord word value
      (memory.write (scratchOffset word) value.toBytes) := by
  have hne : value.toBytes ≠ [] := by
    intro empty
    have lengthEq := B256.length_toBytes value
    rw [empty] at lengthEq
    simp at lengthEq
  rcases bytesEq : value.toBytes with _ | ⟨byte, bytes⟩
  · exact (hne bytesEq).elim
  · have lengthEq : (byte :: bytes).length = 32 := by
      rw [← bytesEq]
      exact B256.length_toBytes value
    have hread :
        ((memory.write (scratchOffset word) (byte :: bytes)).read
          (scratchOffset word) 32).1 = value.toBytes := by
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
              (scratchOffset word) (scratchOffset word + index) (by omega),
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
                  (scratchOffset word + (byte :: bytes).length) 0x00))
              (scratchOffset word) (scratchOffset word + index)
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
                  (scratchOffset word + (byte :: bytes).length)) 0x00))
            (scratchOffset word) (scratchOffset word + index)
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

private theorem RegisterContinuationZero.of_write (memory : Mem) :
    RegisterContinuationZero
      (memory.write continuationOffset (0 : B256).toBytes) := by
  simpa [RegisterContinuationZero, ScratchWord] using
    ScratchWord.of_write continuationWord 0 memory

private theorem RegisterContinuationZero.of_run_seed
    {sevm : Sevm} {pre post : Devm}
    (zeroPrefix : [(0 : B256)] <<+ pre.stack)
    (run : Line.Run sevm pre (mstoreAt continuationWord) post) :
    RegisterContinuationZero post.memory := by
  rcases of_run_mstoreAt_val run zeroPrefix with ⟨stack, memoryEq⟩
  rw [memoryEq]
  exact RegisterContinuationZero.of_write _

private theorem ScratchWord.foldPreservesBefore
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

private theorem ScratchWord.foldReadsMember
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
        rw [ScratchWord.foldPreservesBefore default
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

private theorem ScratchWord.getD_copyD_of_lt
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
  rw [ScratchWord.foldReadsMember default source.toList
    target 0 index targetBound (by omega) (by simpa using sourceBound)]
  simp [Array.getD, sourceBound]

private theorem ScratchWord.writeBefore
    {carrierWord expected : B256} {memory : Mem}
    (carrier : ScratchWord carrierWord expected memory)
    (offset : Nat) (before : offset + 32 ≤ scratchOffset carrierWord)
    (value : B256) :
    ScratchWord carrierWord expected (memory.write offset value.toBytes) := by
  rcases carrier with ⟨readExpected, dataCovered, sizeCovered⟩
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
        (scratchOffset carrierWord) 32 0 = expected.toBytes
      rw [Array.sliceD_eq_map]
      rw [show (memory.read (scratchOffset carrierWord) 32).1 =
          (List.range 32).map
            (fun index =>
              memory.data.getD (scratchOffset carrierWord + index) 0) by
        simp [Mem.read, Array.sliceD_eq_map]] at readExpected
      rw [← readExpected]
      apply List.map_congr_left
      intro index member
      rw [Array.getD_writeD 0 (byte :: bytes) memory.data offset
        (scratchOffset carrierWord + index) writeData, if_neg]
      have indexLt := List.mem_range.mp member
      omega
    · change scratchOffset carrierWord + 32 ≤
        (Array.writeD memory.data offset (byte :: bytes)).size
      simpa [Array.size_writeD] using dataCovered

private theorem ScratchWord.writeAfter
    {carrierWord expected : B256} {memory : Mem}
    (carrier : ScratchWord carrierWord expected memory)
    (offset : Nat) (after : scratchOffset carrierWord + 32 ≤ offset)
    (value : B256) :
    ScratchWord carrierWord expected (memory.write offset value.toBytes) := by
  rcases carrier with ⟨readExpected, dataCovered, sizeCovered⟩
  have readExpectedMap :
      (List.range 32).map
        (fun index =>
          memory.data.getD (scratchOffset carrierWord + index) 0) =
          expected.toBytes := by
    simpa [Mem.read, Array.sliceD_eq_map] using readExpected
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
            (scratchOffset carrierWord) 32 0 = expected.toBytes
          rw [Array.sliceD_eq_map, ← readExpectedMap]
          apply List.map_congr_left
          intro index member
          rw [Array.getD_writeD 0 (byte :: bytes) memory.data offset
            (scratchOffset carrierWord + index) dataEnough, if_neg]
          have indexLt := List.mem_range.mp member
          omega
        · change scratchOffset carrierWord + 32 ≤
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
            (scratchOffset carrierWord) 32 0 = expected.toBytes
          rw [Array.sliceD_eq_map, ← readExpectedMap]
          apply List.map_congr_left
          intro index member
          have indexLt := List.mem_range.mp member
          rw [Array.getD_writeD 0 (byte :: bytes) copied offset
            (scratchOffset carrierWord + index) copiedSize,
            if_neg (by omega)]
          rw [ScratchWord.getD_copyD_of_lt
            memory.data
            (Array.replicate (offset + (byte :: bytes).length) 0)
            0 (scratchOffset carrierWord + index) (by omega) (by
              rw [Array.size_replicate]
              omega)]
        · change scratchOffset carrierWord + 32 ≤
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
          (scratchOffset carrierWord) 32 0 = expected.toBytes
        rw [Array.sliceD_eq_map, ← readExpectedMap]
        apply List.map_congr_left
        intro index member
        have indexLt := List.mem_range.mp member
        rw [Array.getD_writeD 0 (byte :: bytes) copied offset
          (scratchOffset carrierWord + index) copiedSize,
          if_neg (by omega)]
        rw [ScratchWord.getD_copyD_of_lt
          memory.data
          (Array.replicate
            (ceil32 (offset + (byte :: bytes).length)) 0)
          0 (scratchOffset carrierWord + index) (by omega) (by
            rw [Array.size_replicate]
            apply Nat.lt_of_lt_of_le
              (show scratchOffset carrierWord + index < offset by omega)
            exact Nat.le_trans (Nat.le_add_right _ _)
              (Nat.le_ceil32 _))]
      · change scratchOffset carrierWord + 32 ≤
          (Array.writeD copied offset (byte :: bytes)).size
        rw [Array.size_writeD]
        exact Nat.le_trans (by omega) copiedSize
      · exact Nat.le_trans (by omega) (Nat.le_ceil32 _)

private theorem ScratchWord.extend
    {word expected : B256} {memory : Mem}
    (carrier : ScratchWord word expected memory)
    (offset size : Nat) :
    ScratchWord word expected (memory.extend offset size) := by
  rcases carrier with ⟨readExpected, dataCovered, sizeCovered⟩
  refine ⟨readExpected, dataCovered, ?_⟩
  simp only [Mem.extend, memExtSize]
  split
  · exact sizeCovered
  · exact Nat.le_trans sizeCovered <|
      Nat.le_trans (Nat.le_mul_ceilDiv memory.size 32 (by omega)) <|
        Nat.mul_le_mul_left 32 (Nat.le_max_left _ _)

private theorem ScratchWord.prefix_of_loadWord
    {sevm : Sevm} {pre post : Devm} {word expected : B256} {xs : Stack}
    (carrier : ScratchWord word expected pre.memory)
    (stackPrefix : xs <<+ pre.stack)
    (run : Line.Run sevm pre (loadWord word) post) :
    expected :: xs <<+ post.stack ∧
      ScratchWord word expected post.memory := by
  unfold loadWord at run
  rcases Line.of_run_cons run with ⟨pushed, pushRun, rest⟩
  rcases Line.of_run_cons rest with ⟨loaded, loadRun, nilRun⟩
  cases nilRun
  have pushInv := of_run_pushB256 pushRun
  have pushedPrefix : (word * 32) :: xs <<+ pushed.stack :=
    prefix_of_push pushInv stackPrefix
  have pushedCarrier : ScratchWord word expected pushed.memory := by
    rw [← pushInv.memory]
    exact carrier
  have reads : Mem.Reads pushed.memory pushed.memory.data.toList := by
    intro index
    by_cases bound : index < pushed.memory.data.size <;>
      simp [Array.getD, bound, List.getD_eq_getElem?_getD]
  rcases prefix_of_mload_val loadRun pushedPrefix reads with
    ⟨loadedPrefix, loadedMemory, loadedReturnData⟩
  have valueEq : Bytes.toB256
      (pushed.memory.data.toList.sliceD (scratchOffset word) 32 0) =
        expected := by
    rw [← Mem.Reads.read reads (scratchOffset word) 32,
      pushedCarrier.1]
    rw [B256.toB256_toBytes]
  have offsetEq : (word * 32).toNat = scratchOffset word := rfl
  rw [offsetEq, valueEq] at loadedPrefix
  refine ⟨loadedPrefix, ?_⟩
  rw [loadedMemory, offsetEq]
  exact ScratchWord.extend pushedCarrier _ _

private theorem ScratchWord.of_run_loadWord
    {sevm : Sevm} {pre post : Devm} {carrierWord expected word : B256}
    (carrier : ScratchWord carrierWord expected pre.memory)
    (run : Line.Run sevm pre (loadWord word) post) :
    ScratchWord carrierWord expected post.memory := by
  unfold loadWord at run
  rcases Line.of_run_cons run with ⟨pushed, pushRun, rest⟩
  rcases Line.of_run_cons rest with ⟨loaded, loadRun, nilRun⟩
  cases nilRun
  rcases of_run_mload_val loadRun with ⟨offset, stack, memory, returnData⟩
  rw [memory, ← (of_run_pushB256 pushRun).memory]
  exact carrier.extend _ _

private theorem ScratchWord.of_run_mstoreAtBefore
    {sevm : Sevm} {pre post : Devm} {carrierWord expected word : B256}
    (carrier : ScratchWord carrierWord expected pre.memory)
    (before : (word * 32).toNat + 32 ≤ scratchOffset carrierWord)
    (run : Line.Run sevm pre (mstoreAt word) post) :
    ScratchWord carrierWord expected post.memory := by
  unfold mstoreAt at run
  rcases Line.of_run_cons run with ⟨pushed, pushRun, rest⟩
  rcases Line.of_run_cons rest with ⟨stored, storeRun, nilRun⟩
  cases nilRun
  have push := of_run_pushB256 pushRun
  rcases of_run_mstore_val storeRun with ⟨offset, value, pop, memory⟩
  have offsetEq : (word * 32) = offset :=
    (Stack.push_cons_pop_cons push.stack pop).1
  rw [memory, ← push.memory, ← offsetEq]
  exact carrier.writeBefore _ before _

private theorem ScratchWord.of_run_mstoreAtAfter
    {sevm : Sevm} {pre post : Devm} {carrierWord expected word : B256}
    (carrier : ScratchWord carrierWord expected pre.memory)
    (after : scratchOffset carrierWord + 32 ≤ (word * 32).toNat)
    (run : Line.Run sevm pre (mstoreAt word) post) :
    ScratchWord carrierWord expected post.memory := by
  unfold mstoreAt at run
  rcases Line.of_run_cons run with ⟨pushed, pushRun, rest⟩
  rcases Line.of_run_cons rest with ⟨stored, storeRun, nilRun⟩
  cases nilRun
  have push := of_run_pushB256 pushRun
  rcases of_run_mstore_val storeRun with ⟨offset, value, pop, memory⟩
  have offsetEq : (word * 32) = offset :=
    (Stack.push_cons_pop_cons push.stack pop).1
  rw [memory, ← push.memory, ← offsetEq]
  exact carrier.writeAfter _ after _

private theorem ScratchWord.of_run_logWith
    {sevm : Sevm} {pre post : Devm} {carrierWord expected : B256}
    {topics : Fin 4} {offset size : B256}
    (carrier : ScratchWord carrierWord expected pre.memory)
    (run : Line.Run sevm pre (logWith topics offset size) post) :
    ScratchWord carrierWord expected post.memory := by
  unfold logWith at run
  rcases Line.of_run_cons run with ⟨sizePushed, sizeRun, rest⟩
  rcases Line.of_run_cons rest with ⟨offsetPushed, offsetRun, rest⟩
  rcases Line.of_run_cons rest with ⟨logged, logRun, nilRun⟩
  cases nilRun
  rcases of_run_log_mem logRun with ⟨memoryOffset, memorySize, memory⟩
  rw [memory, ← (of_run_pushB256 offsetRun).memory,
    ← (of_run_pushB256 sizeRun).memory]
  exact carrier.extend _ _

private def PauseKernelMemory (memory : Mem) : Prop :=
  ScratchWord newPauserWord 0 memory ∧
    ScratchWord continuationWord 1 memory

private theorem PauseKernelMemory.of_run_loadWord
    {sevm : Sevm} {pre post : Devm} {word : B256}
    (carrier : PauseKernelMemory pre.memory)
    (run : Line.Run sevm pre (loadWord word) post) :
    PauseKernelMemory post.memory :=
  ⟨carrier.1.of_run_loadWord run, carrier.2.of_run_loadWord run⟩

private theorem PauseKernelMemory.of_run_mstoreAtAfter
    {sevm : Sevm} {pre post : Devm} {word : B256}
    (carrier : PauseKernelMemory pre.memory)
    (afterContinuation :
      scratchOffset continuationWord + 32 ≤ (word * 32).toNat)
    (run : Line.Run sevm pre (mstoreAt word) post) :
    PauseKernelMemory post.memory :=
  ⟨carrier.1.of_run_mstoreAtAfter (by
      exact Nat.le_trans (by decide +kernel) afterContinuation) run,
    carrier.2.of_run_mstoreAtAfter afterContinuation run⟩

private theorem PauseKernelMemory.of_run_logWith
    {sevm : Sevm} {pre post : Devm} {topics : Fin 4} {offset size : B256}
    (carrier : PauseKernelMemory pre.memory)
    (run : Line.Run sevm pre (logWith topics offset size) post) :
    PauseKernelMemory post.memory :=
  ⟨carrier.1.of_run_logWith run, carrier.2.of_run_logWith run⟩

private theorem Exec.Deriv.SourceCursor.Toward.dropLineRunExact
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {line : Line} {tail : Func}
    {cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (line +++ tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (lineNe : ∀ instruction ∈ line, instruction ≠ (.reg .sstore)) :
    ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex,
          path.steps ++ List.replicate line.length .rest⟩ tail,
      Line.Run root.sevm cursor.pre line tailCursor.pre ∧
        Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) tailCursor := by
  induction line generalizing path with
  | nil =>
      have pathEq : path =
          ⟨path.functionIndex,
            path.steps ++ List.replicate ([] : Line).length .rest⟩ := by
        cases path
        simp
      rw [← pathEq]
      exact ⟨cursor, .nil, route⟩
  | cons instruction rest ih =>
      change Exec.Deriv.SourceCursor root (runtime dp) path
        (.next instruction (rest +++ tail)) at cursor
      rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
          (lineNe instruction (by simp)) with
        ⟨chronology, restCursor, edge, restRoute⟩
      rcases ih restRoute (fun candidate member =>
          lineNe candidate (by simp [member])) with
        ⟨tailCursor, lineRun, tailRoute⟩
      have stepsEq :
          (path.steps ++ [.rest]) ++
              List.replicate rest.length .rest =
            path.steps ++
              List.replicate (instruction :: rest).length .rest := by
        simp [List.replicate_succ, List.append_assoc]
      rw [← stepsEq]
      exact ⟨tailCursor,
        Line.Run.cons
          (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge cursor edge)
          lineRun,
        tailRoute⟩

private theorem Exec.Deriv.SourceCursor.Toward.dropLineContinuation
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {line : Line} {tail : Func}
    {cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (line +++ tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (lineNe : ∀ instruction ∈ line, instruction ≠ (.reg .sstore))
    (zero : RegisterContinuationZero cursor.pre.memory)
    (preserves : ∀ {pre post}, Line.Run root.sevm pre line post →
      RegisterContinuationZero pre.memory →
        RegisterContinuationZero post.memory) :
    ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex,
          path.steps ++ List.replicate line.length .rest⟩ tail,
      Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) tailCursor ∧
        RegisterContinuationZero tailCursor.pre.memory := by
  rcases Exec.Deriv.SourceCursor.Toward.dropLineRunExact route lineNe with
    ⟨tailCursor, run, tailRoute⟩
  exact ⟨tailCursor, tailRoute, preserves run zero⟩

private theorem Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {word : B256} {tail : Func}
    {cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (loadWord word +++ tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (zero : RegisterContinuationZero cursor.pre.memory) :
    ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex,
          path.steps ++ List.replicate (loadWord word).length .rest⟩ tail,
      Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) tailCursor ∧
        RegisterContinuationZero tailCursor.pre.memory := by
  apply Exec.Deriv.SourceCursor.Toward.dropLineContinuation route _ zero
    (fun run zero => zero.of_run_loadWord run)
  intro instruction member
  simp only [loadWord, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> intro h <;> cases h

private theorem Exec.Deriv.SourceCursor.Toward.dropMstoreAtBeforeContinuation
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {word : B256} {tail : Func}
    {cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (mstoreAt word +++ tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (zero : RegisterContinuationZero cursor.pre.memory)
    (before : (word * 32).toNat + 32 ≤ continuationOffset) :
    ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex,
          path.steps ++ List.replicate (mstoreAt word).length .rest⟩ tail,
      Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) tailCursor ∧
        RegisterContinuationZero tailCursor.pre.memory := by
  apply Exec.Deriv.SourceCursor.Toward.dropLineContinuation route _ zero
    (fun run zero => zero.of_run_mstoreAtBefore before run)
  intro instruction member
  simp only [mstoreAt, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> intro h <;> cases h

private theorem Exec.Deriv.SourceCursor.Toward.dropMstoreAtAfterContinuation
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {word : B256} {tail : Func}
    {cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (mstoreAt word +++ tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (zero : RegisterContinuationZero cursor.pre.memory)
    (after : continuationOffset + 32 ≤ (word * 32).toNat) :
    ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex,
          path.steps ++ List.replicate (mstoreAt word).length .rest⟩ tail,
      Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) tailCursor ∧
        RegisterContinuationZero tailCursor.pre.memory := by
  apply Exec.Deriv.SourceCursor.Toward.dropLineContinuation route _ zero
    (fun run zero => zero.of_run_mstoreAtAfter after run)
  intro instruction member
  simp only [mstoreAt, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> intro h <;> cases h

private theorem Exec.Deriv.SourceCursor.Toward.dropSilentContinuation
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {line : Line} {tail : Func}
    {cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (line +++ tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (lineNe : ∀ instruction ∈ line, instruction ≠ (.reg .sstore))
    (memoryInv : ∀ {sevm pre post},
      Line.Run sevm pre line post → pre.memory = post.memory)
    (zero : RegisterContinuationZero cursor.pre.memory) :
    ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex,
          path.steps ++ List.replicate line.length .rest⟩ tail,
      Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) tailCursor ∧
        RegisterContinuationZero tailCursor.pre.memory := by
  apply Exec.Deriv.SourceCursor.Toward.dropLineContinuation route lineNe zero
  intro pre post run zero
  have memoryEq : pre.memory = post.memory := memoryInv run
  exact memoryEq ▸ zero

/-- The compiled form of an internal source call is exactly a PUSH of the
callee entry, a JUMP, and that entry's JUMPDEST.  Those three instructions are
memory-silent, so the register continuation carrier crosses the call without
requiring a general invariant for arbitrary non-SSTORE prefixes. -/
private theorem Exec.Deriv.SourceCursor.Toward.callBodyContinuation
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {functionIndex : Nat}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (.call functionIndex))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (zero : RegisterContinuationZero cursor.pre.memory) :
    ∃ body, ((runtime dp).main :: (runtime dp).aux)[functionIndex]? = some body ∧
      ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
          ⟨functionIndex, []⟩ body,
        Exec.Deriv.SourceCursor.Toward
            initial target (.reg .sstore) bodyCursor ∧
          RegisterContinuationZero bodyCursor.pre.memory := by
  rcases subcode_compile_call cursor.codeSlice with
    ⟨loc, body, getTable, locBound, pushAt, jumpAt⟩
  have reached :=
    (Exec.Deriv.SourceCursor.Toward.chronology route).cursorToTarget
  rcases Exec.Deriv.ParentPrefix.advance_pushToward reached
      pushAt (by simp) (by trivial) targetAt with
    ⟨afterPushPre, afterPush, pushEdge, afterPushReached, pushBurn⟩
  rw [List.toB256_pair _ locBound] at pushBurn
  rcases Exec.Deriv.ParentPrefix.advance_jumpToward
      afterPushReached jumpAt targetAt with
    ⟨nextPc, beforeJumpdestPre, beforeJumpdest, jumpEdge,
      beforeJumpdestReached, jumpRun⟩
  rcases of_jump_run jumpRun with
    ⟨destination, nextPcEq, popBurn, actualJumpable⟩
  have loc256 : loc < 2 ^ 256 := by
    apply Nat.lt_trans locBound
    rw [Nat.pow_lt_pow_iff_right] <;> omega
  have destinationEq : loc = destination.toNat := by
    rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
      ⟨headEq, stack, pushBurn', popBurn'⟩
    have locToNat : loc.toB256.toNat = loc :=
      B256.toNat_toB256_of_lt loc256
    rw [← congrArg B256.toNat headEq, locToNat]
  have nextPcLoc : nextPc = loc := nextPcEq.trans destinationEq.symm
  cases nextPcLoc
  have getBody :
      ((runtime dp).main :: (runtime dp).aux)[functionIndex]? = some body := by
    have tableLookup :=
      @Prog.get?_table 0 functionIndex ((runtime dp).main :: (runtime dp).aux)
    rw [getTable] at tableLookup
    simpa using tableLookup.symm
  rcases subcode_of_get?_eq_some compiled getTable with
    ⟨jumpdestAt, bodySlice⟩
  have bodyBoundary := Prog.jumpable_of_get?_table compiled getTable
  rcases Exec.Deriv.ParentPrefix.advance_jumpToward
      beforeJumpdestReached jumpdestAt targetAt with
    ⟨bodyPc, bodyPre, bodyExec, jumpdestEdge, bodyReached,
      jumpdestRun⟩
  rcases of_jumpdest_run jumpdestRun with ⟨bodyPcEq, jumpdestBurn⟩
  subst bodyPc
  let bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
      ⟨functionIndex, []⟩ body :=
    ⟨_, _, bodyExec,
      cursor.parentPrefix.snoc pushEdge |>.snoc jumpEdge
        |>.snoc jumpdestEdge,
      bodySlice, bodyBoundary.2, by
        intro site member
        simp only [Prog.sourceSites, List.mem_flatMap]
        refine ⟨functionIndex, ?_, ?_⟩
        · exact List.mem_range.mpr
            (List.getElem?_eq_some_iff.mp getBody).choose
        · simpa only [getTable] using member⟩
  have bodyZero : RegisterContinuationZero bodyCursor.pre.memory := by
    change RegisterContinuationZero bodyPre.memory
    rw [← jumpdestBurn.memory, ← popBurn.memory, ← pushBurn.memory]
    exact zero
  have bodyRoute := bodyCursor.toward compiled bodyReached
    (by trivial) targetAt
  have cursorToBody : Exec.Deriv.ParentPrefix cursor.node bodyCursor.node :=
    .step pushEdge (.step jumpEdge (.step jumpdestEdge (.refl _)))
  have initialToBody : Exec.Deriv.ParentPrefix initial.node bodyCursor.node :=
    (Exec.Deriv.SourceCursor.Toward.chronology route).initialToCursor.trans
      cursorToBody
  exact ⟨body, getBody, bodyCursor,
    Exec.Deriv.SourceCursor.Toward.rebase initialToBody bodyRoute,
    bodyZero⟩

private theorem finishSetPauserCallContinuation
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (.call finishSetPauserSlot))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (zero : RegisterContinuationZero cursor.pre.memory) :
    ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨finishSetPauserSlot, []⟩ finishSetPauser,
      Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) bodyCursor ∧
        RegisterContinuationZero bodyCursor.pre.memory := by
  rcases Exec.Deriv.SourceCursor.Toward.callBodyContinuation
      cursor compiled targetAt route zero with
    ⟨body, lookup, bodyCursor, bodyRoute, bodyZero⟩
  simp [runtime, aux, finishSetPauserSlot] at lookup
  cases lookup
  exact ⟨bodyCursor, bodyRoute, bodyZero⟩

private theorem Exec.Deriv.SourceCursor.Toward.branchArmContinuation
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {left right : Func}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (.branch left right))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (zero : RegisterContinuationZero cursor.pre.memory) :
    (∃ arm : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left,
      Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) arm ∧
        RegisterContinuationZero arm.pre.memory) ∨
    (∃ arm : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex, path.steps ++ [.branchRight]⟩ right,
      Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) arm ∧
        RegisterContinuationZero arm.pre.memory) := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, locEq, locBound, pushAt, jumpiAt, leftSlice, leftBoundary,
      jumpdestAt, jumpable, rightSlice, rightBoundary⟩
  have chronology := Exec.Deriv.SourceCursor.Toward.chronology route
  rcases Exec.Deriv.ParentPrefix.advance_pushToward
      chronology.cursorToTarget ⟨_, pushAt⟩ (by simp) (by trivial)
        targetAt with
    ⟨afterPushPre, afterPush, pushEdge, afterPushReached, pushBurn⟩
  rw [List.toB256_pair _ locBound] at pushBurn
  rcases Exec.Deriv.ParentPrefix.advance_jumpToward
      afterPushReached jumpiAt targetAt with
    ⟨nextPc, armPre, armExec, jumpEdge, armReached, jumpRun⟩
  rcases of_jumpi_run jumpRun with
    ⟨destination, nextPcEq, popBurn⟩ |
      ⟨destination, flag, nextPcEq, popBurn, actualJumpable, nonzero⟩
  · cases nextPcEq
    let armCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left :=
      ⟨_, _, armExec, cursor.parentPrefix.snoc pushEdge |>.snoc jumpEdge,
        leftSlice, leftBoundary, by
          intro site member
          apply cursor.sourceIncluded
          simp only [Func.sourceSites, List.mem_append]
          exact Or.inl member⟩
    have armZero : RegisterContinuationZero armCursor.pre.memory := by
      change RegisterContinuationZero armPre.memory
      rw [← popBurn.memory, ← pushBurn.memory]
      exact zero
    have localRoute := armCursor.toward compiled armReached
      (by trivial) targetAt
    have cursorToArm : Exec.Deriv.ParentPrefix cursor.node armCursor.node :=
      .step pushEdge (.step jumpEdge (.refl _))
    have initialToArm : Exec.Deriv.ParentPrefix initial.node armCursor.node :=
      chronology.initialToCursor.trans cursorToArm
    exact Or.inl ⟨armCursor,
      Exec.Deriv.SourceCursor.Toward.rebase initialToArm localRoute,
      armZero⟩
  · have loc256 : loc < 2 ^ 256 := by
      apply Nat.lt_trans locBound
      rw [Nat.pow_lt_pow_iff_right] <;> omega
    have destinationEq : loc = destination.toNat := by
      rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
        ⟨headEq, stack, pushBurn', popBurn'⟩
      have locToNat : loc.toB256.toNat = loc :=
        B256.toNat_toB256_of_lt loc256
      rw [← congrArg B256.toNat headEq, locToNat]
    have nextPcLoc : nextPc = loc := nextPcEq.trans destinationEq.symm
    cases nextPcLoc
    rcases Exec.Deriv.ParentPrefix.advance_jumpToward
        armReached jumpdestAt targetAt with
      ⟨bodyPc, bodyPre, bodyExec, jumpdestEdge, bodyReached,
        jumpdestRun⟩
    rcases of_jumpdest_run jumpdestRun with ⟨bodyPcEq, jumpdestBurn⟩
    subst bodyPc
    let armCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex, path.steps ++ [.branchRight]⟩ right :=
      ⟨_, _, bodyExec,
        cursor.parentPrefix.snoc pushEdge |>.snoc jumpEdge
          |>.snoc jumpdestEdge,
        rightSlice, rightBoundary, by
          intro site member
          apply cursor.sourceIncluded
          simp only [Func.sourceSites, List.mem_append]
          apply Or.inr
          have rightPc : loc + 1 = cursor.pc + compsize left + 5 := by
            omega
          rw [← rightPc]
          exact member⟩
    have armZero : RegisterContinuationZero armCursor.pre.memory := by
      change RegisterContinuationZero bodyPre.memory
      rw [← jumpdestBurn.memory, ← popBurn.memory, ← pushBurn.memory]
      exact zero
    have localRoute := armCursor.toward compiled bodyReached
      (by trivial) targetAt
    have cursorToArm : Exec.Deriv.ParentPrefix cursor.node armCursor.node :=
      .step pushEdge (.step jumpEdge (.step jumpdestEdge (.refl _)))
    have initialToArm : Exec.Deriv.ParentPrefix initial.node armCursor.node :=
      chronology.initialToCursor.trans cursorToArm
    exact Or.inr ⟨armCursor,
      Exec.Deriv.SourceCursor.Toward.rebase initialToArm localRoute,
      armZero⟩

private theorem Exec.Deriv.SourceCursor.Toward.dropLinePauseMemory
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {line : Line} {tail : Func}
    {cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (line +++ tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (lineNe : ∀ instruction ∈ line, instruction ≠ (.reg .sstore))
    (carrier : PauseKernelMemory cursor.pre.memory)
    (preserves : ∀ {pre post}, Line.Run root.sevm pre line post →
      PauseKernelMemory pre.memory → PauseKernelMemory post.memory) :
    ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex,
          path.steps ++ List.replicate line.length .rest⟩ tail,
      Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) tailCursor ∧
        PauseKernelMemory tailCursor.pre.memory := by
  rcases Exec.Deriv.SourceCursor.Toward.dropLineRunExact route lineNe with
    ⟨tailCursor, run, tailRoute⟩
  exact ⟨tailCursor, tailRoute, preserves run carrier⟩

private theorem Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {word : B256} {tail : Func}
    {cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (loadWord word +++ tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (carrier : PauseKernelMemory cursor.pre.memory) :
    ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex,
          path.steps ++ List.replicate (loadWord word).length .rest⟩ tail,
      Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) tailCursor ∧
        PauseKernelMemory tailCursor.pre.memory := by
  apply Exec.Deriv.SourceCursor.Toward.dropLinePauseMemory route _ carrier
    (fun run memory => memory.of_run_loadWord run)
  intro instruction member
  simp only [loadWord, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> intro h <;> cases h

private theorem Exec.Deriv.SourceCursor.Toward.dropMstoreAtAfterPauseMemory
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {word : B256} {tail : Func}
    {cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (mstoreAt word +++ tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (carrier : PauseKernelMemory cursor.pre.memory)
    (afterContinuation :
      scratchOffset continuationWord + 32 ≤ (word * 32).toNat) :
    ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex,
          path.steps ++ List.replicate (mstoreAt word).length .rest⟩ tail,
      Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) tailCursor ∧
        PauseKernelMemory tailCursor.pre.memory := by
  apply Exec.Deriv.SourceCursor.Toward.dropLinePauseMemory route _ carrier
    (fun run memory => memory.of_run_mstoreAtAfter afterContinuation run)
  intro instruction member
  simp only [mstoreAt, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> intro h <;> cases h

private theorem Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {line : Line} {tail : Func}
    {cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (line +++ tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (lineNe : ∀ instruction ∈ line, instruction ≠ (.reg .sstore))
    (memoryInv : ∀ {sevm pre post},
      Line.Run sevm pre line post → pre.memory = post.memory)
    (carrier : PauseKernelMemory cursor.pre.memory) :
    ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex,
          path.steps ++ List.replicate line.length .rest⟩ tail,
      Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) tailCursor ∧
        PauseKernelMemory tailCursor.pre.memory := by
  apply Exec.Deriv.SourceCursor.Toward.dropLinePauseMemory route lineNe carrier
  intro pre post run memory
  exact (memoryInv run) ▸ memory

private theorem Exec.Deriv.SourceCursor.Toward.callBodyPauseMemory
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {functionIndex : Nat}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (.call functionIndex))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (carrier : PauseKernelMemory cursor.pre.memory) :
    ∃ body, ((runtime dp).main :: (runtime dp).aux)[functionIndex]? = some body ∧
      ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
          ⟨functionIndex, []⟩ body,
        Exec.Deriv.SourceCursor.Toward
            initial target (.reg .sstore) bodyCursor ∧
          PauseKernelMemory bodyCursor.pre.memory := by
  rcases subcode_compile_call cursor.codeSlice with
    ⟨loc, body, getTable, locBound, pushAt, jumpAt⟩
  have reached :=
    (Exec.Deriv.SourceCursor.Toward.chronology route).cursorToTarget
  rcases Exec.Deriv.ParentPrefix.advance_pushToward reached
      pushAt (by simp) (by trivial) targetAt with
    ⟨afterPushPre, afterPush, pushEdge, afterPushReached, pushBurn⟩
  rw [List.toB256_pair _ locBound] at pushBurn
  rcases Exec.Deriv.ParentPrefix.advance_jumpToward
      afterPushReached jumpAt targetAt with
    ⟨nextPc, beforeJumpdestPre, beforeJumpdest, jumpEdge,
      beforeJumpdestReached, jumpRun⟩
  rcases of_jump_run jumpRun with
    ⟨destination, nextPcEq, popBurn, actualJumpable⟩
  have loc256 : loc < 2 ^ 256 := by
    apply Nat.lt_trans locBound
    rw [Nat.pow_lt_pow_iff_right] <;> omega
  have destinationEq : loc = destination.toNat := by
    rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
      ⟨headEq, stack, pushBurn', popBurn'⟩
    have locToNat : loc.toB256.toNat = loc :=
      B256.toNat_toB256_of_lt loc256
    rw [← congrArg B256.toNat headEq, locToNat]
  have nextPcLoc : nextPc = loc := nextPcEq.trans destinationEq.symm
  cases nextPcLoc
  have getBody :
      ((runtime dp).main :: (runtime dp).aux)[functionIndex]? = some body := by
    have tableLookup :=
      @Prog.get?_table 0 functionIndex ((runtime dp).main :: (runtime dp).aux)
    rw [getTable] at tableLookup
    simpa using tableLookup.symm
  rcases subcode_of_get?_eq_some compiled getTable with
    ⟨jumpdestAt, bodySlice⟩
  have bodyBoundary := Prog.jumpable_of_get?_table compiled getTable
  rcases Exec.Deriv.ParentPrefix.advance_jumpToward
      beforeJumpdestReached jumpdestAt targetAt with
    ⟨bodyPc, bodyPre, bodyExec, jumpdestEdge, bodyReached,
      jumpdestRun⟩
  rcases of_jumpdest_run jumpdestRun with ⟨bodyPcEq, jumpdestBurn⟩
  subst bodyPc
  let bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
      ⟨functionIndex, []⟩ body :=
    ⟨_, _, bodyExec,
      cursor.parentPrefix.snoc pushEdge |>.snoc jumpEdge
        |>.snoc jumpdestEdge,
      bodySlice, bodyBoundary.2, by
        intro site member
        simp only [Prog.sourceSites, List.mem_flatMap]
        refine ⟨functionIndex, ?_, ?_⟩
        · exact List.mem_range.mpr
            (List.getElem?_eq_some_iff.mp getBody).choose
        · simpa only [getTable] using member⟩
  have bodyMemory : PauseKernelMemory bodyCursor.pre.memory := by
    change PauseKernelMemory bodyPre.memory
    rw [← jumpdestBurn.memory, ← popBurn.memory, ← pushBurn.memory]
    exact carrier
  have bodyRoute := bodyCursor.toward compiled bodyReached
    (by trivial) targetAt
  have cursorToBody : Exec.Deriv.ParentPrefix cursor.node bodyCursor.node :=
    .step pushEdge (.step jumpEdge (.step jumpdestEdge (.refl _)))
  have initialToBody : Exec.Deriv.ParentPrefix initial.node bodyCursor.node :=
    (Exec.Deriv.SourceCursor.Toward.chronology route).initialToCursor.trans
      cursorToBody
  exact ⟨body, getBody, bodyCursor,
    Exec.Deriv.SourceCursor.Toward.rebase initialToBody bodyRoute,
    bodyMemory⟩

private theorem Exec.Deriv.SourceCursor.Toward.branchArmPauseMemory
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {left right : Func}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (.branch left right))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (carrier : PauseKernelMemory cursor.pre.memory) :
    (∃ arm : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left,
      Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) arm ∧
        PauseKernelMemory arm.pre.memory ∧
          [(0 : B256)] <<+ cursor.pre.stack) ∨
    (∃ flag : B256, flag ≠ 0 ∧ [flag] <<+ cursor.pre.stack ∧
      ∃ arm : Exec.Deriv.SourceCursor root (runtime dp)
          ⟨path.functionIndex, path.steps ++ [.branchRight]⟩ right,
        Exec.Deriv.SourceCursor.Toward
            initial target (.reg .sstore) arm ∧
          PauseKernelMemory arm.pre.memory) := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, locEq, locBound, pushAt, jumpiAt, leftSlice, leftBoundary,
      jumpdestAt, jumpable, rightSlice, rightBoundary⟩
  have chronology := Exec.Deriv.SourceCursor.Toward.chronology route
  rcases Exec.Deriv.ParentPrefix.advance_pushToward
      chronology.cursorToTarget ⟨_, pushAt⟩ (by simp) (by trivial)
        targetAt with
    ⟨afterPushPre, afterPush, pushEdge, afterPushReached, pushBurn⟩
  rw [List.toB256_pair _ locBound] at pushBurn
  rcases Exec.Deriv.ParentPrefix.advance_jumpToward
      afterPushReached jumpiAt targetAt with
    ⟨nextPc, armPre, armExec, jumpEdge, armReached, jumpRun⟩
  rcases of_jumpi_run jumpRun with
    ⟨destination, nextPcEq, popBurn⟩ |
      ⟨destination, flag, nextPcEq, popBurn, actualJumpable, nonzero⟩
  · cases nextPcEq
    let armCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left :=
      ⟨_, _, armExec, cursor.parentPrefix.snoc pushEdge |>.snoc jumpEdge,
        leftSlice, leftBoundary, by
          intro site member
          apply cursor.sourceIncluded
          simp only [Func.sourceSites, List.mem_append]
          exact Or.inl member⟩
    have armMemory : PauseKernelMemory armCursor.pre.memory := by
      change PauseKernelMemory armPre.memory
      rw [← popBurn.memory, ← pushBurn.memory]
      exact carrier
    have localRoute := armCursor.toward compiled armReached
      (by trivial) targetAt
    have cursorToArm : Exec.Deriv.ParentPrefix cursor.node armCursor.node :=
      .step pushEdge (.step jumpEdge (.refl _))
    have initialToArm : Exec.Deriv.ParentPrefix initial.node armCursor.node :=
      chronology.initialToCursor.trans cursorToArm
    rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
      ⟨headEq, stack, pushBurn', popBurn'⟩
    have zeroPop : Devm.PopBurn [(0 : B256)] cursor.pre armPre :=
      Devm.popBurn_of_burn_of_popBurn
        (Devm.burn_of_pushBurn_nil pushBurn') popBurn'
    exact Or.inl ⟨armCursor,
      Exec.Deriv.SourceCursor.Toward.rebase initialToArm localRoute,
      armMemory, pref_of_split zeroPop.stack⟩
  · have loc256 : loc < 2 ^ 256 := by
      apply Nat.lt_trans locBound
      rw [Nat.pow_lt_pow_iff_right] <;> omega
    have destinationEq : loc = destination.toNat := by
      rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
        ⟨headEq, stack, pushBurn', popBurn'⟩
      have locToNat : loc.toB256.toNat = loc :=
        B256.toNat_toB256_of_lt loc256
      rw [← congrArg B256.toNat headEq, locToNat]
    have nextPcLoc : nextPc = loc := nextPcEq.trans destinationEq.symm
    cases nextPcLoc
    rcases Exec.Deriv.ParentPrefix.advance_jumpToward
        armReached jumpdestAt targetAt with
      ⟨bodyPc, bodyPre, bodyExec, jumpdestEdge, bodyReached,
        jumpdestRun⟩
    rcases of_jumpdest_run jumpdestRun with ⟨bodyPcEq, jumpdestBurn⟩
    subst bodyPc
    let armCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨path.functionIndex, path.steps ++ [.branchRight]⟩ right :=
      ⟨_, _, bodyExec,
        cursor.parentPrefix.snoc pushEdge |>.snoc jumpEdge
          |>.snoc jumpdestEdge,
        rightSlice, rightBoundary, by
          intro site member
          apply cursor.sourceIncluded
          simp only [Func.sourceSites, List.mem_append]
          apply Or.inr
          have rightPc : loc + 1 = cursor.pc + compsize left + 5 := by
            omega
          rw [← rightPc]
          exact member⟩
    have armMemory : PauseKernelMemory armCursor.pre.memory := by
      change PauseKernelMemory bodyPre.memory
      rw [← jumpdestBurn.memory, ← popBurn.memory, ← pushBurn.memory]
      exact carrier
    have localRoute := armCursor.toward compiled bodyReached
      (by trivial) targetAt
    have cursorToArm : Exec.Deriv.ParentPrefix cursor.node armCursor.node :=
      .step pushEdge (.step jumpEdge (.step jumpdestEdge (.refl _)))
    have initialToArm : Exec.Deriv.ParentPrefix initial.node armCursor.node :=
      chronology.initialToCursor.trans cursorToArm
    rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
      ⟨headEq, stack, pushBurn', popBurn'⟩
    have flagPop : Devm.PopBurn [flag] cursor.pre armPre :=
      Devm.popBurn_of_burn_of_popBurn
        (Devm.burn_of_pushBurn_nil pushBurn') popBurn'
    exact Or.inr ⟨flag, nonzero, pref_of_split flagPop.stack, armCursor,
      Exec.Deriv.SourceCursor.Toward.rebase initialToArm localRoute,
      armMemory⟩

private inductive RegisterKernelCut
    {dp : DeployParams} {root target : Exec.Deriv}
    (initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)) : Prop
  | registry {path : Prog.SourcePath} {tail : Func}
      (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
        (.next (.reg .sstore) tail))
      (targetEq : cursor.node = target)
      (sourceMember :
        ({ path := path, pc := cursor.pc,
            instruction := (.reg .sstore) } : Prog.SourceSite) ∈
          (runtime dp).sourceSites)
      (functionIndex : path.functionIndex ∈ [14, 15, 16, 17]) :
      RegisterKernelCut initial
  | registerAfterSet
      (cursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨registerAfterSetSlot, []⟩ registerAfterSet)
      (route : Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) cursor) :
      RegisterKernelCut initial

private theorem registerKernelCut_at_sstore
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)}
    {path : Prog.SourcePath} {tail : Func}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (.next (.reg .sstore) tail))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (zero : RegisterContinuationZero cursor.pre.memory)
    (functionIndex : path.functionIndex ∈ [14, 15, 16, 17]) :
    RegisterKernelCut (target := target) initial ∨
      ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
          ⟨path.functionIndex, path.steps ++ [.rest]⟩ tail,
        Exec.Deriv.SourceCursor.Toward
            initial target (.reg .sstore) tailCursor ∧
          RegisterContinuationZero tailCursor.pre.memory := by
  cases route with
  | atTarget cursor chronology site siteEq sourceMember targetEq instructionEq =>
      left
      exact .registry cursor targetEq (by simpa [siteEq] using sourceMember)
        functionIndex
  | next cursor chronology tailCursor edge rest =>
      have storeRun :=
        Exec.Deriv.SourceCursor.ninstRun_of_nextEdge cursor edge
      have memoryEq : cursor.pre.memory = tailCursor.pre.memory :=
        Ninst.Hinv.inv (f := Devm.memory) storeRun
      exact Or.inr ⟨tailCursor, rest, memoryEq ▸ zero⟩

private theorem finishSetPauser_registerCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp)
      ⟨finishSetPauserSlot, []⟩ finishSetPauser)
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (zero : RegisterContinuationZero cursor.pre.memory) :
    RegisterKernelCut (target := target) initial := by
  unfold finishSetPauser at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropLineContinuation
      (cursor := cursor) route
      (line := loadWord newPauserWord)
      (by
        intro instruction member
        simp only [loadWord, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h) zero
      (fun run zero => zero.of_run_loadWord run) with
    ⟨previousCursor, previousRoute, previousZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLineContinuation
      previousRoute (line := loadWord previousPauserWord)
      (by
        intro instruction member
        simp only [loadWord, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h) previousZero
      (fun run zero => zero.of_run_loadWord run) with
    ⟨targetCursor, targetRoute, targetZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLineContinuation
      targetRoute (line := loadWord targetWord)
      (by
        intro instruction member
        simp only [loadWord, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h) targetZero
      (fun run zero => zero.of_run_loadWord run) with
    ⟨eventCursor, eventRoute, eventZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne eventRoute
      (by intro h; cases h) with
    ⟨eventChronology, logCursor, eventEdge, logRoute⟩
  have logZero : RegisterContinuationZero logCursor.pre.memory := by
    rw [← (of_run_pushB256
      (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        eventCursor eventEdge)).memory]
    exact eventZero
  rcases Exec.Deriv.SourceCursor.Toward.dropLineContinuation
      logRoute (line := logWith 3 0 0)
      (by
        intro instruction member
        simp only [logWith, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl | rfl <;> intro h <;> cases h) logZero
      (fun run zero => zero.of_run_logWith run) with
    ⟨continuationCursor, continuationRoute,
      continuationZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLineRun continuationRoute
      (line := loadWord continuationWord) (by
        intro instruction member
        simp only [loadWord, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h) with
    ⟨iszeroPath, iszeroCursor, continuationRun, continuationChronology,
      iszeroRoute⟩
  have continuationPrefix :
      [(0 : B256)] <<+ iszeroCursor.pre.stack :=
    (continuationZero.prefix_of_loadWord nil_pref continuationRun).1
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne iszeroRoute
      (by intro h; cases h) with
    ⟨iszeroChronology, branchCursor, iszeroEdge, branchRoute⟩
  have onePrefix : [(1 : B256)] <<+ branchCursor.pre.stack := by
    have checked := prefix_of_iszero
      (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        iszeroCursor iszeroEdge) continuationPrefix
    simpa [B256.eqCheck] using checked
  rcases Exec.Deriv.SourceCursor.Toward.branchArmStorage
      branchCursor compiled targetAt branchRoute with
    ⟨pauseCursor, pauseRoute, branchStorage, zeroPrefix⟩ |
      ⟨flag, nonzero, flagPrefix, registerCursor, registerRoute,
        branchStorage⟩
  · have oneEqZero : (1 : B256) = 0 :=
      pref_head_unique onePrefix zeroPrefix
    exact (B256.zero_ne_one oneEqZero.symm).elim
  · cases registerRoute with
    | call cursor chronology lookup bodyCursor compilerPrefix rest =>
        simp [runtime, aux, registerAfterSetSlot] at lookup
        cases lookup
        exact .registerAfterSet bodyCursor rest

private theorem removeTarget_registerCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp)
      ⟨removeTargetSlot, []⟩ removeTarget)
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (zero : RegisterContinuationZero cursor.pre.memory) :
    RegisterKernelCut (target := target) initial := by
  unfold removeTarget at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation route zero with
    ⟨indexCursor, indexRoute, indexZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation indexRoute
      (line := tagTop indexRegion ++ [Ninst.sload])
      (by
        intro instruction member
        simp only [tagTop, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at member
        rcases member with (rfl | rfl) | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) indexZero with
    ⟨removedStoreCursor, removedStoreRoute,
      removedStoreZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropMstoreAtAfterContinuation
      removedStoreRoute removedStoreZero
      (by decide +kernel) with
    ⟨lengthLoadCursor, lengthLoadRoute, lengthLoadZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation lengthLoadRoute
      (line := [Ninst.pushB256 arrayLengthSlot, Ninst.sload])
      (by
        intro instruction member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) lengthLoadZero with
    ⟨lengthStoreCursor, lengthStoreRoute,
      lengthStoreZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropMstoreAtAfterContinuation
      lengthStoreRoute lengthStoreZero
      (by decide +kernel) with
    ⟨lastLoadCursor, lastLoadRoute, lastLoadZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
      lastLoadRoute lastLoadZero with
    ⟨lastKeyCursor, lastKeyRoute, lastKeyZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation lastKeyRoute
      (line := tagTop arrayRegion ++ [Ninst.sload])
      (by
        intro instruction member
        simp only [tagTop, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at member
        rcases member with (rfl | rfl) | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) lastKeyZero with
    ⟨lastStoreCursor, lastStoreRoute, lastStoreZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropMstoreAtAfterContinuation
      lastStoreRoute lastStoreZero
      (by decide +kernel) with
    ⟨holeValueCursor, holeValueRoute, holeValueZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
      holeValueRoute holeValueZero with
    ⟨holeIndexCursor, holeIndexRoute, holeIndexZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
      holeIndexRoute holeIndexZero with
    ⟨holeKeyCursor, holeKeyRoute, holeKeyZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation holeKeyRoute
      (line := tagTop arrayRegion)
      (by
        intro instruction member
        simp only [tagTop, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) holeKeyZero with
    ⟨holeStoreCursor, holeStoreRoute, holeStoreZero⟩
  rcases registerKernelCut_at_sstore holeStoreCursor holeStoreRoute
      holeStoreZero (by simp [removeTargetSlot]) with cut | ⟨movedIndexCursor,
        movedIndexRoute, movedIndexZero⟩
  · exact cut
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
      movedIndexRoute movedIndexZero with
    ⟨movedValueCursor, movedValueRoute, movedValueZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
      movedValueRoute movedValueZero with
    ⟨movedKeyCursor, movedKeyRoute, movedKeyZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation movedKeyRoute
      (line := tagTop indexRegion)
      (by
        intro instruction member
        simp only [tagTop, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) movedKeyZero with
    ⟨movedStoreCursor, movedStoreRoute, movedStoreZero⟩
  rcases registerKernelCut_at_sstore movedStoreCursor movedStoreRoute
      movedStoreZero (by simp [removeTargetSlot]) with cut | ⟨clearTailPushCursor,
        clearTailPushRoute, clearTailPushZero⟩
  · exact cut
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation
      clearTailPushRoute
      (line := [Ninst.pushB256 0])
      (by simp [Ninst.pushB256])
      (fun run => Line.of_inv Devm.memory (by line_inv) run)
      clearTailPushZero with
    ⟨clearTailLoadCursor, clearTailLoadRoute,
      clearTailLoadZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
      clearTailLoadRoute clearTailLoadZero with
    ⟨clearTailKeyCursor, clearTailKeyRoute,
      clearTailKeyZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation clearTailKeyRoute
      (line := tagTop arrayRegion)
      (by
        intro instruction member
        simp only [tagTop, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run)
      clearTailKeyZero with
    ⟨clearTailStoreCursor, clearTailStoreRoute,
      clearTailStoreZero⟩
  rcases registerKernelCut_at_sstore clearTailStoreCursor clearTailStoreRoute
      clearTailStoreZero (by simp [removeTargetSlot]) with cut | ⟨lengthValueCursor,
        lengthValueRoute, lengthValueZero⟩
  · exact cut
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
      lengthValueRoute lengthValueZero with
    ⟨lengthSubCursor, lengthSubRoute, lengthSubZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation lengthSubRoute
      (line := [Ninst.pushB256 1, Ninst.swap 0, Ninst.sub,
        Ninst.pushB256 arrayLengthSlot])
      (by
        intro instruction member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;>
          intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) lengthSubZero with
    ⟨lengthWriteCursor, lengthWriteRoute,
      lengthWriteZero⟩
  rcases registerKernelCut_at_sstore lengthWriteCursor lengthWriteRoute
      lengthWriteZero (by simp [removeTargetSlot]) with cut | ⟨clearIndexPushCursor,
        clearIndexPushRoute, clearIndexPushZero⟩
  · exact cut
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation
      clearIndexPushRoute
      (line := [Ninst.pushB256 0])
      (by simp [Ninst.pushB256])
      (fun run => Line.of_inv Devm.memory (by line_inv) run)
      clearIndexPushZero with
    ⟨clearIndexLoadCursor, clearIndexLoadRoute,
      clearIndexLoadZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
      clearIndexLoadRoute clearIndexLoadZero with
    ⟨clearIndexKeyCursor, clearIndexKeyRoute,
      clearIndexKeyZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation clearIndexKeyRoute
      (line := tagTop indexRegion)
      (by
        intro instruction member
        simp only [tagTop, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run)
      clearIndexKeyZero with
    ⟨clearIndexStoreCursor, clearIndexStoreRoute,
      clearIndexStoreZero⟩
  rcases registerKernelCut_at_sstore clearIndexStoreCursor clearIndexStoreRoute
      clearIndexStoreZero (by simp [removeTargetSlot]) with cut | ⟨finishCallCursor,
        finishCallRoute, finishCallZero⟩
  · exact cut
  rcases finishSetPauserCallContinuation finishCallCursor compiled targetAt
      finishCallRoute finishCallZero with
    ⟨finishCursor, finishRoute, finishZero⟩
  exact finishSetPauser_registerCut finishCursor compiled targetAt
    finishRoute finishZero

private theorem afterOldPauser_registerCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp)
      ⟨afterOldPauserSlot, []⟩ afterOldPauser)
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (zero : RegisterContinuationZero cursor.pre.memory) :
    RegisterKernelCut (target := target) initial := by
  unfold afterOldPauser at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation route zero with
    ⟨iszeroCursor, iszeroRoute, iszeroZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne iszeroRoute
      (by intro h; cases h) with
    ⟨iszeroChronology, branchCursor, iszeroEdge, branchRoute⟩
  have branchZero : RegisterContinuationZero branchCursor.pre.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory)
      (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        iszeroCursor iszeroEdge)]
    exact iszeroZero
  rcases Exec.Deriv.SourceCursor.Toward.branchArmContinuation
      branchCursor compiled targetAt branchRoute branchZero with
    ⟨incrementCursor, incrementRoute, incrementZero⟩ |
      ⟨removeCallCursor, removeCallRoute, removeCallZero⟩
  · rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
        incrementRoute incrementZero with
      ⟨countKeyCursor, countKeyRoute, countKeyZero⟩
    rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation countKeyRoute
        (line := tagTop countRegion ++
          [Ninst.sload, Ninst.pushB256 1, Ninst.add])
        (by
          intro instruction member
          simp only [tagTop, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false] at member
          rcases member with (rfl | rfl) | rfl | rfl | rfl <;>
            intro h <;> cases h)
        (fun run => Line.of_inv Devm.memory (by line_inv) run)
        countKeyZero with
      ⟨countValueCursor, countValueRoute, countValueZero⟩
    rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
        countValueRoute countValueZero with
      ⟨countTagCursor, countTagRoute, countTagZero⟩
    rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation countTagRoute
        (line := tagTop countRegion)
        (by
          intro instruction member
          simp only [tagTop, List.mem_cons, List.not_mem_nil,
            or_false] at member
          rcases member with rfl | rfl <;> intro h <;> cases h)
        (fun run => Line.of_inv Devm.memory (by line_inv) run)
        countTagZero with
      ⟨countStoreCursor, countStoreRoute, countStoreZero⟩
    rcases registerKernelCut_at_sstore countStoreCursor countStoreRoute
        countStoreZero (by simp [afterOldPauserSlot]) with cut |
          ⟨finishCallCursor, finishCallRoute, finishCallZero⟩
    · exact cut
    rcases finishSetPauserCallContinuation finishCallCursor compiled targetAt
        finishCallRoute finishCallZero with
      ⟨finishCursor, finishRoute, finishZero⟩
    exact finishSetPauser_registerCut finishCursor compiled targetAt
      finishRoute finishZero
  · rcases Exec.Deriv.SourceCursor.Toward.callBodyContinuation
        removeCallCursor compiled targetAt removeCallRoute removeCallZero with
      ⟨body, lookup, removeCursor, removeRoute, removeZero⟩
    simp [runtime, aux, removeTargetSlot] at lookup
    cases lookup
    exact removeTarget_registerCut removeCursor compiled targetAt
      removeRoute removeZero

private theorem appendTarget_registerCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp)
      ⟨appendTargetSlot, []⟩ appendTarget)
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (zero : RegisterContinuationZero cursor.pre.memory) :
    RegisterKernelCut (target := target) initial := by
  unfold appendTarget at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation route
      (line := [Ninst.pushB256 arrayLengthSlot, Ninst.sload,
        Ninst.pushB256 1, Ninst.add, Ninst.dup 0])
      (by
        intro instruction member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl <;>
          intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) zero with
    ⟨lengthStoreCursor, lengthStoreRoute, lengthStoreZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropMstoreAtAfterContinuation
      lengthStoreRoute lengthStoreZero (by decide +kernel) with
    ⟨arrayValueCursor, arrayValueRoute, arrayValueZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
      arrayValueRoute arrayValueZero with
    ⟨arrayIndexCursor, arrayIndexRoute, arrayIndexZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
      arrayIndexRoute arrayIndexZero with
    ⟨arrayTagCursor, arrayTagRoute, arrayTagZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation arrayTagRoute
      (line := tagTop arrayRegion)
      (by
        intro instruction member
        simp only [tagTop, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) arrayTagZero with
    ⟨arrayStoreCursor, arrayStoreRoute, arrayStoreZero⟩
  rcases registerKernelCut_at_sstore arrayStoreCursor arrayStoreRoute
      arrayStoreZero (by simp [appendTargetSlot]) with cut |
        ⟨reverseValueCursor, reverseValueRoute, reverseValueZero⟩
  · exact cut
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
      reverseValueRoute reverseValueZero with
    ⟨reverseTargetCursor, reverseTargetRoute, reverseTargetZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
      reverseTargetRoute reverseTargetZero with
    ⟨reverseTagCursor, reverseTagRoute, reverseTagZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation reverseTagRoute
      (line := tagTop indexRegion)
      (by
        intro instruction member
        simp only [tagTop, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) reverseTagZero with
    ⟨reverseStoreCursor, reverseStoreRoute, reverseStoreZero⟩
  rcases registerKernelCut_at_sstore reverseStoreCursor reverseStoreRoute
      reverseStoreZero (by simp [appendTargetSlot]) with cut |
        ⟨finalLengthCursor, finalLengthRoute, finalLengthZero⟩
  · exact cut
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
      finalLengthRoute finalLengthZero with
    ⟨lengthKeyCursor, lengthKeyRoute, lengthKeyZero⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation lengthKeyRoute
      (line := [Ninst.pushB256 arrayLengthSlot])
      (by simp [Ninst.pushB256])
      (fun run => Line.of_inv Devm.memory (by line_inv) run) lengthKeyZero with
    ⟨finalStoreCursor, finalStoreRoute, finalStoreZero⟩
  rcases registerKernelCut_at_sstore finalStoreCursor finalStoreRoute
      finalStoreZero (by simp [appendTargetSlot]) with cut |
        ⟨afterOldCallCursor, afterOldCallRoute, afterOldCallZero⟩
  · exact cut
  rcases Exec.Deriv.SourceCursor.Toward.callBodyContinuation
      afterOldCallCursor compiled targetAt afterOldCallRoute afterOldCallZero with
    ⟨body, lookup, afterOldCursor, afterOldRoute, afterOldZero⟩
  simp [runtime, aux, afterOldPauserSlot] at lookup
  cases lookup
  exact afterOldPauser_registerCut afterOldCursor compiled targetAt
    afterOldRoute afterOldZero

private theorem setPauserKernel_registerCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp)
      ⟨setPauserSlot, []⟩ setPauserKernel)
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (zero : RegisterContinuationZero cursor.pre.memory) :
    RegisterKernelCut (target := target) initial := by
  unfold setPauserKernel at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation route zero with
    ⟨targetZeroCursor, targetZeroRoute, targetZeroMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne targetZeroRoute
      (by intro h; cases h) with
    ⟨targetZeroChronology, targetBranchCursor, targetZeroEdge,
      targetBranchRoute⟩
  have targetBranchMemory :
      RegisterContinuationZero targetBranchCursor.pre.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory)
      (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        targetZeroCursor targetZeroEdge)]
    exact targetZeroMemory
  rcases Exec.Deriv.SourceCursor.Toward.branchArmContinuation
      targetBranchCursor compiled targetAt targetBranchRoute
      targetBranchMemory with
    ⟨assignmentCursor, assignmentRoute, assignmentMemory⟩ |
      ⟨zeroErrorCursor, zeroErrorRoute, zeroErrorMemory⟩
  · rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
        assignmentRoute assignmentMemory with
      ⟨assignmentTagCursor, assignmentTagRoute, assignmentTagMemory⟩
    rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation
        assignmentTagRoute
        (line := tagTop assignmentRegion ++ [Ninst.sload, Ninst.dup 0])
        (by
          intro instruction member
          simp only [tagTop, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false] at member
          rcases member with (rfl | rfl) | rfl | rfl <;>
            intro h <;> cases h)
        (fun run => Line.of_inv Devm.memory (by line_inv) run)
        assignmentTagMemory with
      ⟨previousStoreCursor, previousStoreRoute, previousStoreMemory⟩
    rcases Exec.Deriv.SourceCursor.Toward.dropMstoreAtBeforeContinuation
        previousStoreRoute previousStoreMemory (by decide +kernel) with
      ⟨newValueCursor, newValueRoute, newValueMemory⟩
    rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
        newValueRoute newValueMemory with
      ⟨assignmentTargetCursor, assignmentTargetRoute,
        assignmentTargetMemory⟩
    rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
        assignmentTargetRoute assignmentTargetMemory with
      ⟨assignmentKeyCursor, assignmentKeyRoute, assignmentKeyMemory⟩
    rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation
        assignmentKeyRoute (line := tagTop assignmentRegion)
        (by
          intro instruction member
          simp only [tagTop, List.mem_cons, List.not_mem_nil,
            or_false] at member
          rcases member with rfl | rfl <;> intro h <;> cases h)
        (fun run => Line.of_inv Devm.memory (by line_inv) run)
        assignmentKeyMemory with
      ⟨assignmentStoreCursor, assignmentStoreRoute, assignmentStoreMemory⟩
    rcases registerKernelCut_at_sstore assignmentStoreCursor
        assignmentStoreRoute assignmentStoreMemory
        (by simp [setPauserSlot]) with cut |
          ⟨oldZeroCursor, oldZeroRoute, oldZeroMemory⟩
    · exact cut
    rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne oldZeroRoute
        (by intro h; cases h) with
      ⟨oldZeroChronology, oldBranchCursor, oldZeroEdge, oldBranchRoute⟩
    have oldBranchMemory :
        RegisterContinuationZero oldBranchCursor.pre.memory := by
      rw [← Ninst.Hinv.inv (f := Devm.memory)
        (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
          oldZeroCursor oldZeroEdge)]
      exact oldZeroMemory
    rcases Exec.Deriv.SourceCursor.Toward.branchArmContinuation
        oldBranchCursor compiled targetAt oldBranchRoute oldBranchMemory with
      ⟨oldCountCursor, oldCountRoute, oldCountMemory⟩ |
        ⟨appendCallCursor, appendCallRoute, appendCallMemory⟩
    · rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
          oldCountRoute oldCountMemory with
        ⟨oldCountTagCursor, oldCountTagRoute, oldCountTagMemory⟩
      rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation
          oldCountTagRoute
          (line := tagTop countRegion ++ [Ninst.sload, Ninst.pushB256 1,
            Ninst.swap 0, Ninst.sub])
          (by
            intro instruction member
            simp only [tagTop, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false] at member
            rcases member with (rfl | rfl) | rfl | rfl | rfl | rfl <;>
              intro h <;> cases h)
          (fun run => Line.of_inv Devm.memory (by line_inv) run)
          oldCountTagMemory with
        ⟨oldCountValueCursor, oldCountValueRoute, oldCountValueMemory⟩
      rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordContinuation
          oldCountValueRoute oldCountValueMemory with
        ⟨oldCountKeyCursor, oldCountKeyRoute, oldCountKeyMemory⟩
      rcases Exec.Deriv.SourceCursor.Toward.dropSilentContinuation
          oldCountKeyRoute (line := tagTop countRegion)
          (by
            intro instruction member
            simp only [tagTop, List.mem_cons, List.not_mem_nil,
              or_false] at member
            rcases member with rfl | rfl <;> intro h <;> cases h)
          (fun run => Line.of_inv Devm.memory (by line_inv) run)
          oldCountKeyMemory with
        ⟨oldCountStoreCursor, oldCountStoreRoute, oldCountStoreMemory⟩
      rcases registerKernelCut_at_sstore oldCountStoreCursor
          oldCountStoreRoute oldCountStoreMemory
          (by simp [setPauserSlot]) with cut |
            ⟨afterOldCallCursor, afterOldCallRoute, afterOldCallMemory⟩
      · exact cut
      rcases Exec.Deriv.SourceCursor.Toward.callBodyContinuation
          afterOldCallCursor compiled targetAt afterOldCallRoute
          afterOldCallMemory with
        ⟨body, lookup, afterOldCursor, afterOldRoute, afterOldMemory⟩
      simp [runtime, aux, afterOldPauserSlot] at lookup
      cases lookup
      exact afterOldPauser_registerCut afterOldCursor compiled targetAt
        afterOldRoute afterOldMemory
    · rcases Exec.Deriv.SourceCursor.Toward.callBodyContinuation
          appendCallCursor compiled targetAt appendCallRoute
          appendCallMemory with
        ⟨body, lookup, appendCursor, appendRoute, appendMemory⟩
      simp [runtime, aux, appendTargetSlot] at lookup
      cases lookup
      exact appendTarget_registerCut appendCursor compiled targetAt
        appendRoute appendMemory
  · exact (zeroErrorCursor.noSstore_of_entrySstoreFree compiled
      [pausableZeroErrorSlot] rfl
      (Exec.Deriv.SourceCursor.Toward.chronology
        zeroErrorRoute).cursorToTarget targetAt).elim

private theorem registerPauser_registerCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)}
    {path : Prog.SourcePath}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (registerPauser dp))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    RegisterKernelCut (target := target) initial := by
  rcases requireStaticArgsToward 2 cursor compiled targetAt route with
    ⟨firstPath, firstCursor, firstRoute⟩
  rcases canonicalAddressArgToward 0 firstCursor compiled targetAt firstRoute with
    ⟨secondPath, secondCursor, secondRoute⟩
  rcases canonicalAddressArgToward 1 secondCursor compiled targetAt secondRoute with
    ⟨adminPath, adminCursor, adminRoute⟩
  rcases onlyAdminToward adminCursor compiled targetAt adminRoute with
    ⟨setupPath, setupCursor, setupRoute⟩
  let setupBeforeContinuation : Line :=
    arg 0 ++ mstoreAt targetWord ++
      arg 1 ++ mstoreAt newPauserWord ++
      [Ninst.pushB256 0] ++ mstoreAt previousPauserWord
  rcases Exec.Deriv.SourceCursor.Toward.dropLineRun setupRoute
      (line := setupBeforeContinuation) (by
        intro instruction member
        simp [setupBeforeContinuation, arg, cdl, mstoreAt,
          Ninst.pushB256] at member
        rcases member with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl <;>
          intro h <;> cases h) with
    ⟨zeroPushPath, zeroPushCursor, setupRun, setupChronology,
      zeroPushRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne zeroPushRoute
      (by intro h; cases h) with
    ⟨zeroPushChronology, continuationStoreCursor, zeroPushEdge,
      continuationStoreRoute⟩
  have zeroPrefix : [(0 : B256)] <<+
      continuationStoreCursor.pre.stack := by
    simpa [Ninst.pushB256] using prefix_of_push
      (of_run_pushB256
        (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
          zeroPushCursor zeroPushEdge)) nil_pref
  rcases Exec.Deriv.SourceCursor.Toward.dropLineRun continuationStoreRoute
      (line := mstoreAt continuationWord) (by
        intro instruction member
        simp only [mstoreAt, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h) with
    ⟨callPath, callCursor, continuationRun, continuationChronology,
      callRoute⟩
  have continuationZero :
      RegisterContinuationZero callCursor.pre.memory :=
    RegisterContinuationZero.of_run_seed zeroPrefix continuationRun
  rcases Exec.Deriv.SourceCursor.Toward.callBodyContinuation
      callCursor compiled targetAt callRoute continuationZero with
    ⟨body, lookup, kernelCursor, kernelRoute, kernelZero⟩
  simp [runtime, aux, setPauserSlot] at lookup
  cases lookup
  exact setPauserKernel_registerCut kernelCursor compiled targetAt
    kernelRoute kernelZero

private inductive PauseKernelCut
    {dp : DeployParams} {root target : Exec.Deriv}
    (initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)) : Prop
  | registry {path : Prog.SourcePath} {tail : Func}
      (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
        (.next (.reg .sstore) tail))
      (targetEq : cursor.node = target)
      (sourceMember :
        ({ path := path, pc := cursor.pc,
            instruction := (.reg .sstore) } : Prog.SourceSite) ∈
          (runtime dp).sourceSites)
      (functionIndex : path.functionIndex ∈ [14, 15, 17]) :
      PauseKernelCut initial
  | pauseAfterSet
      (cursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨pauseAfterSetSlot, []⟩ pauseAfterSet)
      (route : Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) cursor) :
      PauseKernelCut initial

private theorem pauseKernelCut_at_sstore
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)}
    {path : Prog.SourcePath} {tail : Func}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (.next (.reg .sstore) tail))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (carrier : PauseKernelMemory cursor.pre.memory)
    (functionIndex : path.functionIndex ∈ [14, 15, 17]) :
    PauseKernelCut (target := target) initial ∨
      ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
          ⟨path.functionIndex, path.steps ++ [.rest]⟩ tail,
        Exec.Deriv.SourceCursor.Toward
            initial target (.reg .sstore) tailCursor ∧
          PauseKernelMemory tailCursor.pre.memory := by
  cases route with
  | atTarget cursor chronology site siteEq sourceMember targetEq instructionEq =>
      left
      exact .registry cursor targetEq (by simpa [siteEq] using sourceMember)
        functionIndex
  | next cursor chronology tailCursor edge rest =>
      have storeRun :=
        Exec.Deriv.SourceCursor.ninstRun_of_nextEdge cursor edge
      have memoryEq : cursor.pre.memory = tailCursor.pre.memory :=
        Ninst.Hinv.inv (f := Devm.memory) storeRun
      exact Or.inr ⟨tailCursor, rest, memoryEq ▸ carrier⟩

private theorem finishSetPauser_pauseCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp)
      ⟨finishSetPauserSlot, []⟩ finishSetPauser)
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (carrier : PauseKernelMemory cursor.pre.memory) :
    PauseKernelCut (target := target) initial := by
  unfold finishSetPauser at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      route carrier with
    ⟨previousCursor, previousRoute, previousMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      previousRoute previousMemory with
    ⟨targetCursor, targetRoute, targetMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      targetRoute targetMemory with
    ⟨eventCursor, eventRoute, eventMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne eventRoute
      (by intro h; cases h) with
    ⟨eventChronology, logCursor, eventEdge, logRoute⟩
  have logMemory : PauseKernelMemory logCursor.pre.memory := by
    rw [← (of_run_pushB256
      (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        eventCursor eventEdge)).memory]
    exact eventMemory
  rcases Exec.Deriv.SourceCursor.Toward.dropLinePauseMemory
      logRoute (line := logWith 3 0 0)
      (by
        intro instruction member
        simp only [logWith, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl | rfl <;> intro h <;> cases h)
      logMemory (fun run memory => memory.of_run_logWith run) with
    ⟨continuationCursor, continuationRoute, continuationMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLineRun continuationRoute
      (line := loadWord continuationWord) (by
        intro instruction member
        simp only [loadWord, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h) with
    ⟨iszeroPath, iszeroCursor, continuationRun, continuationChronology,
      iszeroRoute⟩
  have continuationPrefix :
      [(1 : B256)] <<+ iszeroCursor.pre.stack :=
    (continuationMemory.2.prefix_of_loadWord nil_pref continuationRun).1
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne iszeroRoute
      (by intro h; cases h) with
    ⟨iszeroChronology, branchCursor, iszeroEdge, branchRoute⟩
  have zeroPrefix : [(0 : B256)] <<+ branchCursor.pre.stack := by
    have checked := prefix_of_iszero
      (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        iszeroCursor iszeroEdge) continuationPrefix
    simpa [B256.eqCheck, show (1 : B256) ≠ 0 by decide +kernel] using checked
  rcases Exec.Deriv.SourceCursor.Toward.branchArmStorage
      branchCursor compiled targetAt branchRoute with
    ⟨pauseCursor, pauseRoute, branchStorage, actualZeroPrefix⟩ |
      ⟨flag, nonzero, flagPrefix, registerCursor, registerRoute,
        branchStorage⟩
  · cases pauseRoute with
    | call cursor chronology lookup bodyCursor compilerPrefix rest =>
        simp [runtime, aux, pauseAfterSetSlot] at lookup
        cases lookup
        exact .pauseAfterSet bodyCursor rest
  · have flagEqZero : flag = 0 := pref_head_unique flagPrefix zeroPrefix
    exact (nonzero flagEqZero).elim

private theorem finishSetPauserCallPauseMemory
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (.call finishSetPauserSlot))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (carrier : PauseKernelMemory cursor.pre.memory) :
    ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨finishSetPauserSlot, []⟩ finishSetPauser,
      Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) bodyCursor ∧
        PauseKernelMemory bodyCursor.pre.memory := by
  rcases Exec.Deriv.SourceCursor.Toward.callBodyPauseMemory
      cursor compiled targetAt route carrier with
    ⟨body, lookup, bodyCursor, bodyRoute, bodyMemory⟩
  simp [runtime, aux, finishSetPauserSlot] at lookup
  cases lookup
  exact ⟨bodyCursor, bodyRoute, bodyMemory⟩

private theorem removeTarget_pauseCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp)
      ⟨removeTargetSlot, []⟩ removeTarget)
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (carrier : PauseKernelMemory cursor.pre.memory) :
    PauseKernelCut (target := target) initial := by
  unfold removeTarget at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      route carrier with
    ⟨indexCursor, indexRoute, indexMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory indexRoute
      (line := tagTop indexRegion ++ [Ninst.sload])
      (by
        intro instruction member
        simp only [tagTop, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at member
        rcases member with (rfl | rfl) | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) indexMemory with
    ⟨removedStoreCursor, removedStoreRoute, removedStoreMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropMstoreAtAfterPauseMemory
      removedStoreRoute removedStoreMemory (by decide +kernel) with
    ⟨lengthLoadCursor, lengthLoadRoute, lengthLoadMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory lengthLoadRoute
      (line := [Ninst.pushB256 arrayLengthSlot, Ninst.sload])
      (by
        intro instruction member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run)
      lengthLoadMemory with
    ⟨lengthStoreCursor, lengthStoreRoute, lengthStoreMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropMstoreAtAfterPauseMemory
      lengthStoreRoute lengthStoreMemory (by decide +kernel) with
    ⟨lastLoadCursor, lastLoadRoute, lastLoadMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      lastLoadRoute lastLoadMemory with
    ⟨lastKeyCursor, lastKeyRoute, lastKeyMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory lastKeyRoute
      (line := tagTop arrayRegion ++ [Ninst.sload])
      (by
        intro instruction member
        simp only [tagTop, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at member
        rcases member with (rfl | rfl) | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) lastKeyMemory with
    ⟨lastStoreCursor, lastStoreRoute, lastStoreMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropMstoreAtAfterPauseMemory
      lastStoreRoute lastStoreMemory (by decide +kernel) with
    ⟨holeValueCursor, holeValueRoute, holeValueMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      holeValueRoute holeValueMemory with
    ⟨holeIndexCursor, holeIndexRoute, holeIndexMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      holeIndexRoute holeIndexMemory with
    ⟨holeKeyCursor, holeKeyRoute, holeKeyMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory holeKeyRoute
      (line := tagTop arrayRegion)
      (by
        intro instruction member
        simp only [tagTop, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) holeKeyMemory with
    ⟨holeStoreCursor, holeStoreRoute, holeStoreMemory⟩
  rcases pauseKernelCut_at_sstore holeStoreCursor holeStoreRoute
      holeStoreMemory (by simp [removeTargetSlot]) with cut |
      ⟨movedIndexCursor, movedIndexRoute, movedIndexMemory⟩
  · exact cut
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      movedIndexRoute movedIndexMemory with
    ⟨movedValueCursor, movedValueRoute, movedValueMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      movedValueRoute movedValueMemory with
    ⟨movedKeyCursor, movedKeyRoute, movedKeyMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory movedKeyRoute
      (line := tagTop indexRegion)
      (by
        intro instruction member
        simp only [tagTop, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) movedKeyMemory with
    ⟨movedStoreCursor, movedStoreRoute, movedStoreMemory⟩
  rcases pauseKernelCut_at_sstore movedStoreCursor movedStoreRoute
      movedStoreMemory (by simp [removeTargetSlot]) with cut |
      ⟨clearTailPushCursor, clearTailPushRoute, clearTailPushMemory⟩
  · exact cut
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory
      clearTailPushRoute (line := [Ninst.pushB256 0])
      (by simp [Ninst.pushB256])
      (fun run => Line.of_inv Devm.memory (by line_inv) run)
      clearTailPushMemory with
    ⟨clearTailLoadCursor, clearTailLoadRoute, clearTailLoadMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      clearTailLoadRoute clearTailLoadMemory with
    ⟨clearTailKeyCursor, clearTailKeyRoute, clearTailKeyMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory clearTailKeyRoute
      (line := tagTop arrayRegion)
      (by
        intro instruction member
        simp only [tagTop, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run)
      clearTailKeyMemory with
    ⟨clearTailStoreCursor, clearTailStoreRoute, clearTailStoreMemory⟩
  rcases pauseKernelCut_at_sstore clearTailStoreCursor clearTailStoreRoute
      clearTailStoreMemory (by simp [removeTargetSlot]) with cut |
      ⟨lengthValueCursor, lengthValueRoute, lengthValueMemory⟩
  · exact cut
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      lengthValueRoute lengthValueMemory with
    ⟨lengthSubCursor, lengthSubRoute, lengthSubMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory lengthSubRoute
      (line := [Ninst.pushB256 1, Ninst.swap 0, Ninst.sub,
        Ninst.pushB256 arrayLengthSlot])
      (by
        intro instruction member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;>
          intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) lengthSubMemory with
    ⟨lengthWriteCursor, lengthWriteRoute, lengthWriteMemory⟩
  rcases pauseKernelCut_at_sstore lengthWriteCursor lengthWriteRoute
      lengthWriteMemory (by simp [removeTargetSlot]) with cut |
      ⟨clearIndexPushCursor, clearIndexPushRoute, clearIndexPushMemory⟩
  · exact cut
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory
      clearIndexPushRoute (line := [Ninst.pushB256 0])
      (by simp [Ninst.pushB256])
      (fun run => Line.of_inv Devm.memory (by line_inv) run)
      clearIndexPushMemory with
    ⟨clearIndexLoadCursor, clearIndexLoadRoute, clearIndexLoadMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      clearIndexLoadRoute clearIndexLoadMemory with
    ⟨clearIndexKeyCursor, clearIndexKeyRoute, clearIndexKeyMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory clearIndexKeyRoute
      (line := tagTop indexRegion)
      (by
        intro instruction member
        simp only [tagTop, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run)
      clearIndexKeyMemory with
    ⟨clearIndexStoreCursor, clearIndexStoreRoute, clearIndexStoreMemory⟩
  rcases pauseKernelCut_at_sstore clearIndexStoreCursor clearIndexStoreRoute
      clearIndexStoreMemory (by simp [removeTargetSlot]) with cut |
      ⟨finishCallCursor, finishCallRoute, finishCallMemory⟩
  · exact cut
  rcases finishSetPauserCallPauseMemory finishCallCursor compiled targetAt
      finishCallRoute finishCallMemory with
    ⟨finishCursor, finishRoute, finishMemory⟩
  exact finishSetPauser_pauseCut finishCursor compiled targetAt
    finishRoute finishMemory

private theorem afterOldPauser_pauseCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp)
      ⟨afterOldPauserSlot, []⟩ afterOldPauser)
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (carrier : PauseKernelMemory cursor.pre.memory) :
    PauseKernelCut (target := target) initial := by
  unfold afterOldPauser at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropLineRun route
      (line := loadWord newPauserWord) (by
        intro instruction member
        simp only [loadWord, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h) with
    ⟨iszeroPath, iszeroCursor, newPauserRun, newPauserChronology,
      iszeroRoute⟩
  have newPauserPrefix : [(0 : B256)] <<+ iszeroCursor.pre.stack :=
    (carrier.1.prefix_of_loadWord nil_pref newPauserRun).1
  have iszeroMemory : PauseKernelMemory iszeroCursor.pre.memory :=
    carrier.of_run_loadWord newPauserRun
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne iszeroRoute
      (by intro h; cases h) with
    ⟨iszeroChronology, branchCursor, iszeroEdge, branchRoute⟩
  have onePrefix : [(1 : B256)] <<+ branchCursor.pre.stack := by
    have checked := prefix_of_iszero
      (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        iszeroCursor iszeroEdge) newPauserPrefix
    simpa [B256.eqCheck] using checked
  have branchMemory : PauseKernelMemory branchCursor.pre.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory)
      (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        iszeroCursor iszeroEdge)]
    exact iszeroMemory
  rcases Exec.Deriv.SourceCursor.Toward.branchArmPauseMemory
      branchCursor compiled targetAt branchRoute branchMemory with
    ⟨incrementCursor, incrementRoute, incrementMemory, zeroPrefix⟩ |
      ⟨flag, nonzero, flagPrefix, removeCallCursor, removeCallRoute,
        removeCallMemory⟩
  · have oneEqZero : (1 : B256) = 0 :=
      pref_head_unique onePrefix zeroPrefix
    exact (B256.zero_ne_one oneEqZero.symm).elim
  · rcases Exec.Deriv.SourceCursor.Toward.callBodyPauseMemory
        removeCallCursor compiled targetAt removeCallRoute removeCallMemory with
      ⟨body, lookup, removeCursor, removeRoute, removeMemory⟩
    simp [runtime, aux, removeTargetSlot] at lookup
    cases lookup
    exact removeTarget_pauseCut removeCursor compiled targetAt
      removeRoute removeMemory

private theorem appendTarget_pauseCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp)
      ⟨appendTargetSlot, []⟩ appendTarget)
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (carrier : PauseKernelMemory cursor.pre.memory) :
    PauseKernelCut (target := target) initial := by
  unfold appendTarget at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory route
      (line := [Ninst.pushB256 arrayLengthSlot, Ninst.sload,
        Ninst.pushB256 1, Ninst.add, Ninst.dup 0])
      (by
        intro instruction member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl <;>
          intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) carrier with
    ⟨lengthStoreCursor, lengthStoreRoute, lengthStoreMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropMstoreAtAfterPauseMemory
      lengthStoreRoute lengthStoreMemory (by decide +kernel) with
    ⟨arrayValueCursor, arrayValueRoute, arrayValueMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      arrayValueRoute arrayValueMemory with
    ⟨arrayIndexCursor, arrayIndexRoute, arrayIndexMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      arrayIndexRoute arrayIndexMemory with
    ⟨arrayTagCursor, arrayTagRoute, arrayTagMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory arrayTagRoute
      (line := tagTop arrayRegion)
      (by
        intro instruction member
        simp only [tagTop, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run) arrayTagMemory with
    ⟨arrayStoreCursor, arrayStoreRoute, arrayStoreMemory⟩
  rcases pauseKernelCut_at_sstore arrayStoreCursor arrayStoreRoute
      arrayStoreMemory (by simp [appendTargetSlot]) with cut |
      ⟨reverseValueCursor, reverseValueRoute, reverseValueMemory⟩
  · exact cut
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      reverseValueRoute reverseValueMemory with
    ⟨reverseTargetCursor, reverseTargetRoute, reverseTargetMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      reverseTargetRoute reverseTargetMemory with
    ⟨reverseTagCursor, reverseTagRoute, reverseTagMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory reverseTagRoute
      (line := tagTop indexRegion)
      (by
        intro instruction member
        simp only [tagTop, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> intro h <;> cases h)
      (fun run => Line.of_inv Devm.memory (by line_inv) run)
      reverseTagMemory with
    ⟨reverseStoreCursor, reverseStoreRoute, reverseStoreMemory⟩
  rcases pauseKernelCut_at_sstore reverseStoreCursor reverseStoreRoute
      reverseStoreMemory (by simp [appendTargetSlot]) with cut |
      ⟨finalLengthCursor, finalLengthRoute, finalLengthMemory⟩
  · exact cut
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
      finalLengthRoute finalLengthMemory with
    ⟨lengthKeyCursor, lengthKeyRoute, lengthKeyMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory lengthKeyRoute
      (line := [Ninst.pushB256 arrayLengthSlot])
      (by simp [Ninst.pushB256])
      (fun run => Line.of_inv Devm.memory (by line_inv) run) lengthKeyMemory with
    ⟨finalStoreCursor, finalStoreRoute, finalStoreMemory⟩
  rcases pauseKernelCut_at_sstore finalStoreCursor finalStoreRoute
      finalStoreMemory (by simp [appendTargetSlot]) with cut |
      ⟨afterOldCallCursor, afterOldCallRoute, afterOldCallMemory⟩
  · exact cut
  rcases Exec.Deriv.SourceCursor.Toward.callBodyPauseMemory
      afterOldCallCursor compiled targetAt afterOldCallRoute
      afterOldCallMemory with
    ⟨body, lookup, afterOldCursor, afterOldRoute, afterOldMemory⟩
  simp [runtime, aux, afterOldPauserSlot] at lookup
  cases lookup
  exact afterOldPauser_pauseCut afterOldCursor compiled targetAt
    afterOldRoute afterOldMemory

private theorem setPauserKernel_pauseCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp)
      ⟨setPauserSlot, []⟩ setPauserKernel)
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (carrier : PauseKernelMemory cursor.pre.memory) :
    PauseKernelCut (target := target) initial := by
  unfold setPauserKernel at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory route carrier with
    ⟨targetZeroCursor, targetZeroRoute, targetZeroMemory⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne targetZeroRoute
      (by intro h; cases h) with
    ⟨targetZeroChronology, targetBranchCursor, targetZeroEdge,
      targetBranchRoute⟩
  have targetBranchMemory :
      PauseKernelMemory targetBranchCursor.pre.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory)
      (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
        targetZeroCursor targetZeroEdge)]
    exact targetZeroMemory
  rcases Exec.Deriv.SourceCursor.Toward.branchArmPauseMemory
      targetBranchCursor compiled targetAt targetBranchRoute
      targetBranchMemory with
    ⟨assignmentCursor, assignmentRoute, assignmentMemory, zeroPrefix⟩ |
      ⟨flag, nonzero, flagPrefix, zeroErrorCursor, zeroErrorRoute,
        zeroErrorMemory⟩
  · rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
        assignmentRoute assignmentMemory with
      ⟨assignmentTagCursor, assignmentTagRoute, assignmentTagMemory⟩
    rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory
        assignmentTagRoute
        (line := tagTop assignmentRegion ++ [Ninst.sload, Ninst.dup 0])
        (by
          intro instruction member
          simp only [tagTop, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false] at member
          rcases member with (rfl | rfl) | rfl | rfl <;>
            intro h <;> cases h)
        (fun run => Line.of_inv Devm.memory (by line_inv) run)
        assignmentTagMemory with
      ⟨previousStoreCursor, previousStoreRoute, previousStoreMemory⟩
    rcases Exec.Deriv.SourceCursor.Toward.dropLinePauseMemory
        previousStoreRoute (line := mstoreAt previousPauserWord)
        (by
          intro instruction member
          simp only [mstoreAt, List.mem_cons, List.not_mem_nil,
            or_false] at member
          rcases member with rfl | rfl <;> intro h <;> cases h)
        previousStoreMemory (fun run memory =>
          ⟨memory.1.of_run_mstoreAtAfter (by decide +kernel) run,
            memory.2.of_run_mstoreAtBefore (by decide +kernel) run⟩) with
      ⟨newValueCursor, newValueRoute, newValueMemory⟩
    rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
        newValueRoute newValueMemory with
      ⟨assignmentTargetCursor, assignmentTargetRoute,
        assignmentTargetMemory⟩
    rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
        assignmentTargetRoute assignmentTargetMemory with
      ⟨assignmentKeyCursor, assignmentKeyRoute, assignmentKeyMemory⟩
    rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory
        assignmentKeyRoute (line := tagTop assignmentRegion)
        (by
          intro instruction member
          simp only [tagTop, List.mem_cons, List.not_mem_nil,
            or_false] at member
          rcases member with rfl | rfl <;> intro h <;> cases h)
        (fun run => Line.of_inv Devm.memory (by line_inv) run)
        assignmentKeyMemory with
      ⟨assignmentStoreCursor, assignmentStoreRoute, assignmentStoreMemory⟩
    rcases pauseKernelCut_at_sstore assignmentStoreCursor
        assignmentStoreRoute assignmentStoreMemory
        (by simp [setPauserSlot]) with cut |
        ⟨oldZeroCursor, oldZeroRoute, oldZeroMemory⟩
    · exact cut
    rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne oldZeroRoute
        (by intro h; cases h) with
      ⟨oldZeroChronology, oldBranchCursor, oldZeroEdge, oldBranchRoute⟩
    have oldBranchMemory : PauseKernelMemory oldBranchCursor.pre.memory := by
      rw [← Ninst.Hinv.inv (f := Devm.memory)
        (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
          oldZeroCursor oldZeroEdge)]
      exact oldZeroMemory
    rcases Exec.Deriv.SourceCursor.Toward.branchArmPauseMemory
        oldBranchCursor compiled targetAt oldBranchRoute oldBranchMemory with
      ⟨oldCountCursor, oldCountRoute, oldCountMemory, oldZeroPrefix⟩ |
        ⟨oldFlag, oldNonzero, oldFlagPrefix, appendCallCursor,
          appendCallRoute, appendCallMemory⟩
    · rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
          oldCountRoute oldCountMemory with
        ⟨oldCountTagCursor, oldCountTagRoute, oldCountTagMemory⟩
      rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory
          oldCountTagRoute
          (line := tagTop countRegion ++ [Ninst.sload, Ninst.pushB256 1,
            Ninst.swap 0, Ninst.sub])
          (by
            intro instruction member
            simp only [tagTop, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false] at member
            rcases member with (rfl | rfl) | rfl | rfl | rfl | rfl <;>
              intro h <;> cases h)
          (fun run => Line.of_inv Devm.memory (by line_inv) run)
          oldCountTagMemory with
        ⟨oldCountValueCursor, oldCountValueRoute, oldCountValueMemory⟩
      rcases Exec.Deriv.SourceCursor.Toward.dropLoadWordPauseMemory
          oldCountValueRoute oldCountValueMemory with
        ⟨oldCountKeyCursor, oldCountKeyRoute, oldCountKeyMemory⟩
      rcases Exec.Deriv.SourceCursor.Toward.dropSilentPauseMemory
          oldCountKeyRoute (line := tagTop countRegion)
          (by
            intro instruction member
            simp only [tagTop, List.mem_cons, List.not_mem_nil,
              or_false] at member
            rcases member with rfl | rfl <;> intro h <;> cases h)
          (fun run => Line.of_inv Devm.memory (by line_inv) run)
          oldCountKeyMemory with
        ⟨oldCountStoreCursor, oldCountStoreRoute, oldCountStoreMemory⟩
      rcases pauseKernelCut_at_sstore oldCountStoreCursor
          oldCountStoreRoute oldCountStoreMemory
          (by simp [setPauserSlot]) with cut |
          ⟨afterOldCallCursor, afterOldCallRoute, afterOldCallMemory⟩
      · exact cut
      rcases Exec.Deriv.SourceCursor.Toward.callBodyPauseMemory
          afterOldCallCursor compiled targetAt afterOldCallRoute
          afterOldCallMemory with
        ⟨body, lookup, afterOldCursor, afterOldRoute, afterOldMemory⟩
      simp [runtime, aux, afterOldPauserSlot] at lookup
      cases lookup
      exact afterOldPauser_pauseCut afterOldCursor compiled targetAt
        afterOldRoute afterOldMemory
    · rcases Exec.Deriv.SourceCursor.Toward.callBodyPauseMemory
          appendCallCursor compiled targetAt appendCallRoute
          appendCallMemory with
        ⟨body, lookup, appendCursor, appendRoute, appendMemory⟩
      simp [runtime, aux, appendTargetSlot] at lookup
      cases lookup
      exact appendTarget_pauseCut appendCursor compiled targetAt
        appendRoute appendMemory
  · exact (zeroErrorCursor.noSstore_of_entrySstoreFree compiled
      [pausableZeroErrorSlot] rfl
      (Exec.Deriv.SourceCursor.Toward.chronology
        zeroErrorRoute).cursorToTarget targetAt).elim

private theorem pauseExpiryFinishTarget
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path pauseExpiryFinish)
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
          finalPath.functionIndex = path.functionIndex := by
  unfold pauseExpiryFinish storeHeartbeatExpiryFromStack at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropLineExact route
      (line := [Ninst.dup 0] ++ mstoreAt 0 ++
        [Ninst.caller] ++ tagTop expiryRegion) (by
        intro instruction member
        simp only [mstoreAt, tagTop, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at member
        rcases member with (head | rfl) | rfl | rfl
        rcases head with rfl | rfl | rfl
        all_goals intro h; cases h) with
    ⟨storeCursor, storeRoute⟩
  cases storeRoute with
  | atTarget finalCursor chronology site siteEq sourceMember targetEq instructionEq =>
      exact ⟨_, _, storeCursor, targetEq,
        by simpa [siteEq] using sourceMember, rfl⟩
  | next storeCursor chronology tailCursor edge tailRoute =>
      exact (tailCursor.noSstore_of_entrySstoreFree compiled [] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology
          tailRoute).cursorToTarget targetAt).elim

private theorem checkedPauseExpiryFinishTarget
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (checkedHeartbeatExpiry pauseExpiryFinish))
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
          finalPath.functionIndex = path.functionIndex := by
  unfold checkedHeartbeatExpiry at cursor
  let checkedLine : Line :=
    [Ninst.timestamp, Ninst.pushB256 heartbeatIntervalSlot,
      Ninst.sload, Ninst.add, Ninst.dup 0, Ninst.timestamp,
      Ninst.swap 0, Ninst.lt]
  rcases Exec.Deriv.SourceCursor.Toward.dropLineExact route
      (line := checkedLine) (by
        intro instruction member
        simp only [checkedLine, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          intro h <;> cases h) with
    ⟨branchCursor, branchRoute⟩
  cases branchRoute with
  | branchRight branchCursor chronology errorCursor compilerPrefix errorRoute =>
      exact (errorCursor.noSstore_of_entrySstoreFree compiled
        [arithmeticPanicSlot] (by
          simp [Prog.entrySstoreFree, Prog.componentSstoreFree,
            Prog.function?, runtime, aux, arithmeticPanicSlot,
            Func.revertData, Func.localSstoreFree, Func.callsIn]
          decide +kernel)
        (Exec.Deriv.SourceCursor.Toward.chronology
          errorRoute).cursorToTarget targetAt).elim
  | branchLeft branchCursor chronology bodyCursor compilerPrefix bodyRoute =>
      simpa using pauseExpiryFinishTarget bodyCursor compiled targetAt bodyRoute

private theorem pauseSuccessTarget
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path pauseSuccess)
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
          finalPath.functionIndex = path.functionIndex := by
  unfold pauseSuccess at cursor
  let pausePrefix : Line :=
    loadWord durationWord ++ mstoreAt 0 ++
      [Ninst.caller] ++ loadWord targetWord ++
      [Ninst.pushB256 pauseTriggeredEvent] ++ logWith 2 0 1 ++
      [Ninst.caller] ++ tagTop countRegion ++ [Ninst.sload, Ninst.iszero]
  rcases Exec.Deriv.SourceCursor.Toward.dropLineExact route
      (line := pausePrefix) (by
        intro instruction member
        simp [pausePrefix, loadWord, mstoreAt, logWith, tagTop,
          Ninst.pushB256] at member
        rcases member with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          intro h <;> cases h) with
    ⟨branchCursor, branchRoute⟩
  cases branchRoute with
  | branchLeft branchCursor chronology checkedCursor compilerPrefix checkedRoute =>
      rcases checkedPauseExpiryFinishTarget (initial := initial) checkedCursor
          compiled targetAt checkedRoute with
        ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
          functionIndex⟩
      exact ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
        functionIndex⟩
  | branchRight branchCursor chronology zeroCursor compilerPrefix zeroRoute =>
      rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne zeroRoute
          (by intro h; cases h) with
        ⟨pushChronology, finishCursor, pushEdge, finishRoute⟩
      rcases pauseExpiryFinishTarget (initial := initial) finishCursor
          compiled targetAt finishRoute with
        ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
          functionIndex⟩
      exact ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
        functionIndex⟩

private theorem pauseAfterSetTarget
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp)
      ⟨pauseAfterSetSlot, []⟩ pauseAfterSet)
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
          finalPath.functionIndex = pauseAfterSetSlot := by
  unfold pauseAfterSet at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropLineExact route
      (line := loadWord targetWord ++
        [Ninst.dup 0, Ninst.extcodesize, Ninst.iszero])
      (by simp [loadWord, Ninst.pushB256]) with
    ⟨codeBranchCursor, codeBranchRoute⟩
  cases codeBranchRoute with
  | branchRight branchCursor chronology errorCursor compilerPrefix errorRoute =>
      exact (errorCursor.noSstore_of_entrySstoreFree compiled
        [emptyRevertSlot] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology
          errorRoute).cursorToTarget targetAt).elim
  | branchLeft branchCursor chronology callCursor compilerPrefix callRoute =>
      let callLine : Line :=
        [Ninst.pop, Ninst.pushB256 pauseForSelector] ++ mstoreAt 8 ++
          loadWord durationWord ++ mstoreAt 9 ++
          pushList [0, 0, 36, 0x11c, 0] ++ loadWord targetWord ++
          [Ninst.gas, Ninst.call, Ninst.iszero]
      rcases Exec.Deriv.SourceCursor.Toward.dropLineExact callRoute
          (line := callLine) (by
            intro instruction member
            simp [callLine, mstoreAt, loadWord, pushList,
              Ninst.pushB256] at member
            rcases member with
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl | rfl <;>
              intro h <;> cases h) with
        ⟨callBranchCursor, callBranchRoute⟩
      cases callBranchRoute with
      | branchRight branchCursor chronology errorCursor compilerPrefix errorRoute =>
          exact (errorCursor.noSstore_of_entrySstoreFree compiled
            [bubbleRevertSlot] rfl
            (Exec.Deriv.SourceCursor.Toward.chronology
              errorRoute).cursorToTarget targetAt).elim
      | branchLeft branchCursor chronology staticCursor compilerPrefix staticRoute =>
          let staticLine : Line :=
            [Ninst.pushB256 isPausedSelector] ++ mstoreAt 8 ++
              pushList [32, 0, 4, 0x11c] ++ loadWord targetWord ++
              [Ninst.gas, Ninst.staticcall, Ninst.iszero]
          rcases Exec.Deriv.SourceCursor.Toward.dropLineExact staticRoute
              (line := staticLine) (by
                intro instruction member
                simp [staticLine, mstoreAt, loadWord, pushList,
                  Ninst.pushB256] at member
                rcases member with
                    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                  intro h <;> cases h) with
            ⟨staticBranchCursor, staticBranchRoute⟩
          cases staticBranchRoute with
          | branchRight branchCursor chronology errorCursor compilerPrefix errorRoute =>
              exact (errorCursor.noSstore_of_entrySstoreFree compiled
                [bubbleRevertSlot] rfl
                (Exec.Deriv.SourceCursor.Toward.chronology
                  errorRoute).cursorToTarget targetAt).elim
          | branchLeft branchCursor chronology decodeCursor compilerPrefix decodeRoute =>
              unfold decodePausedResult at decodeCursor
              rcases Exec.Deriv.SourceCursor.Toward.dropLineExact decodeRoute
                  (line := returnDataShorterThan 32)
                  (by simp [returnDataShorterThan, Ninst.pushB256]) with
                ⟨lengthBranchCursor, lengthBranchRoute⟩
              cases lengthBranchRoute with
              | branchRight branchCursor chronology errorCursor compilerPrefix errorRoute =>
                  exact (errorCursor.noSstore_of_entrySstoreFree compiled
                    [emptyRevertSlot] rfl
                    (Exec.Deriv.SourceCursor.Toward.chronology
                      errorRoute).cursorToTarget targetAt).elim
              | branchLeft branchCursor chronology valueCursor compilerPrefix valueRoute =>
                  rcases Exec.Deriv.SourceCursor.Toward.dropLineExact valueRoute
                      (line := loadWord 0 ++ [Ninst.dup 0, Ninst.iszero])
                      (by simp [loadWord, Ninst.pushB256]) with
                    ⟨valueBranchCursor, valueBranchRoute⟩
                  cases valueBranchRoute with
                  | branchRight branchCursor chronology errorCursor compilerPrefix errorRoute =>
                      exact (errorCursor.noSstore_of_entrySstoreFree compiled
                        [pauseFailedErrorSlot] rfl
                        (Exec.Deriv.SourceCursor.Toward.chronology
                          errorRoute).cursorToTarget targetAt).elim
                  | branchLeft branchCursor chronology eqCursor compilerPrefix eqRoute =>
                      rcases Exec.Deriv.SourceCursor.Toward.dropLineExact eqRoute
                          (line := [Ninst.pushB256 1, Ninst.eq])
                          (by simp [Ninst.pushB256]) with
                        ⟨eqBranchCursor, eqBranchRoute⟩
                      cases eqBranchRoute with
                      | branchLeft branchCursor chronology errorCursor compilerPrefix errorRoute =>
                          exact (errorCursor.noSstore_of_entrySstoreFree compiled
                            [emptyRevertSlot] rfl
                            (Exec.Deriv.SourceCursor.Toward.chronology
                              errorRoute).cursorToTarget targetAt).elim
                      | branchRight branchCursor chronology successCursor compilerPrefix successRoute =>
                          rcases pauseSuccessTarget successCursor compiled
                              targetAt successRoute with
                            ⟨finalPath, finalTail, finalCursor, targetEq,
                              sourceMember, functionIndex⟩
                          exact ⟨finalPath, finalTail, finalCursor, targetEq,
                            sourceMember, by
                              simpa [pauseAfterSetSlot] using functionIndex⟩
private theorem Exec.Deriv.SourceCursor.Toward.storePrefixTarget
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {line : Line} {tail : Func}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (line +++ .next (.reg .sstore) tail))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (lineNe : ∀ instruction ∈ line,
      instruction ≠ (.reg .sstore))
    (freeSlots : List Nat)
    (tailFree : (runtime dp).entrySstoreFree tail freeSlots = true) :
    ∃ finalPath finalTail,
      ∃ finalCursor : Exec.Deriv.SourceCursor root (runtime dp)
          finalPath (.next (.reg .sstore) finalTail),
        finalCursor.node = target ∧
          ({ path := finalPath, pc := finalCursor.pc,
              instruction := (.reg .sstore) } : Prog.SourceSite) ∈
            (runtime dp).sourceSites ∧
          finalPath.functionIndex = path.functionIndex := by
  rcases Exec.Deriv.SourceCursor.Toward.dropLineExact route lineNe with
    ⟨storeCursor, storeRoute⟩
  cases storeRoute with
  | atTarget finalCursor chronology site siteEq sourceMember targetEq instructionEq =>
      exact ⟨_, _, storeCursor, targetEq,
        by simpa [siteEq] using sourceMember, rfl⟩
  | next storeCursor chronology tailCursor edge tailRoute =>
      exact (tailCursor.noSstore_of_entrySstoreFree compiled freeSlots tailFree
        (Exec.Deriv.SourceCursor.Toward.chronology
          tailRoute).cursorToTarget targetAt).elim

private theorem checkedRegisterExpiryTarget
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (pauserWord : B256) (tail : Func)
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (checkedHeartbeatExpiry <|
        Ninst.dup 0 ::: mstoreAt 0 +++
          loadWord pauserWord +++ tagTop expiryRegion +++
            Ninst.sstore ::: tail))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (tailFree : (runtime dp).entrySstoreFree tail [] = true) :
    ∃ finalPath finalTail,
      ∃ finalCursor : Exec.Deriv.SourceCursor root (runtime dp)
          finalPath (.next (.reg .sstore) finalTail),
        finalCursor.node = target ∧
          ({ path := finalPath, pc := finalCursor.pc,
              instruction := (.reg .sstore) } : Prog.SourceSite) ∈
            (runtime dp).sourceSites ∧
          finalPath.functionIndex = path.functionIndex := by
  unfold checkedHeartbeatExpiry at cursor
  let checkedLine : Line :=
    [Ninst.timestamp, Ninst.pushB256 heartbeatIntervalSlot,
      Ninst.sload, Ninst.add, Ninst.dup 0, Ninst.timestamp,
      Ninst.swap 0, Ninst.lt]
  rcases Exec.Deriv.SourceCursor.Toward.dropLineExact route
      (line := checkedLine) (by
        intro instruction member
        simp only [checkedLine, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          intro h <;> cases h) with
    ⟨branchCursor, branchRoute⟩
  cases branchRoute with
  | branchRight branchCursor chronology errorCursor compilerPrefix errorRoute =>
      exact (errorCursor.noSstore_of_entrySstoreFree compiled
        [arithmeticPanicSlot] (by
          simp [Prog.entrySstoreFree, Prog.componentSstoreFree,
            Prog.function?, runtime, aux, arithmeticPanicSlot,
            Func.revertData, Func.localSstoreFree, Func.callsIn]
          decide +kernel)
        (Exec.Deriv.SourceCursor.Toward.chronology
          errorRoute).cursorToTarget targetAt).elim
  | branchLeft branchCursor chronology bodyCursor compilerPrefix bodyRoute =>
      rcases Exec.Deriv.SourceCursor.Toward.storePrefixTarget
          (initial := initial)
          (line := [Ninst.dup 0] ++ mstoreAt 0 ++
            loadWord pauserWord ++ tagTop expiryRegion)
          (tail := tail) bodyCursor compiled targetAt bodyRoute (by
        intro instruction member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false, mstoreAt, loadWord, tagTop] at member
        rcases member with
            ((rfl | rfl | rfl) | rfl | rfl) | rfl | rfl <;>
          intro h <;> cases h) [] tailFree with
        ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
          functionIndex⟩
      exact ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
        by simpa using functionIndex⟩

private theorem registerNewExpiryTarget
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (loadWord newPauserWord +++ Ninst.iszero :::
        (Func.stop <?>
          (checkedHeartbeatExpiry <|
            Ninst.dup 0 ::: mstoreAt 0 +++
              loadWord newPauserWord +++ tagTop expiryRegion +++
                Ninst.sstore :::
                  loadWord newPauserWord +++
                    Ninst.pushB256 heartbeatUpdatedEvent :::
                      logWith 1 0 1 +++ Func.stop))))
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
          finalPath.functionIndex = path.functionIndex := by
  rcases Exec.Deriv.SourceCursor.Toward.dropLineExact route
      (line := loadWord newPauserWord ++ [Ninst.iszero]) (by
        intro instruction member
        simp only [loadWord, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at member
        rcases member with (rfl | rfl) | rfl <;>
          intro h <;> cases h) with
    ⟨branchCursor, branchRoute⟩
  cases branchRoute with
  | branchRight branchCursor chronology stopCursor compilerPrefix stopRoute =>
      exact (stopCursor.noSstore_of_entrySstoreFree compiled [] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology
          stopRoute).cursorToTarget targetAt).elim
  | branchLeft branchCursor chronology expiryCursor compilerPrefix expiryRoute =>
      rcases checkedRegisterExpiryTarget newPauserWord
          (loadWord newPauserWord +++
            Ninst.pushB256 heartbeatUpdatedEvent :::
              logWith 1 0 1 +++ Func.stop)
          expiryCursor compiled targetAt expiryRoute (by
            rfl) with
        ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
          functionIndex⟩
      exact ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
        by simpa using functionIndex⟩

private theorem registerAfterSetTarget
    {dp : DeployParams} {root target : Exec.Deriv}
    {initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp)
      ⟨registerAfterSetSlot, []⟩ registerAfterSet)
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
          finalPath.functionIndex = registerAfterSetSlot := by
  unfold registerAfterSet at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropLineExact route
      (line := loadWord previousPauserWord ++ [Ninst.iszero]) (by
        intro instruction member
        simp only [loadWord, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at member
        rcases member with (rfl | rfl) | rfl <;>
          intro h <;> cases h) with
    ⟨previousBranchCursor, previousBranchRoute⟩
  cases previousBranchRoute with
  | branchRight branchCursor chronology freshCursor compilerPrefix freshRoute =>
      rcases registerNewExpiryTarget freshCursor compiled targetAt freshRoute with
        ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
          functionIndex⟩
      exact ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
        by simpa using functionIndex⟩
  | branchLeft branchCursor chronology retainedCursor compilerPrefix retainedRoute =>
      rcases Exec.Deriv.SourceCursor.Toward.dropLineExact retainedRoute
          (line := previousCountKey ++ [Ninst.sload, Ninst.iszero]) (by
            intro instruction member instructionEq
            subst instruction
            simp [previousCountKey, loadWord, tagTop,
              Ninst.pushB256] at member) with
        ⟨countBranchCursor, countBranchRoute⟩
      cases countBranchRoute with
      | branchLeft branchCursor chronology liveOldCursor compilerPrefix liveOldRoute =>
          rcases registerNewExpiryTarget liveOldCursor compiled targetAt
              liveOldRoute with
            ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
              functionIndex⟩
          exact ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
            by simpa using functionIndex⟩
      | branchRight branchCursor chronology clearOldCursor compilerPrefix clearOldRoute =>
          let clearPrefix : Line :=
            [Ninst.pushB256 0] ++ loadWord previousPauserWord ++
              tagTop expiryRegion
          rcases Exec.Deriv.SourceCursor.Toward.dropLineExact clearOldRoute
              (line := clearPrefix) (by
                intro instruction member instructionEq
                subst instruction
                simp [clearPrefix, loadWord, tagTop,
                  Ninst.pushB256] at member) with
            ⟨clearStoreCursor, clearStoreRoute⟩
          cases clearStoreRoute with
          | atTarget finalCursor chronology site siteEq sourceMember targetEq instructionEq =>
              exact ⟨_, _, clearStoreCursor, targetEq,
                by simpa [siteEq] using sourceMember, rfl⟩
          | next storeCursor chronology afterClearCursor edge afterClearRoute =>
              let clearEventPrefix : Line :=
                [Ninst.pushB256 0] ++ mstoreAt 0 ++
                  loadWord previousPauserWord ++
                    [Ninst.pushB256 heartbeatUpdatedEvent] ++
                      logWith 1 0 1
              rcases Exec.Deriv.SourceCursor.Toward.dropLineExact
                  afterClearRoute (line := clearEventPrefix) (by
                    intro instruction member instructionEq
                    subst instruction
                    simp [clearEventPrefix, mstoreAt, loadWord, logWith,
                      Ninst.pushB256] at member) with
                ⟨newBranchCursor, newBranchRoute⟩
              rcases registerNewExpiryTarget newBranchCursor compiled targetAt
                  newBranchRoute with
                ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
                  functionIndex⟩
              exact ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
                by simpa using functionIndex⟩

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
      initial write (.reg .sstore) bodyCursor)
    (writeSite : ∃ site ∈ runtimePersistentSourceSites dp,
      site.pc = write.pc ∧ site.path.functionIndex = 0) :
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
        countNe liveLt writeSite
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
      have writeSite : ∃ writeSite ∈ runtimePersistentSourceSites dp,
          writeSite.pc = write.pc ∧ writeSite.path.functionIndex = 0 :=
        ⟨site, RuntimePersistentWrite.sourceSite?_mem found, sitePc, by
          rcases rowEq with rfl | rfl <;>
            exact RuntimePersistentWrite.sourceSite?_functionIndex found⟩
      refine ⟨.adminConfiguration, ?_,
        .setPauseDuration endpoint guard callerEq writeSite⟩
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
      have writeSite : ∃ writeSite ∈ runtimePersistentSourceSites dp,
          writeSite.pc = write.pc ∧ writeSite.path.functionIndex = 0 :=
        ⟨site, RuntimePersistentWrite.sourceSite?_mem found, sitePc, by
          rcases rowEq with rfl | rfl <;>
            exact RuntimePersistentWrite.sourceSite?_functionIndex found⟩
      refine ⟨.adminConfiguration, ?_,
        .setHeartbeatInterval endpoint guard callerEq writeSite⟩
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
          (entryStorage.trans mainStorage) compiled targetAt route
          ⟨site, RuntimePersistentWrite.sourceSite?_mem found, sitePc,
            RuntimePersistentWrite.sourceSite?_functionIndex found⟩⟩

private theorem runtimeDispatchCut_registerPauserAuthority
    {dp : DeployParams} {frameRoot write : Exec.Deriv}
    (mainCursor : Exec.Deriv.SourceCursor frameRoot (runtime dp)
      ⟨0, []⟩ (runtimeMain dp))
    (frameToMain : Exec.Deriv.ParentPrefix frameRoot mainCursor.node)
    (compiled : some frameRoot.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At write.sevm.code write.pc (.reg .sstore))
    (row : RuntimePersistentWrite) (site : Prog.SourceSite)
    (found : row.sourceSite? dp = some site)
    (sitePc : site.pc = write.pc)
    {path : Prog.SourcePath}
    (cursor : Exec.Deriv.SourceCursor frameRoot (runtime dp) path
      (registerPauser dp))
    (route : Exec.Deriv.SourceCursor.Toward
      mainCursor write (.reg .sstore) cursor) :
    ∃ role : InvocationRole,
      role ∈ row.permittedRoles ∧
        RuntimeWriteAuthority dp frameRoot write role := by
  let endpoint := RuntimeEndpointOccurrence.ofCursor
    frameToMain cursor route
  rcases registerPauserBodyGuard rfl cursor compiled targetAt route with
    ⟨guardPath, guardTail, guardCursor, branchCursor,
      guardChronology, guardEdge, guardRun, branchRoute, callerEq⟩
  let guard := RuntimeGuardOccurrence.ofCursor frameToMain
    guardChronology guardEdge guardRun targetAt (by intro h; cases h)
  have registerCut := registerPauser_registerCut cursor compiled targetAt route
  cases registerCut with
  | registry finalCursor targetEq sourceMember functionIndex =>
      have exactFunction :=
        RuntimePersistentWrite.sourceFunctionIndex_of_terminal
          finalCursor found sitePc targetEq sourceMember
      have permitted : InvocationRole.adminRegistry ∈ row.permittedRoles :=
        RuntimePersistentWrite.adminRegistry_mem_of_functionIndex (by
          rw [exactFunction]
          exact functionIndex)
      exact ⟨.adminRegistry, permitted,
        .adminRegistry endpoint guard callerEq
          ⟨site, RuntimePersistentWrite.sourceSite?_mem found, sitePc, by
            rw [RuntimePersistentWrite.sourceSite?_functionIndex found,
              exactFunction]
            exact functionIndex⟩⟩
  | registerAfterSet afterCursor afterRoute =>
      rcases registerAfterSetTarget afterCursor compiled targetAt afterRoute with
        ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
          functionIndex⟩
      have exactFunction :=
        RuntimePersistentWrite.sourceFunctionIndex_of_terminal
          finalCursor found sitePc targetEq sourceMember
      have permitted : InvocationRole.adminExpiry ∈ row.permittedRoles :=
        RuntimePersistentWrite.adminExpiry_mem_of_functionIndex
          (exactFunction.trans functionIndex)
      exact ⟨.adminExpiry, permitted,
        .adminExpiry endpoint guard callerEq
          ⟨site, RuntimePersistentWrite.sourceSite?_mem found, sitePc,
            (RuntimePersistentWrite.sourceSite?_functionIndex found).trans
              (exactFunction.trans functionIndex)⟩⟩

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
    {path : Prog.SourcePath}
    {initial : Exec.Deriv.SourceCursor frameRoot (runtime dp)
      ⟨0, []⟩ (runtimeMain dp)}
    (bodyCursor : Exec.Deriv.SourceCursor frameRoot (runtime dp) path pause)
    (frameToInitial : Exec.Deriv.ParentPrefix frameRoot initial.node)
    (bodyStorage :
      Devm.getStor bodyCursor.pre = Devm.getStor frameRoot.devm)
    (compiled : some frameRoot.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At write.sevm.code write.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial write (.reg .sstore) bodyCursor) :
    PauseAuthorityEvidence dp frameRoot write ∧
      PauseKernelCut (target := write) initial := by
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
        let evidence : PauseAuthorityEvidence dp frameRoot write :=
          .intro endpoint assignedOccurrence liveOccurrence
            assignedAtEntry liveAtEntry
        let setupBeforeNew : Line :=
          [Ninst.pushB256 pauseDurationSlot, Ninst.sload] ++
            mstoreAt durationWord ++ arg 0 ++ mstoreAt targetWord
        rcases Exec.Deriv.SourceCursor.Toward.dropLineRun successRoute
            (line := setupBeforeNew) (by
              intro instruction member
              simp [setupBeforeNew, mstoreAt, arg, cdl,
                Ninst.pushB256] at member
              rcases member with
                  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                intro h <;> cases h) with
          ⟨newPushPath, newPushCursor, setupPrefixRun,
            newPushChronology, newPushRoute⟩
        rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
            newPushRoute (by intro h; cases h) with
          ⟨newPushChronology, newStoreCursor, newPushEdge, newStoreRoute⟩
        have newPrefix : [(0 : B256)] <<+ newStoreCursor.pre.stack := by
          simpa [Ninst.pushB256] using prefix_of_push
            (of_run_pushB256
              (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
                newPushCursor newPushEdge)) nil_pref
        rcases Exec.Deriv.SourceCursor.Toward.dropLineRun newStoreRoute
            (line := mstoreAt newPauserWord) (by
              intro instruction member
              simp only [mstoreAt, List.mem_cons, List.not_mem_nil,
                or_false] at member
              rcases member with rfl | rfl <;> intro h <;> cases h) with
          ⟨previousPushPath, previousPushCursor, newStoreRun,
            previousPushChronology, previousPushRoute⟩
        rcases of_run_mstoreAt_val newStoreRun newPrefix with
          ⟨newStack, newMemoryEq⟩
        have newCarrier : ScratchWord newPauserWord 0
            previousPushCursor.pre.memory := by
          rw [newMemoryEq]
          exact ScratchWord.of_write newPauserWord 0 _
        rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
            previousPushRoute (by intro h; cases h) with
          ⟨previousPushChronology, previousStoreCursor, previousPushEdge,
            previousStoreRoute⟩
        have previousPrefix : [(0 : B256)] <<+
            previousStoreCursor.pre.stack := by
          simpa [Ninst.pushB256] using prefix_of_push
            (of_run_pushB256
              (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
                previousPushCursor previousPushEdge)) nil_pref
        have newAtPreviousStore : ScratchWord newPauserWord 0
            previousStoreCursor.pre.memory := by
          rw [← (of_run_pushB256
            (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
              previousPushCursor previousPushEdge)).memory]
          exact newCarrier
        rcases Exec.Deriv.SourceCursor.Toward.dropLineRun previousStoreRoute
            (line := mstoreAt previousPauserWord) (by
              intro instruction member
              simp only [mstoreAt, List.mem_cons, List.not_mem_nil,
                or_false] at member
              rcases member with rfl | rfl <;> intro h <;> cases h) with
          ⟨continuationPushPath, continuationPushCursor, previousStoreRun,
            continuationPushChronology, continuationPushRoute⟩
        have newAfterPrevious : ScratchWord newPauserWord 0
            continuationPushCursor.pre.memory :=
          ScratchWord.of_run_mstoreAtAfter (word := previousPauserWord)
            newAtPreviousStore (by decide +kernel) previousStoreRun
        rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
            continuationPushRoute (by intro h; cases h) with
          ⟨continuationPushChronology, continuationStoreCursor,
            continuationPushEdge, continuationStoreRoute⟩
        have continuationPrefix : [(1 : B256)] <<+
            continuationStoreCursor.pre.stack := by
          simpa [Ninst.pushB256] using prefix_of_push
            (of_run_pushB256
              (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
                continuationPushCursor continuationPushEdge)) nil_pref
        have newAtContinuationStore : ScratchWord newPauserWord 0
            continuationStoreCursor.pre.memory := by
          rw [← (of_run_pushB256
            (Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
              continuationPushCursor continuationPushEdge)).memory]
          exact newAfterPrevious
        rcases Exec.Deriv.SourceCursor.Toward.dropLineRun continuationStoreRoute
            (line := mstoreAt continuationWord) (by
              intro instruction member
              simp only [mstoreAt, List.mem_cons, List.not_mem_nil,
                or_false] at member
              rcases member with rfl | rfl <;> intro h <;> cases h) with
          ⟨callPath, callCursor, continuationStoreRun,
            callChronology, callRoute⟩
        rcases of_run_mstoreAt_val continuationStoreRun continuationPrefix with
          ⟨continuationStack, continuationMemoryEq⟩
        have pauseMemory : PauseKernelMemory callCursor.pre.memory := by
          rw [continuationMemoryEq]
          exact ⟨newAtContinuationStore.writeAfter
              (scratchOffset continuationWord) (by decide +kernel) 1,
            ScratchWord.of_write continuationWord 1 _⟩
        rcases Exec.Deriv.SourceCursor.Toward.callBodyPauseMemory
            callCursor compiled targetAt callRoute pauseMemory with
          ⟨body, lookup, kernelCursor, kernelRoute, kernelMemory⟩
        simp [runtime, aux, setPauserSlot] at lookup
        cases lookup
        exact ⟨evidence,
          setPauserKernel_pauseCut kernelCursor compiled targetAt
            kernelRoute kernelMemory⟩

private theorem runtimeDispatchCut_pauseAuthority
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
    {path : Prog.SourcePath}
    (cursor : Exec.Deriv.SourceCursor frameRoot (runtime dp) path pause)
    (route : Exec.Deriv.SourceCursor.Toward
      mainCursor write (.reg .sstore) cursor)
    (entryStorage : Devm.getStor cursor.pre = Devm.getStor mainCursor.pre) :
    ∃ role : InvocationRole,
      role ∈ row.permittedRoles ∧
        RuntimeWriteAuthority dp frameRoot write role := by
  rcases pauseBodyAuthorityEvidence cursor frameToMain
      (entryStorage.trans mainStorage) compiled targetAt route with
    ⟨evidence, kernelCut⟩
  cases evidence with
  | intro endpoint assignedGuard liveGuard assigned live =>
      cases kernelCut with
      | registry finalCursor targetEq sourceMember functionIndex =>
          have exactFunction :=
            RuntimePersistentWrite.sourceFunctionIndex_of_terminal
              finalCursor found sitePc targetEq sourceMember
          have permitted :
              InvocationRole.pauseRegistry ∈ row.permittedRoles :=
            RuntimePersistentWrite.pauseRegistry_mem_of_functionIndex (by
              rw [exactFunction]
              exact functionIndex)
          exact ⟨.pauseRegistry, permitted,
            .pauseRegistry endpoint assignedGuard liveGuard assigned live
              ⟨site, RuntimePersistentWrite.sourceSite?_mem found, sitePc, by
                rw [RuntimePersistentWrite.sourceSite?_functionIndex found,
                  exactFunction]
                exact functionIndex⟩⟩
      | pauseAfterSet afterCursor afterRoute =>
          rcases pauseAfterSetTarget afterCursor compiled targetAt afterRoute with
            ⟨finalPath, finalTail, finalCursor, targetEq, sourceMember,
              functionIndex⟩
          have exactFunction :=
            RuntimePersistentWrite.sourceFunctionIndex_of_terminal
              finalCursor found sitePc targetEq sourceMember
          have permitted : InvocationRole.pauseExpiry ∈ row.permittedRoles :=
            RuntimePersistentWrite.pauseExpiry_mem_of_functionIndex
              (exactFunction.trans functionIndex)
          exact ⟨.pauseExpiry, permitted,
            .pauseExpiry endpoint assignedGuard liveGuard assigned live
              ⟨site, RuntimePersistentWrite.sourceSite?_mem found, sitePc,
                (RuntimePersistentWrite.sourceSite?_functionIndex found).trans
                  (exactFunction.trans functionIndex)⟩⟩

/-- The concrete runtime entry JUMPDEST is storage-silent.  This retains that
entry fact alongside the target-directed main cursor used by the authority
classifier. -/
private theorem runtimeMainTowardStorage
    {dp : DeployParams} {ca : Adr} {root target : Exec.Deriv}
    (invocation : root.exactInvocation (runtime dp) ca ca)
    (reached : Exec.Deriv.ParentPrefix root target)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    ∃ cursor : Exec.Deriv.SourceCursor root (runtime dp)
        ⟨0, []⟩ (runtimeMain dp),
      Exec.Deriv.ParentPrefix root cursor.node ∧
        Devm.getStor cursor.pre = Devm.getStor root.devm ∧
          Exec.Deriv.SourceCursor.Toward
            cursor target (.reg .sstore) cursor := by
  rcases root with ⟨pc, sevm, pre, out, run⟩
  rcases invocation with ⟨pcEq, targetEq, addressEq, compiled⟩
  dsimp at pcEq targetEq addressEq compiled reached targetAt
  subst pc
  have mainLookup :
      (table 0 ((runtime dp).main :: (runtime dp).aux))[0]? =
        some (0, (runtime dp).main) := rfl
  rcases subcode_of_get?_eq_some compiled mainLookup with
    ⟨jumpdestAt, sourceSlice⟩
  have sourceBoundary : noPushBefore sevm.code 1 32 = true :=
    (Prog.jumpable_of_get?_table compiled mainLookup).2
  cases reached with
  | refl =>
      exact (targetAt.false_of_jinstAt jumpdestAt).elim
  | step edge rest =>
      cases edge with
      | cont step next =>
          have static :
              Evm.step ⟨0, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨0, sevm, pre⟩ .jumpdest) :=
            Evm.step_jump jumpdestAt
          have jumpdestRun :
              Jinst.Run ⟨0, sevm, pre⟩ .jumpdest (.ok ⟨_, _⟩) :=
            Step.ofJump_cont (static.symm.trans step)
          rcases of_jumpdest_run jumpdestRun with ⟨nextPcEq, burn⟩
          cases nextPcEq
          let nextNode : Exec.Deriv := ⟨1, sevm, _, out, next⟩
          let parentEdge : Exec.Deriv.ParentStep nextNode
              ⟨0, sevm, pre, out, .cont step next⟩ :=
            .cont step next
          have parentPrefix : Exec.Deriv.ParentPrefix
              ⟨0, sevm, pre, out, .cont step next⟩ nextNode :=
            .step parentEdge (.refl _)
          let cursor : Exec.Deriv.SourceCursor
              ⟨0, sevm, pre, out, .cont step next⟩ (runtime dp)
              ⟨0, []⟩ (runtimeMain dp) :=
            ⟨1, _, next, parentPrefix, sourceSlice, sourceBoundary, by
              intro site member
              simp only [Prog.sourceSites, List.mem_flatMap]
              refine ⟨0, by simp, ?_⟩
              rw [mainLookup]
              change site ∈ Func.sourceSites 0 [] 1 (runtimeMain dp)
              exact member⟩
          have storage :
              Devm.getStor cursor.pre = Devm.getStor pre := by
            exact (Burn.Inv.inv burn).symm
          have route := cursor.toward compiled rest (by trivial) targetAt
          exact ⟨cursor, parentPrefix, storage, route⟩
      | doneOk step enter resume next =>
          have static :
              Evm.step ⟨0, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨0, sevm, pre⟩ .jumpdest) :=
            Evm.step_jump jumpdestAt
          exact (Step.ofJump_ne_spawn (static.symm.trans step)).elim
      | runOk step enter child resume next =>
          have static :
              Evm.step ⟨0, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨0, sevm, pre⟩ .jumpdest) :=
            Evm.step_jump jumpdestAt
          exact (Step.ofJump_ne_spawn (static.symm.trans step)).elim

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

/-- Every same-frame runtime SSTORE in an exact selected raw invocation has
one exact source row and one of that row's actual runtime authority roles.
The enclosing invocation may have any terminal outcome. -/
theorem Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot
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
      (∀ candidate : RuntimePersistentWrite,
        candidate.sourceSite? dp = some site → candidate = row) ∧
      ∃ role : InvocationRole,
        role ∈ row.permittedRoles ∧
          RuntimeWriteAuthority dp frameRoot occurrence.node role := by
  rcases Exec.NinstOccurrence.runtimePersistentWrite_of_rawFrameRoot
      occurrence instructionEq selected invocation sameFrame with
    ⟨row, site, rowMember, found, classified, sitePc,
      siteInstruction, unique⟩
  have targetAt : Ninst.At occurrence.node.sevm.code occurrence.node.pc
      (.reg .sstore) := by
    rw [← instructionEq]
    exact occurrence.decoded
  rcases runtimeMainTowardStorage invocation sameFrame targetAt with
    ⟨mainCursor, frameToMain, mainStorage, mainRoute⟩
  have cut := runtimeMain_writeEndpointCut mainCursor invocation.2.2.2
    targetAt mainRoute
  have authority : ∃ role : InvocationRole,
      role ∈ row.permittedRoles ∧
        RuntimeWriteAuthority dp frameRoot occurrence.node role := by
    cases cut with
    | setPauseDuration cursor route entryStorage =>
        exact runtimeDispatchCut_configurationOrHeartbeatAuthority
          mainCursor frameToMain mainStorage invocation.2.2.2 targetAt
          row site found sitePc
          (.setPauseDuration cursor route entryStorage)
          (.setPauseDuration cursor route entryStorage)
    | setHeartbeatInterval cursor route entryStorage =>
        exact runtimeDispatchCut_configurationOrHeartbeatAuthority
          mainCursor frameToMain mainStorage invocation.2.2.2 targetAt
          row site found sitePc
          (.setHeartbeatInterval cursor route entryStorage)
          (.setHeartbeatInterval cursor route entryStorage)
    | registerPauser cursor route entryStorage =>
        exact runtimeDispatchCut_registerPauserAuthority
          mainCursor frameToMain invocation.2.2.2 targetAt
          row site found sitePc cursor route
    | heartbeat cursor route entryStorage =>
        exact runtimeDispatchCut_configurationOrHeartbeatAuthority
          mainCursor frameToMain mainStorage invocation.2.2.2 targetAt
          row site found sitePc
          (.heartbeat cursor route entryStorage)
          (.heartbeat cursor route entryStorage)
    | pause cursor route entryStorage =>
        exact runtimeDispatchCut_pauseAuthority
          mainCursor frameToMain mainStorage invocation.2.2.2 targetAt
          row site found sitePc cursor route entryStorage
  exact ⟨row, site, rowMember, found, classified, sitePc,
    siteInstruction, unique, authority⟩

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
