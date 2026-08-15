import Blanc.LidoCircuitBreakerSites

/-!
Arbitrary-outcome runtime authority for Lido CircuitBreaker.

This module starts at canonical raw frame traversal.  Its structural theorem
does not assume that a store succeeds, commits, changes a cell, or survives
message settlement; guard and invocation-role refinements build on this exact
same-instance source cut.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

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
