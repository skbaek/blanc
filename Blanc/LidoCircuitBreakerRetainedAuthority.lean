import Blanc.LidoCircuitBreakerAuthority
import Blanc.LidoCircuitBreakerOwnerClosure

/-!
Settlement-retained authority for the exact Lido CircuitBreaker runtime.

This leaf composes the contract-local owner-closure theorem, the generic
retained-last-writer theorem, and arbitrary-outcome runtime authority.  Raw
occurrence classification remains in `LidoCircuitBreakerAuthority`; this file
only narrows a changed committed owner cell to its last surviving writer.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-- Every settlement-retained descendant frame was also an actually entered
raw frame.  This contract-local copy keeps the generic occurrence substrate
unchanged. -/
private theorem Exec.mem_rawFrameDescendants_of_mem_descendantFrames :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
      (run : Exec pc sevm pre out) (frame : Exec.Frame),
      frame ∈ Exec.descendantFrames run →
        frame.rootDeriv ∈ Exec.rawFrameDescendants run := by
  intro pc sevm pre out run
  induction run with
  | halt hstep => simp [Exec.descendantFrames, Exec.rawFrameDescendants]
  | cont hstep next ih =>
      simpa [Exec.descendantFrames, Exec.rawFrameDescendants] using ih
  | doneErr hstep henter hresume =>
      simp [Exec.descendantFrames, Exec.rawFrameDescendants]
  | doneOk hstep henter hresume next ih =>
      simpa [Exec.descendantFrames, Exec.rawFrameDescendants] using ih
  | runErr hstep henter child hresume =>
      simp [Exec.descendantFrames, Exec.rawFrameDescendants]
  | runOk hstep henter child hresume next childIh nextIh =>
      intro frame member
      simp only [Exec.descendantFrames, Exec.rawFrameDescendants] at member ⊢
      split at member
      next childSettles =>
        simp only [List.mem_append, List.mem_cons] at member ⊢
        rcases member with (rfl | childMember) | nextMember
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (childIh _ childMember))
        · exact Or.inr (Or.inr (nextIh _ nextMember))
      next childDoesNotSettle =>
        simp only [List.nil_append] at member
        simp only [List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (nextIh _ member))

/-- A committed frame root is a member of the all-outcome raw-frame
traversal. -/
private theorem Exec.mem_rawFrameRoots_of_mem_committedFrames
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (frame : Exec.Frame)
    (member : frame ∈ Exec.committedFrames run) :
    frame.rootDeriv ∈ Exec.rawFrameRoots run := by
  unfold Exec.committedFrames at member
  split at member
  next committed =>
    simp only [List.mem_cons] at member
    rcases member with rfl | descendant
    · exact Exec.mem_rawFrameRoots_self run
    · simp only [Exec.rawFrameRoots, List.mem_cons]
      exact Or.inr
        (Exec.mem_rawFrameDescendants_of_mem_descendantFrames
          run frame descendant)
  next notCommitted => simp at member

/-- Complete retained authority for one changed CircuitBreaker-owned cell.
The selected successful SSTORE is the exact last retained write of `final` to
`key`; its committed exact-runtime frame and AT4/AT5 classification are kept
in the same witness. -/
inductive Exec.RuntimeOwnerCellAuthority
    (dp : DeployParams) (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (key final : B256) : Prop where
  | intro
      (write : Exec.SuccessfulSstoreOccurrence
        (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv))
      (retained : write.Retained)
      (owner_eq : write.storageOwner = ca)
      (key_eq : write.key = key)
      (final_value : write.value = final)
      (lastRetained : write.IsLastRetained)
      (frame : Exec.Frame)
      (frameCommitted : frame ∈ Exec.committedFrames run)
      (frameRaw : frame.rootDeriv ∈ Exec.rawFrameRoots run)
      (frameInvocation :
        frame.rootDeriv.exactInvocation (runtime dp) ca ca)
      (sameFrame :
        Exec.Deriv.ParentPrefix frame.rootDeriv write.occurrence.node)
      (row : RuntimePersistentWrite)
      (site : Prog.SourceSite)
      (row_mem : row ∈ RuntimePersistentWrite.all)
      (sourceSite : row.sourceSite? dp = some site)
      (classified :
        classifyRuntimePersistentWrite dp site.path site.pc = some row)
      (site_pc : site.pc = write.occurrence.node.pc)
      (site_instruction : site.instruction = .reg .sstore)
      (unique : ∀ candidate : RuntimePersistentWrite,
        candidate.sourceSite? dp = some site → candidate = row)
      (role : InvocationRole)
      (role_permitted : role ∈ row.permittedRoles)
      (authority : RuntimeWriteAuthority dp frame.rootDeriv
        write.occurrence.node role) :
      Exec.RuntimeOwnerCellAuthority dp ca run key final

/-- Every changed CircuitBreaker-owned word at the committed raw endpoint has
an exact retained last writer in an installed exact Lido runtime frame, with
its unique source row and actual preceding runtime authority. -/
theorem Exec.runtimeOwnerCellAuthority_of_committedPost_ne
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (installed : Prog.At (runtime dp) ca pc sevm pre)
    (rootExact :
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv).exactInvocation
        (runtime dp) ca ca)
    (committed : Execution.commits out = true)
    {key : B256}
    (changed :
      (Devm.getStor pre ca).get key ≠
        (Devm.getStor (Execution.committedPost out committed) ca).get key) :
    Exec.RuntimeOwnerCellAuthority dp ca run key
      ((Devm.getStor (Execution.committedPost out committed) ca).get key) := by
  rcases Exec.exists_lastRetainedSstore_of_getStor_ne
      run committed changed with
    ⟨write, retained, owner, keyEq, valueEq, last⟩
  rcases Exec.retainedSstore_runtimeOwnerClosure
      run committed installed rootExact write retained owner with
    ⟨frame, frameCommitted, frameInvocation, sameFrame⟩
  have frameRaw : frame.rootDeriv ∈ Exec.rawFrameRoots run :=
    Exec.mem_rawFrameRoots_of_mem_committedFrames
      run frame frameCommitted
  rcases Blanc.LidoCircuitBreaker.Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot
      write.occurrence
      write.instruction_eq frameRaw frameInvocation sameFrame with
    ⟨row, site, rowMem, sourceSite, classified, sitePc,
      siteInstruction, unique, role, rolePermitted, authority⟩
  exact .intro write retained owner keyEq valueEq last frame
    frameCommitted frameRaw frameInvocation sameFrame row site rowMem
    sourceSite classified sitePc siteInstruction unique role rolePermitted
    authority

/-- The body state entered by an exact `ProcessMessage` has the same persistent
storage as the message-entry world.  Value transfer may change balances but
not storage. -/
private theorem ProcessMessage.bodyStorage_eq_entry
    {msg : Msg} {settled : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (process : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok settled)) :
    Devm.getStor pre = msg.benv.state.getStor := by
  have enter : (Frame.ofCall msg).enter = .run ⟨pc, sevm, pre⟩ :=
    (RunFrame.some_inv process).1
  rcases Frame.enter_run_inv enter with ⟨benv, transfer, evmEq⟩
  have preState : pre.state = benv.state :=
    congrArg (fun evm : Evm => evm.dyna.state) evmEq
  funext owner
  change pre.state.getStor owner = msg.benv.state.getStor owner
  rw [preState, benvAfterTransfer_getStor_eq transfer]
  rfl

/-- A clean direct message transfers committed-post retained authority to the
settled owner cell.  Commitment and both endpoint equalities are derived from
the concrete message execution rather than supplied for the selected writer. -/
theorem ProcessMessage.runtimeOwnerCellAuthority_of_clean_settled_ne
    {dp : DeployParams} {ca : Adr} {msg : Msg} {settled : Devm}
    {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out)
    (installed : Prog.At (runtime dp) ca 0 sevm pre)
    (rootExact :
      (⟨0, sevm, pre, out, run⟩ : Exec.Deriv).exactInvocation
        (runtime dp) ca ca)
    (process : ProcessMessage msg
      (.some ⟨⟨0, sevm, pre⟩, out⟩) (.ok settled))
    (clean : settled.error.isSome = false)
    {key : B256}
    (changed :
      (msg.benv.state.getStor ca).get key ≠
        (Devm.getStor settled ca).get key) :
    Exec.RuntimeOwnerCellAuthority dp ca run key
      ((Devm.getStor settled ca).get key) := by
  have settles :=
    ProcessMessage.settlementCommits_of_some_ok_clean process clean
  have committed : Execution.commits out = true :=
    Frame.raw_commits_of_settlementCommits settles
  have entryStorage := ProcessMessage.bodyStorage_eq_entry process
  have settledStorage :=
    ProcessMessage.runtimeOwnerStorage_eq_committedPost
      run rootExact process committed
  have changedRaw :
      (Devm.getStor pre ca).get key ≠
        (Devm.getStor (Execution.committedPost out committed) ca).get key := by
    intro equal
    apply changed
    calc
      (msg.benv.state.getStor ca).get key =
          (Devm.getStor pre ca).get key :=
        (congrArg (fun storage => (storage ca).get key) entryStorage).symm
      _ = (Devm.getStor (Execution.committedPost out committed) ca).get key :=
        equal
      _ = (Devm.getStor settled ca).get key :=
        (congrArg (fun storage => storage.get key) settledStorage).symm
  have authority := Exec.runtimeOwnerCellAuthority_of_committedPost_ne
    run installed rootExact committed changedRaw
  have finalEq :
      (Devm.getStor (Execution.committedPost out committed) ca).get key =
        (Devm.getStor settled ca).get key :=
    (congrArg (fun storage => storage.get key) settledStorage).symm
  rw [finalEq] at authority
  exact authority

/-- Any settled error of an exact direct Lido-runtime message restores the
complete CircuitBreaker owner storage and transient storage from message
entry.  Raw execution occurrences and raw logs are intentionally not erased. -/
theorem ProcessMessage.runtime_settled_error_restores_owner
    (dp : DeployParams) {msg : Msg} {slot : Xlot} {post : Devm}
    {ca : Adr}
    (_target : msg.target = some ca)
    (_owner : msg.currentTarget = ca)
    (_codeAddress : msg.codeAddress = some ca)
    (_code : msg.code.toList = lidoCircuitBreakerCode dp)
    (process : ProcessMessage msg slot (.ok post))
    (error : post.error.isSome) :
    Devm.getStor post ca = msg.benv.state.getStor ca ∧
      post.transientStorage = msg.tenv.transientStorage := by
  have rollback := ProcessMessage.rollback_of_error process error
  exact ⟨congrArg (fun state : State => state.getStor ca) rollback.1,
    rollback.2⟩

/-- A noncommitting raw root has no committed frame. -/
theorem Exec.no_committedFrame_of_not_commits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (notCommitted : Execution.commits out ≠ true)
    (frame : Exec.Frame) :
    frame ∉ Exec.committedFrames run := by
  rw [Exec.committedFrames_eq_nil_of_not_commits run notCommitted]
  simp

/-- A noncommitting raw root retains no successful SSTORE, including no write
owned by the CircuitBreaker account. -/
theorem Exec.no_retainedOwnerSstore_of_not_commits
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (notCommitted : Execution.commits out ≠ true) :
    ¬ ∃ write : Exec.SuccessfulSstoreOccurrence
        (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
      write.Retained ∧ write.storageOwner = ca := by
  rintro ⟨write, retained, owner⟩
  unfold Exec.SuccessfulSstoreOccurrence.Retained
    Exec.NinstOccurrence.Retained at retained
  rw [Exec.retainedNodes_eq_nil_of_not_commits run notCommitted] at retained
  simp at retained

/-- Consequently a noncommitting root cannot carry the retained-authority
witness: it has neither a committed exact frame nor a retained last writer. -/
theorem Exec.no_runtimeOwnerCellAuthority_of_not_commits
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (notCommitted : Execution.commits out ≠ true)
    (key final : B256) :
    ¬ Exec.RuntimeOwnerCellAuthority dp ca run key final := by
  intro authority
  cases authority with
  | intro write retained owner keyEq finalValue last frame frameCommitted
      frameRaw frameInvocation sameFrame row site rowMem sourceSite classified
      sitePc siteInstruction unique role rolePermitted roleAuthority =>
      exact Exec.no_committedFrame_of_not_commits
        run notCommitted frame frameCommitted

end Blanc.LidoCircuitBreaker
