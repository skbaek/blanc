import Blanc.Semantics

/-!
Contract-neutral committed-execution and complete frame-settlement traversal.
Child retention is decided by full frame settlement, including CREATE code
deposit, rather than raw execution success.
-/

namespace Blanc

open Jaune

/-- Whether an execution outcome commits its frame state. -/
def Execution.commits : Execution → Bool
  | .error _ => false
  | .ok post => post.error.isNone

/-- Whether the child world survives the complete message-frame settlement.
For CREATE this is strictly stronger than raw execution success: code-deposit
failure rolls the constructor world back before the parent resumes. -/
def Frame.settlementCommits (frame : Frame) (raw : Execution) : Bool :=
  match frame.settle raw with
  | .error _ => false
  | .ok post => post.error.isNone

private theorem execution_commits_of_handleError_clean
    {raw : Execution} {post : Devm}
    (hresult : executeCode.handleError raw = .ok post)
    (hclean : post.error.isNone = true) :
    Execution.commits raw = true := by
  cases raw with
  | ok rawPost =>
      simp only [executeCode.handleError, Except.ok.injEq] at hresult
      subst post
      exact hclean
  | error error =>
      rcases error with ⟨error, rawPost⟩
      cases error <;>
        simp [executeCode.handleError, Devm.withError,
          Devm.setMeta] at hresult
      all_goals subst post
      all_goals change (some _).isNone = true at hclean
      all_goals simp at hclean

private theorem processMessage_clean_input
    {msg : Msg}
    {input : Except (EvmError × State × AdrSet × Tra) Devm}
    {post : Devm}
    (hresult : processMessage.settle msg input = .ok post)
    (hclean : post.error.isNone = true) :
    ∃ pre : Devm, input = .ok pre ∧ pre.error.isNone = true := by
  cases input with
  | error error =>
      simp [processMessage.settle, Bind.bind, Except.bind] at hresult
  | ok pre =>
      cases herror : pre.error with
      | none => exact ⟨pre, rfl, by simp [herror]⟩
      | some error =>
          simp [processMessage.settle, Bind.bind, Except.bind, herror] at hresult
          rw [← hresult] at hclean
          change pre.error.isNone = true at hclean
          rw [herror] at hclean
          simp at hclean

private theorem processCreateMessage_clean_input
    {msg : Msg}
    {input : Except (EvmError × State × AdrSet × Tra) Devm}
    {post : Devm}
    (hresult : processCreateMessage.settle msg input = .ok post)
    (hclean : post.error.isNone = true) :
    ∃ pre : Devm, input = .ok pre ∧ pre.error.isNone = true := by
  cases input with
  | error error =>
      simp [processCreateMessage.settle, Bind.bind, Except.bind] at hresult
  | ok pre =>
      cases herror : pre.error with
      | none => exact ⟨pre, rfl, by simp [herror]⟩
      | some error =>
          simp [processCreateMessage.settle, Bind.bind, Except.bind, herror] at hresult
          rw [← hresult] at hclean
          change pre.error.isNone = true at hclean
          rw [herror] at hclean
          simp at hclean

/-- Complete frame settlement can be clean only when the underlying code
execution itself was clean. -/
theorem Frame.raw_commits_of_settlementCommits
    {frame : Frame} {raw : Execution}
    (h : Blanc.Frame.settlementCommits frame raw = true) :
    Execution.commits raw = true := by
  unfold Frame.settlementCommits at h
  cases hsettled : frame.settle raw with
  | error error => simp [hsettled] at h
  | ok settled =>
      have hclean : settled.error.isNone = true := by
        simpa only [hsettled] using h
      unfold Frame.settle Frame.settleMsg at hsettled
      cases hcreate : frame.isCreate with
      | false =>
          simp only [hcreate, Bool.false_eq_true, ↓reduceIte] at hsettled
          rcases processMessage_clean_input hsettled hclean with
            ⟨handled, hhandled, hhandledClean⟩
          exact execution_commits_of_handleError_clean hhandled hhandledClean
      | true =>
          simp only [hcreate, ↓reduceIte] at hsettled
          rcases processCreateMessage_clean_input hsettled hclean with
            ⟨inner, hinner, hinnerClean⟩
          rcases processMessage_clean_input hinner hinnerClean with
            ⟨handled, hhandled, hhandledClean⟩
          exact execution_commits_of_handleError_clean hhandled hhandledClean

/-- The concrete outcome indexed by an `Exec` derivation. -/
def Exec.outcome {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (_ : Exec pc sevm pre out) : Execution := out

/-- A retained successful execution frame.  Keeping the full derivation makes
the history suitable for later provenance refinements, rather than merely
retaining a precomputed numeric tally. -/
structure Exec.Frame where
  pc : Nat
  sevm : Sevm
  pre : Devm
  out : Execution
  run : Exec pc sevm pre out
  committed : Execution.commits out = true

/-- The committed post-machine indexed by a retained frame. -/
def Execution.committedPost (out : Execution)
    (h : Execution.commits out = true) : Devm :=
  match out with
  | .ok post => post
  | .error _ => by simp [Execution.commits] at h

def Exec.Frame.post (frame : Exec.Frame) : Devm :=
  Execution.committedPost frame.out frame.committed

def Exec.Frame.ofRun {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true) : Exec.Frame :=
  ⟨pc, sevm, pre, out, run, committed⟩

/-- Successful descendant frames whose effects survive in the enclosing
successful frame.  Failed children are discarded, while successful children
are traversed to arbitrary depth. -/
def Exec.descendantFrames {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : List Exec.Frame :=
  match run with
  | .halt _ => []
  | .cont _ next => Exec.descendantFrames next
  | .doneErr _ _ _ => []
  | .doneOk _ _ _ next => Exec.descendantFrames next
  | .runErr _ _ _ _ => []
  | .runOk (f := frame) (raw := raw) _ _ child _ next =>
      let childFrames :=
        if h : Blanc.Frame.settlementCommits frame raw = true then
          let hraw : Execution.commits raw = true :=
            Blanc.Frame.raw_commits_of_settlementCommits h
          Exec.Frame.ofRun child hraw :: Exec.descendantFrames child
        else []
      childFrames ++ Exec.descendantFrames next
termination_by sizeOf run

/-- A successful spawn retains its settlement-committing child before the
child's descendants and before the parent continuation's descendants. -/
@[simp] theorem Exec.descendantFrames_runOk_of_settlementCommits
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {f : Jaune.Frame} {rsm : Resume}
    {cevm : Evm} {raw out : Execution}
    (hstep : Jaune.Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .ok devm')
    (next : Exec pc' sevm devm' out)
    (hcommit : Frame.settlementCommits f raw = true) :
    Exec.descendantFrames (Exec.runOk hstep henter child hr next) =
      Exec.Frame.ofRun child
          (Frame.raw_commits_of_settlementCommits hcommit) ::
        Exec.descendantFrames child ++ Exec.descendantFrames next := by
  simp [Exec.descendantFrames, hcommit]

/-- A spawned child whose complete frame settlement does not commit contributes
no retained frame, even if its raw execution itself committed. -/
@[simp] theorem Exec.descendantFrames_runOk_of_not_settlementCommits
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {f : Jaune.Frame} {rsm : Resume}
    {cevm : Evm} {raw out : Execution}
    (hstep : Jaune.Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .ok devm')
    (next : Exec pc' sevm devm' out)
    (hnot : Blanc.Frame.settlementCommits f raw ≠ true) :
    Exec.descendantFrames (Exec.runOk hstep henter child hr next) =
      Exec.descendantFrames next := by
  simp only [Exec.descendantFrames, dif_neg hnot, List.nil_append]

/-- In particular, a CREATE child whose raw execution commits but whose
code-deposit settlement rolls back contributes no descendant frame.  The raw
commit premise records the semantic counterexample to pruning by raw outcome
alone. -/
theorem Exec.descendantFrames_runOk_create_codeDepositRollback
    {pc pc' : Nat} {sevm : Sevm} {pre devm' settled : Devm}
    {f : Jaune.Frame} {rsm : Resume}
    {cevm : Evm} {raw out : Execution}
    (hstep : Jaune.Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .ok devm')
    (next : Exec pc' sevm devm' out)
    (_rawCommits : Execution.commits raw = true)
    (hcreate : f.isCreate = true)
    (hsettled : processCreateMessage.settle f.outer
      (processMessage.settle f.inner (executeCode.handleError raw)) =
        .ok settled)
    (herror : settled.error.isSome = true) :
    Exec.descendantFrames (Exec.runOk hstep henter child hr next) =
      Exec.descendantFrames next := by
  apply Exec.descendantFrames_runOk_of_not_settlementCommits
    hstep henter child hr next
  intro hcommit
  have hframeSettle : f.settle raw = .ok settled := by
    unfold Frame.settle Frame.settleMsg
    simpa only [hcreate, ↓reduceIte] using hsettled
  unfold Blanc.Frame.settlementCommits at hcommit
  rw [hframeSettle] at hcommit
  cases hoption : settled.error with
  | none => simp [hoption] at herror
  | some error => simp [hoption] at hcommit

/-- All and only committed frames in a successful root execution.  An errored
root contributes no frames, so a later enclosing rollback cannot leak actions
into the accounting fold. -/
def Exec.committedFrames {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : List Exec.Frame :=
  if h : Execution.commits out = true then
    Exec.Frame.ofRun run h :: Exec.descendantFrames run
  else []

/-- A noncommitting root contributes no retained frame, regardless of any
locally successful descendants in its derivation. -/
@[simp] theorem Exec.committedFrames_eq_nil_of_not_commits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (h : Execution.commits out ≠ true) :
    Exec.committedFrames run = [] := by
  simp [Exec.committedFrames, h]

theorem ProcessMessage.settlementCommits_of_some_ok_clean
    {msg : Msg} {pc : Nat} {sevm : Sevm} {pre child : Devm}
    {raw : Execution}
    (hprocess : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, raw⟩) (.ok child))
    (hclean : child.error.isSome = false) :
    Frame.settlementCommits (Frame.ofCall msg) raw = true := by
  have hsettle := (RunFrame.some_inv hprocess).2
  have hclean' : child.error.isNone = true := by
    cases herror : child.error <;> simp_all
  unfold Frame.settlementCommits
  rw [← hsettle]
  exact hclean'

theorem Frame.settlementCommits_ofCall_of_raw_commits
    {msg : Msg} {raw : Execution}
    (hraw : Execution.commits raw = true) :
    Frame.settlementCommits (Frame.ofCall msg) raw = true := by
  cases raw with
  | error err =>
      simp [Execution.commits] at hraw
  | ok post =>
      cases herror : post.error with
      | none =>
          simp [Frame.settlementCommits, Frame.settle, Frame.settleMsg,
            Frame.ofCall, executeCode.handleError,
            processMessage.settle, Bind.bind, Except.bind, herror]
      | some error =>
          simp [Execution.commits, herror] at hraw

end Blanc
