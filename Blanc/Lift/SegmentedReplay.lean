import Blanc.Lift.CommittedLogs

/-!
Exact contiguous regrouping of the existing state chronology.  A chunk retains
its original nonempty boundary list; it is neither an execution relation nor a
replacement provenance carrier.  Semantic cut admissibility remains separate.
-/

namespace Blanc

open Jaune

abbrev ReplayChunk (Origin : Type) :=
  StateTransition (List (StateTransition Origin))

/-- Exact flattening, nonempty chunks, and each chunk's actual continuous replay. -/
def ExactChunks {Origin : Type}
    (raw : List (StateTransition Origin))
    (chunks : List (ReplayChunk Origin)) : Prop :=
  chunks.flatMap (fun chunk => chunk.origin) = raw ∧
    ∀ chunk ∈ chunks, chunk.origin ≠ [] ∧
      StateReplay chunk.before chunk.origin chunk.after

private theorem StateReplay.post_unique
    {Origin : Type} {pre pre' post post' : State}
    {events : List (StateTransition Origin)}
    (left : StateReplay pre events post)
    (right : StateReplay pre' events post')
    (empty : events = [] → pre = pre') : post = post' := by
  induction left generalizing pre' with
  | nil => cases right; exact empty rfl
  | cons event rest ih =>
      cases right with
      | cons _ rightRest => exact ih rightRest (fun _ => rfl)

private theorem StateReplay.nonempty_endpoints
    {Origin : Type} {pre post pre' post' : State}
    {events : List (StateTransition Origin)}
    (left : StateReplay pre events post)
    (right : StateReplay pre' events post') (nonempty : events ≠ []) :
    pre = pre' ∧ post = post' := by
  cases left with
  | nil => exact (nonempty rfl).elim
  | cons event rest =>
      cases right with
      | cons _ rightRest => exact ⟨rfl, rest.post_unique rightRest (fun _ => rfl)⟩

private theorem StateReplay.split_append
    {Origin : Type} {pre post : State}
    (left right : List (StateTransition Origin))
    (replay : StateReplay pre (left ++ right) post) :
    ∃ middle, StateReplay pre left middle ∧ StateReplay middle right post := by
  induction left generalizing pre with
  | nil => exact ⟨pre, .nil pre, replay⟩
  | cons event tail ih =>
      cases replay with
      | cons _ rest =>
          obtain ⟨middle, headReplay, tailReplay⟩ := ih rest
          exact ⟨middle, .cons event headReplay, tailReplay⟩

/-- The actual raw replay fixes every chunk cut; no endpoint premise is added. -/
theorem StateReplay.rechunk
    {Origin : Type} {pre post : State}
    {raw : List (StateTransition Origin)} {chunks : List (ReplayChunk Origin)}
    (rawReplay : StateReplay pre raw post)
    (exactChunks : ExactChunks raw chunks) : StateReplay pre chunks post := by
  rcases exactChunks with ⟨flatten, pieces⟩
  subst raw
  induction chunks generalizing pre with
  | nil => cases rawReplay; exact .nil _
  | cons chunk tail ih =>
      obtain ⟨middle, headReplay, tailReplay⟩ :=
        StateReplay.split_append chunk.origin
          (tail.flatMap (fun piece => piece.origin)) rawReplay
      obtain ⟨nonempty, chunkReplay⟩ := pieces chunk (List.mem_cons_self)
      obtain ⟨beforeEq, afterEq⟩ := headReplay.nonempty_endpoints chunkReplay nonempty
      subst pre
      subst middle
      exact .cons chunk (ih
        (fun piece member => pieces piece (List.mem_cons_of_mem chunk member)) tailReplay)

/-- A local relation/observation fold along actual boundaries.  Prefixes stay
explicit so a consumer may retain suspended locals and exact source cuts. -/
private theorem StateReplay.simulateFrom
    {Origin Q Step O : Type}
    (R : Q → List Step → Q → Prop)
    (nil : ∀ q, R q [] q)
    (append : ∀ {a b c xs ys}, R a xs b → R b ys c → R a (xs ++ ys) c)
    (obs : List Step → List O) (obs_nil : obs [] = [])
    (obs_append : ∀ xs ys, obs (xs ++ ys) = obs xs ++ obs ys)
    (actual : StateTransition Origin → List O)
    (all : List (StateTransition Origin))
    (Link : List (StateTransition Origin) → State → Q → Prop)
    (localStep : ∀ prior event suffix,
      all = prior ++ event :: suffix → ∀ q, Link prior event.before q →
      ∃ q' steps, R q steps q' ∧ Link (prior ++ [event]) event.after q' ∧
        obs steps = actual event)
    {pre post : State} {events : List (StateTransition Origin)}
    (replay : StateReplay pre events post)
    (prior : List (StateTransition Origin)) (aligned : all = prior ++ events)
    {q : Q} (opening : Link prior pre q) :
    ∃ q' steps, R q steps q' ∧ Link all post q' ∧
      obs steps = events.flatMap actual := by
  induction replay generalizing prior q with
  | nil state =>
      rw [List.append_nil] at aligned
      subst all
      exact ⟨q, [], nil q, opening, obs_nil⟩
  | @cons tail post event rest ih =>
      obtain ⟨middle, headSteps, headRun, cut, headObs⟩ :=
        localStep prior event _ aligned q opening
      have nextAligned : all = (prior ++ [event]) ++ tail := by
        simpa only [List.append_assoc, List.singleton_append] using aligned
      obtain ⟨final, tailSteps, tailRun, ending, tailObs⟩ :=
        ih (prior ++ [event]) nextAligned cut
      exact ⟨final, headSteps ++ tailSteps, append headRun tailRun, ending,
        (obs_append headSteps tailSteps).trans
          (congrArg₂ List.append headObs tailObs)⟩

/-- Simulate each exact local chunk and preserve chronological observations.
The local premise is one step from the incoming cut relation, not a claimed
whole-frame endpoint. -/
theorem StateReplay.simulateChunks
    {Origin Q Step O : Type}
    (R : Q → List Step → Q → Prop)
    (nil : ∀ q, R q [] q)
    (append : ∀ {a b c xs ys}, R a xs b → R b ys c → R a (xs ++ ys) c)
    (obs : List Step → List O) (obs_nil : obs [] = [])
    (obs_append : ∀ xs ys, obs (xs ++ ys) = obs xs ++ obs ys)
    (actual : StateTransition Origin → List O)
    {pre post : State} {raw : List (StateTransition Origin)}
    {chunks : List (ReplayChunk Origin)}
    (rawReplay : StateReplay pre raw post) (exactChunks : ExactChunks raw chunks)
    (Link : List (ReplayChunk Origin) → State → Q → Prop)
    {q₀ : Q} (opening : Link [] pre q₀)
    (localStep : ∀ prior chunk suffix,
      chunks = prior ++ chunk :: suffix → ∀ q, Link prior chunk.before q →
      ∃ q' steps, R q steps q' ∧ Link (prior ++ [chunk]) chunk.after q' ∧
        obs steps = chunk.origin.flatMap actual) :
    ∃ q' steps, R q₀ steps q' ∧ Link chunks post q' ∧
      obs steps = raw.flatMap actual := by
  obtain ⟨q', steps, run, ending, observed⟩ :=
    (rawReplay.rechunk exactChunks).simulateFrom R nil append obs obs_nil obs_append
      (fun chunk => chunk.origin.flatMap actual) chunks Link localStep [] rfl opening
  refine ⟨q', steps, run, ending, ?_⟩
  rw [← exactChunks.1]
  simpa only [List.flatMap_assoc] using observed

/-- An own boundary is a nonexternal instruction or the terminal instruction.
The decoded instruction is inspected even when an external step immediately
fails or completes without interpreted child code. -/
def Exec.StateBoundary.isOwn (boundary : Exec.StateBoundary) : Prop :=
  (boundary.origin.kind = .instruction ∨ boundary.origin.kind = .terminal) ∧
    ∀ executable, Evm.getInst
      ⟨boundary.origin.driver.pc, boundary.origin.driver.sevm,
        boundary.origin.driver.pre⟩ ≠ .some (.next (.exec executable))

/-- An admissible own chunk stays at one original frame path, crosses no
external instruction or child seam, and permits terminal only at the end.
Every non-own boundary occupies its own seam chunk. -/
def Exec.AdmissibleChunk (chunk : ReplayChunk Exec.StateBoundaryOrigin) : Prop :=
  (∃ before last, chunk.origin = before ++ [last] ∧
    (∀ boundary ∈ before, boundary.origin.framePath = last.origin.framePath ∧
      boundary.origin.kind = .instruction ∧ Exec.StateBoundary.isOwn boundary) ∧ Exec.StateBoundary.isOwn last) ∨
  (∃ boundary, chunk.origin = [boundary] ∧ ¬ Exec.StateBoundary.isOwn boundary)

/-- Semantic cut obligation in addition to exact flattening and continuity. -/
def Exec.AdmissibleCuts (chunks : List (ReplayChunk Exec.StateBoundaryOrigin)) : Prop :=
  ∀ chunk ∈ chunks, Exec.AdmissibleChunk chunk

/-- Local chunk simulation on the actual settlement-pruned execution stream.
The semantic cut certificate is supplied to each local producer; it cannot
hide an external instruction or a child subtree in a whole-frame chunk. -/
theorem Exec.simulateCommittedChunks
    {Q Step O : Type}
    (R : Q → List Step → Q → Prop)
    (nil : ∀ q, R q [] q)
    (append : ∀ {a b c xs ys}, R a xs b → R b ys c → R a (xs ++ ys) c)
    (obs : List Step → List O) (obs_nil : obs [] = [])
    (obs_append : ∀ xs ys, obs (xs ++ ys) = obs xs ++ obs ys)
    (actual : Exec.StateBoundary → List O)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    {chunks : List (ReplayChunk Exec.StateBoundaryOrigin)}
    (exactChunks : ExactChunks (Exec.committedStateBoundaries run) chunks)
    (admissible : Exec.AdmissibleCuts chunks)
    (Link : List (ReplayChunk Exec.StateBoundaryOrigin) → State → Q → Prop)
    {q₀ : Q} (opening : Link [] pre.state q₀)
    (localStep : ∀ prior chunk suffix,
      chunks = prior ++ chunk :: suffix → Exec.AdmissibleChunk chunk →
      ∀ q, Link prior chunk.before q →
      ∃ q' steps, R q steps q' ∧ Link (prior ++ [chunk]) chunk.after q' ∧
        obs steps = chunk.origin.flatMap actual) :
    ∃ q' steps, R q₀ steps q' ∧
      Link chunks (Execution.committedPost out committed).state q' ∧
      obs steps = (Exec.committedStateBoundaries run).flatMap actual := by
  apply (Exec.committedStateReplay run committed).simulateChunks
    R nil append obs obs_nil obs_append actual exactChunks Link opening
  intro prior chunk suffix aligned q cut
  have member : chunk ∈ chunks := by
    rw [aligned]
    exact List.mem_append_right prior List.mem_cons_self
  exact localStep prior chunk suffix aligned (admissible chunk member) q cut

/-- A local producer whose observations are the actual successful LOGs yields
both exact chronological observations and the concrete committed endpoint logs. -/
theorem Exec.simulateCommittedLogChunks
    {Q Step : Type}
    (R : Q → List Step → Q → Prop)
    (nil : ∀ q, R q [] q)
    (append : ∀ {a b c xs ys}, R a xs b → R b ys c → R a (xs ++ ys) c)
    (obs : List Step → List Log) (obs_nil : obs [] = [])
    (obs_append : ∀ xs ys, obs (xs ++ ys) = obs xs ++ obs ys)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (fork : CoveredFork sevm.benvStat.fork)
    {chunks : List (ReplayChunk Exec.StateBoundaryOrigin)}
    (exactChunks : ExactChunks (Exec.committedStateBoundaries run) chunks)
    (admissible : Exec.AdmissibleCuts chunks)
    (Link : List (ReplayChunk Exec.StateBoundaryOrigin) → State → Q → Prop)
    {q₀ : Q} (opening : Link [] pre.state q₀)
    (localStep : ∀ prior chunk suffix,
      chunks = prior ++ chunk :: suffix → Exec.AdmissibleChunk chunk →
      ∀ q, Link prior chunk.before q →
      ∃ q' steps, R q steps q' ∧ Link (prior ++ [chunk]) chunk.after q' ∧
        obs steps = chunk.origin.flatMap Exec.boundaryOwnLogs) :
    ∃ q' steps, R q₀ steps q' ∧
      Link chunks (Execution.committedPost out committed).state q' ∧
      obs steps = (Exec.committedStateBoundaries run).flatMap Exec.boundaryOwnLogs ∧
      (Execution.committedPost out committed).logs = pre.logs ++ obs steps := by
  obtain ⟨q', steps, model, ending, logs⟩ :=
    Exec.simulateCommittedChunks R nil append obs obs_nil obs_append
      Exec.boundaryOwnLogs run committed exactChunks admissible Link opening localStep
  refine ⟨q', steps, model, ending, logs, ?_⟩
  rw [logs]
  exact Exec.committed_logs run committed fork

end Blanc
