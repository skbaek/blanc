import Blanc.Lift.SegmentedReplay
import Blanc.ExecutionHistoryStateTrace

/-!
A local segmented consumer of the existing configured-history chronology.
The original wrappers, selected fork witnesses and state boundaries stay in
that chronology; raw frame boundaries are exposed only for cut admissibility.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

private def MessageStateBoundaryOrigin.execution? :
    MessageStateBoundaryOrigin → Option Exec.StateBoundaryOrigin
  | .wrapper .. => none
  | .execution _ origin => some origin

private def SystemMessageStateBoundaryOrigin.execution? :
    SystemMessageStateBoundaryOrigin → Option Exec.StateBoundaryOrigin
  | .preparation .. => none
  | .message _ origin => MessageStateBoundaryOrigin.execution? origin

private def TransactionStateBoundaryOrigin.execution? :
    TransactionStateBoundaryOrigin → Option Exec.StateBoundaryOrigin
  | .message _ origin => MessageStateBoundaryOrigin.execution? origin
  | _ => none

private def RequestsStateBoundaryOrigin.execution? :
    RequestsStateBoundaryOrigin → Option Exec.StateBoundaryOrigin
  | .withdrawal _ origin => SystemMessageStateBoundaryOrigin.execution? origin
  | .consolidation _ origin => SystemMessageStateBoundaryOrigin.execution? origin

private def AppliedBodyStateBoundaryOrigin.execution? :
    AppliedBodyStateBoundaryOrigin → Option Exec.StateBoundaryOrigin
  | .beacon _ origin => SystemMessageStateBoundaryOrigin.execution? origin
  | .history _ origin => SystemMessageStateBoundaryOrigin.execution? origin
  | .transaction _ origin => TransactionStateBoundaryOrigin.execution? origin
  | .withdrawal .. => none
  | .request _ origin => RequestsStateBoundaryOrigin.execution? origin

private def ConfiguredBlockStateBoundary.execution?
    (boundary : ConfiguredBlockStateBoundary) : Option Exec.StateBoundary :=
  let origin := match boundary.origin with
    | .preparation .. => none
    | .body _ origin => AppliedBodyStateBoundaryOrigin.execution? origin
  origin.map (fun raw =>
    { origin := raw, before := boundary.before, after := boundary.after })

/-- Every raw member retains the exact corresponding wrapper boundary.  A raw
chunk may contain no wrapper seam; nonexecution wrappers are singleton cuts. -/
def ConfiguredAdmissibleChunk
    (chunk : ReplayChunk ConfiguredBlockStateBoundaryOrigin) : Prop :=
  (∃ raw, List.Forall₂
      (fun boundary event => ConfiguredBlockStateBoundary.execution? boundary = some event)
      chunk.origin raw ∧
      Exec.AdmissibleChunk { origin := raw, before := chunk.before, after := chunk.after }) ∨
  (∃ boundary, chunk.origin = [boundary] ∧
    ConfiguredBlockStateBoundary.execution? boundary = none)

private def ConfiguredBlockStateBoundary.canPrepend
    (boundary : ConfiguredBlockStateBoundary)
    (chunk : ReplayChunk ConfiguredBlockStateBoundaryOrigin) : Prop :=
  ∃ event raw,
    ConfiguredBlockStateBoundary.execution? boundary = some event ∧
    List.Forall₂
      (fun boundary event => ConfiguredBlockStateBoundary.execution? boundary = some event)
      chunk.origin raw ∧ Exec.canPrepend event
        {origin := raw, before := chunk.before, after := chunk.after}

private theorem configured_singleton_admissible (boundary : ConfiguredBlockStateBoundary) :
    ConfiguredAdmissibleChunk
      {origin := [boundary], before := boundary.before, after := boundary.after} := by
  cases decoded : ConfiguredBlockStateBoundary.execution? boundary with
  | none => exact Or.inr ⟨boundary, rfl, decoded⟩
  | some event =>
      exact Or.inl ⟨[event], .cons decoded .nil, Exec.singleton_admissible event⟩

private theorem configured_prepend_admissible
    (boundary : ConfiguredBlockStateBoundary)
    (chunk : ReplayChunk ConfiguredBlockStateBoundaryOrigin)
    (can : ConfiguredBlockStateBoundary.canPrepend boundary chunk)
    (admissible : ConfiguredAdmissibleChunk chunk) :
    ConfiguredAdmissibleChunk
      {origin := boundary :: chunk.origin, before := boundary.before, after := chunk.after} := by
  obtain ⟨event, raw, decoded, mapped, own⟩ := can
  rcases admissible with ⟨raw', mapped', rawAdmissible⟩ | ⟨seam, eq, noExecution⟩
  · have same : raw = raw' := List.right_unique_forall₂'
      (fun _ _ _ first second => Option.some.inj (first.symm.trans second)) mapped mapped'
    subst raw'
    exact Or.inl ⟨event :: raw, .cons decoded mapped,
      Exec.prepend_admissible own rawAdmissible⟩
  · rw [eq] at mapped
    cases mapped with
    | cons head tail => rw [noExecution] at head; contradiction

/-- Canonical cuts retain the original configured wrappers; each raw execution
segment obeys the same semantic policy, and every wrapper seam is a singleton. -/
noncomputable def ConfiguredHistoryStateChronology.canonicalChunks
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint future}
    (chronology : ConfiguredHistoryStateChronology history) :
    List (ReplayChunk ConfiguredBlockStateBoundaryOrigin) :=
  StateTransition.canonicalChunks ConfiguredBlockStateBoundary.canPrepend chronology.stateBoundaries

/-- Both flattening/endpoints and semantic cuts follow from the actual configured
chronology, without a supplied partition or a second history state chain. -/
theorem ConfiguredHistoryStateChronology.canonicalChunks_spec
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint future}
    (chronology : ConfiguredHistoryStateChronology history) :
    ExactChunks chronology.stateBoundaries chronology.canonicalChunks ∧
      ∀ chunk ∈ chronology.canonicalChunks, ConfiguredAdmissibleChunk chunk :=
  ⟨StateReplay.canonicalChunks_exact ConfiguredBlockStateBoundary.canPrepend chronology.stateReplay,
    StateTransition.canonicalChunks_satisfies ConfiguredBlockStateBoundary.canPrepend
      ConfiguredAdmissibleChunk configured_singleton_admissible configured_prepend_admissible _⟩

/-- Specialize the exact local fold to the actual configured history, with
coverage at each retained block supplied by its existing chronology witness.
No independently supplied state chain or whole-run model endpoint is used. -/
theorem ConfiguredHistoryStateChronology.simulateChunks
    {Q Step O : Type}
    (R : Q → List Step → Q → Prop)
    (nil : ∀ q, R q [] q)
    (append : ∀ {a b c xs ys}, R a xs b → R b ys c → R a (xs ++ ys) c)
    (obs : List Step → List O) (obs_nil : obs [] = [])
    (obs_append : ∀ xs ys, obs (xs ++ ys) = obs xs ++ obs ys)
    (actual : ConfiguredBlockStateBoundary → List O)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint future}
    (chronology : ConfiguredHistoryStateChronology history)
    {chunks : List (ReplayChunk ConfiguredBlockStateBoundaryOrigin)}
    (exactChunks : ExactChunks chronology.stateBoundaries chunks)
    (admissible : ∀ chunk ∈ chunks, ConfiguredAdmissibleChunk chunk)
    (Link : List (ReplayChunk ConfiguredBlockStateBoundaryOrigin) → State → Q → Prop)
    {q₀ : Q} (opening : Link [] checkpoint.state q₀)
    (localStep : ∀ prior chunk suffix,
      chunks = prior ++ chunk :: suffix → ConfiguredAdmissibleChunk chunk →
      ∀ q, Link prior chunk.before q →
      ∃ q' steps, R q steps q' ∧ Link (prior ++ [chunk]) chunk.after q' ∧
        obs steps = chunk.origin.flatMap actual) :
    ∃ q' steps, R q₀ steps q' ∧ Link chunks future.state q' ∧
      obs steps = chronology.stateBoundaries.flatMap actual := by
  apply chronology.stateReplay.simulateChunks
    R nil append obs obs_nil obs_append actual exactChunks Link opening
  intro prior chunk suffix aligned q cut
  have member : chunk ∈ chunks := by
    rw [aligned]
    exact List.mem_append_right prior List.mem_cons_self
  exact localStep prior chunk suffix aligned (admissible chunk member) q cut

/-- The configured local fold consumes its actual canonical admissible cuts,
including original block/message wrappers and each retained fork witness. -/
theorem ConfiguredHistoryStateChronology.simulateCanonicalChunks
    {Q Step O : Type}
    (R : Q → List Step → Q → Prop)
    (nil : ∀ q, R q [] q)
    (append : ∀ {a b c xs ys}, R a xs b → R b ys c → R a (xs ++ ys) c)
    (obs : List Step → List O) (obs_nil : obs [] = [])
    (obs_append : ∀ xs ys, obs (xs ++ ys) = obs xs ++ obs ys)
    (actual : ConfiguredBlockStateBoundary → List O)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint future}
    (chronology : ConfiguredHistoryStateChronology history)
    (Link : List (ReplayChunk ConfiguredBlockStateBoundaryOrigin) → State → Q → Prop)
    {q₀ : Q} (opening : Link [] checkpoint.state q₀)
    (localStep : ∀ prior chunk suffix,
      chronology.canonicalChunks = prior ++ chunk :: suffix → ConfiguredAdmissibleChunk chunk →
      ∀ q, Link prior chunk.before q →
      ∃ q' steps, R q steps q' ∧ Link (prior ++ [chunk]) chunk.after q' ∧
        obs steps = chunk.origin.flatMap actual) :
    ∃ q' steps, R q₀ steps q' ∧ Link chronology.canonicalChunks future.state q' ∧
      obs steps = chronology.stateBoundaries.flatMap actual := by
  obtain ⟨exactCuts, admissible⟩ := chronology.canonicalChunks_spec
  exact chronology.simulateChunks R nil append obs obs_nil obs_append actual
    exactCuts admissible Link opening localStep

end ExecutionTrace

end Blanc
