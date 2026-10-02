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

end ExecutionTrace

end Blanc
