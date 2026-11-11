import Blanc.Composition.Corpus.Freeze.ConsolidationExecution
import Blanc.Lift.ConsolidationRequest.Occurrence
import Blanc.Lift.RequestQueue.DrainLatency

/-! # EIP-7251 bounded queue delivery and its capacity/publication control -/

namespace Blanc.Corpus.Proofs.Consolidation

open Jaune Blanc
open Blanc.Composition.ConsolidationRequestPublic
open Blanc.Corpus.Freeze.Consolidation
open Blanc.Lift.ConsolidationRequest
open Blanc.Lift.BuilderRequest (QueueState queueBase)

private theorem queueAtRequests_eq (b : KeptBlock) :
    Lift.RequestQueue.Occurrence.queueAtRequests reading linked b = queueAtRequests b := rfl

private theorem occurrence_blockEmissions (b : KeptBlock) :
    Lift.RequestQueue.Occurrence.blockEmissions reading linked b = Blanc.Composition.ConsolidationRequestPublic.records116 (Blanc.Composition.ConsolidationRequestPublic.blockConsolidations b) := by
  rw [Blanc.Composition.ConsolidationRequestPublic.blockConsolidations_eq]
  rfl

private theorem occurrence_submissions (blocks : List KeptBlock) :
    Lift.RequestQueue.Occurrence.submissions linked blocks = Blanc.Composition.ConsolidationRequestPublic.submissions blocks := (Blanc.Composition.ConsolidationRequestPublic.submissions_eq blocks).symm

private theorem occurrence_emissions (blocks : List KeptBlock) :
    Lift.RequestQueue.Occurrence.emissions reading linked blocks = Blanc.Composition.ConsolidationRequestPublic.emissions blocks := by
  unfold Lift.RequestQueue.Occurrence.emissions Blanc.Composition.ConsolidationRequestPublic.emissions
  congr 1
  funext b
  exact occurrence_blockEmissions b


/-- **C-S8.** Every record at a request boundary is published by its exact quotient block,
at its exact remainder slot, with the frozen prefix and submission-occurrence identities. -/
theorem c_s8 : C_S8 := by
  intro cfg start final blocks kept covered root clean cap j q B D r atB atD queued
  have hlen : ((Lift.RequestQueue.Link.kept addr blocks).filterMap keptRecord).length ≤ 2 ^ 253 := by
    rw [Blanc.Composition.ConsolidationRequestPublic.submissions_eq, List.length_map] at cap
    exact cap
  have h256 : (2 : Nat) ^ 256 = 8 * 2 ^ 253 := rfl
  have hlen' : ((Lift.RequestQueue.Link.kept linked.address blocks).filterMap linked.record?).length ≤
      2 ^ 253 := hlen
  have premises : Lift.RequestQueue.Occurrence.Premises linked cfg start blocks final
      ⟨2 ^ 256 - 1, 0, 0, 0, []⟩ :=
    ⟨kept, covered, root.code, root.holds, root.systemEmpty, clean,
      by dsimp only; unfold queueBase; omega, by dsimp only; omega⟩
  obtain ⟨delivered, preceding, occurrence, -⟩ :=
    Lift.RequestQueue.Occurrence.history_latency reading drainLinked premises (by decide)
      atB atD (by rw [queueAtRequests_eq]; exact queued)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [blockRecords, occurrence_blockEmissions] using delivered
  · simpa only [blockRecords, occurrence_blockEmissions, queueAtRequests_eq] using preceding
  · simpa only [List.map_nil, List.nil_append, occurrence_submissions, occurrence_emissions] using occurrence

private def controlStorage : Stor := (Stor.empty.set 3 2).set 11 1
private def controlFirst : Bytes := queueRecord controlStorage.get 0
private def controlSecond : Bytes := queueRecord controlStorage.get 1

private theorem storage_capacity_control :
    storedQueue controlStorage.get = [controlFirst, controlSecond] ∧
    controlFirst.length = 116 ∧ controlSecond.length = 116 ∧ controlFirst ≠ controlSecond ∧
    (storedQueue controlStorage.get)[1]? = some controlSecond ∧
    (records116 (Lift.ConsolidationRequest.drained controlStorage.get))[1 % 2]? = some controlSecond ∧
    records116 (drainedCap1 controlStorage.get) = [controlFirst] ∧
    (records116 (drainedCap1 controlStorage.get))[1 % 2]? ≠ some controlSecond ∧
    (records116 [])[1 % 2]? ≠ some controlSecond := by
  decide +kernel

/-- **C-S8 control.** Capacity two has the model bound. Capacity one breaks it, and the
closed storage witness also distinguishes the real dequeue from capacity-one and omitted publication. -/
theorem c_s8_control : C_S8_control := by
  refine ⟨?_, ?_, controlStorage, controlFirst, controlSecond, storage_capacity_control⟩
  · intro st es j q r ds drains queued delivered
    exact Lift.RequestQueue.deliveries_drain_position 2 (by decide) st es j q r ds drains queued delivered
  · intro law
    have bad := law (⟨0, 0, 0, 2, [[0], [1]]⟩ : QueueState Bytes)
      [.drain (fun _ _ => 0)] 0 1 [1] [[0]] (by
        intro k hk
        have same : k = 0 := by omega
        subst k
        exact ⟨fun _ _ => 0, rfl⟩) rfl rfl
    cases bad

end Blanc.Corpus.Proofs.Consolidation
