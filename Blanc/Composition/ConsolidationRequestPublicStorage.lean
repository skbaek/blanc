import Blanc.Composition.ConsolidationRequestPublicHistory
import Blanc.Composition.Corpus.Proofs.ConsolidationExecution
import Blanc.Lift.ConsolidationRequest.Occurrence
import Blanc.Lift.RequestSystem.Storage
import Blanc.ExecutionKeptStorageFold

/-!
# EIP-7251: the complete word-storage fold and actual block publication

The pure updater follows the bytecode's write order over arbitrary incoming storage. The core
history fold needs only installed code and covered forks. The checkpoint theorem adds exactly
the existing FIFO premises and identifies each actual request boundary by the guarded prefix.
-/

namespace Blanc.Composition.ConsolidationRequestPublic

open Jaune Blanc Blanc.Lift
open Blanc.ExecutionAccountingReplay
open Blanc.Lift.ConsolidationRequest (Record keptRecord)
open Blanc.Lift.BuilderRequest (queueBase)

/-- The bytes' exact word update, using only incoming storage and the call's caller/calldata.
No post-state is read; stale slots and word-arithmetic aliases retain their actual write order. -/
def storageUpdate (s : Stor) (call : Sevm) : Stor :=
  if call.caller = systemAddress then
    BuilderRequest.Delivery.drainStor SystemExecution.ConsolidationRequest.Amsterdam.sysShape s
  else if call.data.length = 96 then ConsolidationRequest.submittedStorage call s else s

/-- Apply the pure word update to every frame actually kept at this contract, in order. -/
def storeAfter (s : Stor) (frames : List Exec.Frame) : Stor :=
  frames.foldl (fun incoming f => storageUpdate incoming f.sevm) s

/-- Exact C-S2 effects imply the pure update on the whole storage, in every success arm. -/
theorem settled_storageUpdate {f : Exec.Frame} (settled : Corpus.Freeze.Consolidation.Settled f) :
    Devm.getStor f.post addr = storageUpdate (Devm.getStor f.pre addr) f.sevm := by
  cases settled with
  | dequeue caller _ state _ _ =>
      rw [storageUpdate, ite_eq_left caller]
      change f.post.state.getStor addr = _
      rw [state, BuilderRequest.Delivery.sysState_getStor]
      rfl
  | submission caller length _ _ _ storage _ _ _ _ =>
      simpa only [storageUpdate, ite_eq_right caller, ite_eq_left length] using storage
  | feeRead caller empty _ _ _ storage _ _ =>
      have length : f.sevm.data.length ≠ 96 := by rw [empty]; decide
      simpa only [storageUpdate, ite_eq_right caller, ite_eq_right length] using storage addr

/-- Derive every incoming storage boundary from the actual history; no replay is assumed. -/
theorem history_storage_replay {cfg : ChainConfig} {start final : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory cfg start blocks final) (code : installed start.state)
    (covered : ∀ b ∈ blocks, CoveredFork b.fork) :
    GuardedStorageReplay (fun incoming (f : Exec.Frame) => storageUpdate incoming f.sevm)
      (fun incoming f => Devm.getStor f.pre addr = incoming)
      (start.state.getStor addr) (blocks.flatMap (KeptBlock.keptAt addr)) (final.state.getStor addr) := by
  obtain ⟨-, nondelegating, nonempty⟩ := systemContracts_facts _ ConsolidationRequest.member
  have hc : (start.state.getCode addr).toList ≠ [] := by rw [code]; exact nonempty
  have hd : ¬ isValidDelegation (start.state.getCode addr) := by rw [code]; exact nondelegating
  refine (history.chain hc hd).1.storageReplay (fun incoming f => storageUpdate incoming f.sevm) ?_
  intro f hf
  obtain ⟨b, hb, member⟩ := List.mem_flatMap.mp hf
  exact settled_storageUpdate (Corpus.Proofs.Consolidation.c_s2 history code covered b hb f member)

/-- **Exact whole storage.** This includes metadata, stale record slots and arbitrary untouched root
contents, without a clean-history, initialization, submission-cap or no-wrap premise. -/
theorem history_storage_fold {cfg : ChainConfig} {start final : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory cfg start blocks final) (code : installed start.state)
    (covered : ∀ b ∈ blocks, CoveredFork b.fork) :
    final.state.getStor addr = storeAfter (start.state.getStor addr) (blocks.flatMap (KeptBlock.keptAt addr)) :=
  (history_storage_replay history code covered).fold_eq.symm

/-- **C-S3 positive endpoint.** The entire final storage is the actual committed-call fold. Under
exactly C4's root, clean-history and submission bound, FIFO holds and each block publishes precisely
the first two records at its actual request-boundary prefix, with exact flattened bytes. -/
theorem history_storage_exact {cfg : ChainConfig} {checkpoint final : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory cfg checkpoint blocks final) (covered : ∀ b ∈ blocks, CoveredFork b.fork)
    (start : CheckpointStart checkpoint.state) (clean : HistoryClean blocks)
    (cap : (submissions blocks).length ≤ 2 ^ 253) :
    final.state.getStor addr = storeAfter (checkpoint.state.getStor addr) (blocks.flatMap (KeptBlock.keptAt addr)) ∧
    Fifo blocks final.state ∧
    ∀ pre b post, blocks = pre ++ b :: post →
      let fs := pre.flatMap (KeptBlock.keptAt addr) ++
        (b.keptAt addr).takeWhile (fun f => !RequestQueue.Occurrence.isSystemFrame f)
      let s := storeAfter (checkpoint.state.getStor addr) fs
      records116 (blockConsolidations b) = (storedQueue s.get).take 2 ∧
        (records116 (blockConsolidations b)).flatten = blockConsolidations b := by
  refine ⟨history_storage_fold history start.code covered, history_fifo history covered start clean cap, ?_⟩
  have hlen : ((RequestQueue.Link.kept addr blocks).filterMap keptRecord).length ≤ 2 ^ 253 := by
    rw [submissions_eq, List.length_map] at cap
    exact cap
  have hlen' : ((RequestQueue.Link.kept ConsolidationRequest.linked.address blocks).filterMap
      ConsolidationRequest.linked.record?).length ≤ 2 ^ 253 := hlen
  have h256 : (2 : Nat) ^ 256 = 8 * 2 ^ 253 := rfl
  have premises : RequestQueue.Occurrence.Premises ConsolidationRequest.linked cfg checkpoint blocks final
      ⟨2 ^ 256 - 1, 0, 0, 0, []⟩ :=
    ⟨history, covered, start.code, start.holds, start.systemEmpty, clean,
      by dsimp only; unfold queueBase; omega, by dsimp only; omega⟩
  intro pre b post split
  dsimp only
  obtain ⟨fss, related, -, -⟩ := premises.steps ConsolidationRequest.drainLinked
  rw [split] at related
  obtain ⟨_, _, _, _, _, one, _⟩ := Blanc.List.forall₂_split related
  obtain ⟨before, f, after, frames, -, -, found, taken⟩ :=
    Blanc.List.split_of_filter_length_one RequestQueue.Occurrence.isSystemFrame one.2.2
  change b.keptAt addr = before ++ f :: after at frames
  change (b.keptAt addr).find? RequestQueue.Occurrence.isSystemFrame = some f at found
  change (b.keptAt addr).takeWhile (fun x => !RequestQueue.Occurrence.isSystemFrame x) = before at taken
  have frameSplit : blocks.flatMap (KeptBlock.keptAt addr) =
      (pre.flatMap (KeptBlock.keptAt addr) ++ before) ++ f ::
        (after ++ post.flatMap (KeptBlock.keptAt addr)) := by
    rw [split, List.flatMap_append, List.flatMap_cons, frames]
    simp only [List.append_assoc, List.cons_append]
  have replay := history_storage_replay history start.code covered
  rw [frameSplit] at replay
  have atFrame := (replay.split (left := pre.flatMap (KeptBlock.keptAt addr) ++ before)
    (right := f :: (after ++ post.flatMap (KeptBlock.keptAt addr)))).2.head_guard
  have incoming : Devm.getStor f.pre addr = storeAfter (checkpoint.state.getStor addr)
      (pre.flatMap (KeptBlock.keptAt addr) ++
        (b.keptAt addr).takeWhile (fun f => !RequestQueue.Occurrence.isSystemFrame f)) := by
    rw [taken]
    exact atFrame
  have boundary : RequestQueue.Occurrence.queueAtRequests ConsolidationRequest.reading
      ConsolidationRequest.linked b = storedQueue (storeAfter (checkpoint.state.getStor addr)
        (pre.flatMap (KeptBlock.keptAt addr) ++
          (b.keptAt addr).takeWhile (fun f => !RequestQueue.Occurrence.isSystemFrame f))).get := by
    change (match (b.keptAt addr).find? RequestQueue.Occurrence.isSystemFrame with
      | some frame => storedQueue (Devm.getStor frame.pre addr).get
      | none => []) = _
    rw [found]
    dsimp only
    rw [incoming]
  have emission : RequestQueue.Occurrence.blockEmissions ConsolidationRequest.reading
      ConsolidationRequest.linked b = records116 (blockConsolidations b) := by
    rw [blockConsolidations_eq]
    rfl
  have published := RequestQueue.Occurrence.history_block ConsolidationRequest.reading
    ConsolidationRequest.drainLinked premises split
  rw [emission] at published
  refine ⟨?_, published.1.1.trans (blockConsolidations_eq b).symm⟩
  rw [boundary] at published
  exact published.2.2.1

/-- The same complete storage/publication result from the existing recorded mainnet checkpoint.
This projects the supplied observation; it adds no zero-stale-storage or authentication claim. -/
theorem history_storage_exact_mainnet {checkpoint final : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory mainnetChainConfig checkpoint blocks final)
    (obs : ConsolidationCheckpointObservation checkpoint) (clean : HistoryClean blocks)
    (cap : (submissions blocks).length ≤ 2 ^ 253) :
    final.state.getStor addr = storeAfter (checkpoint.state.getStor addr) (blocks.flatMap (KeptBlock.keptAt addr)) ∧
    Fifo blocks final.state ∧
    ∀ pre b post, blocks = pre ++ b :: post →
      let fs := pre.flatMap (KeptBlock.keptAt addr) ++
        (b.keptAt addr).takeWhile (fun f => !RequestQueue.Occurrence.isSystemFrame f)
      let s := storeAfter (checkpoint.state.getStor addr) fs
      records116 (blockConsolidations b) = (storedQueue s.get).take 2 ∧
        (records116 (blockConsolidations b)).flatten = blockConsolidations b :=
  history_storage_exact history (mainnet_covered history) obs.start clean cap

end Blanc.Composition.ConsolidationRequestPublic
