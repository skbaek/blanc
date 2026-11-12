import Blanc.Composition.BuilderRequestClassification
import Blanc.Composition.Corpus.Proofs.BuilderCheckpoint
import Blanc.ExecutionKeptStorageFold

/-!
# B-S3: Builder request contracts — deterministic whole-storage fold and checkpoint publication

The pure word-storage updaters `depositStorageUpdate` and `exitStorageUpdate` follow the exact
write order of all four arms of `DepositSettled` and `ExitSettled` (`dequeue`, `latch`,
`submission`, and `feeRead`) over arbitrary incoming storage.

1. `deposit_history_storage_replay`, `exit_history_storage_replay`, and `history_storage_fold`
   establish the whole-storage fold over every kept history starting with both builder codes
   installed (`CodesKept`), with no clean-history, initialization, `systemEmpty`, or submission-cap
   premise.
2. `observed_history_storage_exact` specializes to an observed checkpoint (`BuilderCheckpointObservation`),
   packaging both whole-storage fold equations, end-to-end FIFO delivery, and per-block
   request-boundary `storedQueue` publication from the guarded prefix before each block's first
   system frame.
-/

namespace Blanc.Composition.BuilderRequestPublic

open Jaune Blanc Blanc.Lift.BuilderRequest
open Blanc.ExecutionAccountingReplay

/-- Whole-storage extraction for the builder latch, reusing the shared updater with
its exact inhibitor write and the bytecode's original store order. -/
theorem latchState_getStor (p : Blanc.Lift.RequestSystem.SysShape) (σ : State) (a : Adr) :
    (latchState p σ a).getStor a = Delivery.drainStor { p with next := fun _ _ => B256.max } (σ.getStor a) := by
  unfold latchState Delivery.drainStor
  dsimp only
  split <;> simp only [State.getStor_setStorVal_self]

/-- Pure whole-word storage update for a committed frame at the builder deposit contract,
matching the four disjoint arms of `DepositSettled` (`dequeue`, `latch`, 184-byte `submission`,
and `feeRead`). -/
def depositStorageUpdate (s : Stor) (call : Sevm) : Stor :=
  if call.caller = systemAddress then
    if call.data = [] then
      Delivery.drainStor Deposit.sysShape s
    else
      Delivery.drainStor { Deposit.sysShape with next := fun _ _ => B256.max } s
  else if call.data.length = 184 then
    Deposit.submittedStorage call s
  else
    s

/-- Pure whole-word storage update for a committed frame at the builder exit contract,
matching the four disjoint arms of `ExitSettled` (`dequeue`, `latch`, 48-byte `submission`,
and `feeRead`). -/
def exitStorageUpdate (s : Stor) (call : Sevm) : Stor :=
  if call.caller = systemAddress then
    if call.data = [] then
      Delivery.drainStor Exit.sysShape s
    else
      Delivery.drainStor { Exit.sysShape with next := fun _ _ => B256.max } s
  else if call.data.length = 48 then
    Exit.submittedStorage call s
  else
    s

/-- Fold `depositStorageUpdate` across every frame kept at the builder deposit contract. -/
def depositStoreAfter (s : Stor) (frames : List Exec.Frame) : Stor :=
  frames.foldl (fun incoming f => depositStorageUpdate incoming f.sevm) s

/-- Fold `exitStorageUpdate` across every frame kept at the builder exit contract. -/
def exitStoreAfter (s : Stor) (frames : List Exec.Frame) : Stor :=
  frames.foldl (fun incoming f => exitStorageUpdate incoming f.sevm) s

/-- Every `DepositSettled` arm updates `depositAddr` storage by `depositStorageUpdate`. -/
theorem deposit_settled_storageUpdate {b : KeptBlock} {f : Exec.Frame}
    (settled : Corpus.Freeze.Builder.DepositSettled b f) :
    Devm.getStor f.post depositAddr =
      depositStorageUpdate (Devm.getStor f.pre depositAddr) f.sevm := by
  cases settled with
  | dequeue caller empty _ state _ _ _ =>
      rw [depositStorageUpdate, ite_eq_left caller, ite_eq_left empty]
      change f.post.state.getStor depositAddr = _
      rw [state, Delivery.sysState_getStor]
      rfl
  | latch caller nonempty _ state _ _ _ =>
      rw [depositStorageUpdate, ite_eq_left caller, ite_eq_right nonempty]
      change f.post.state.getStor depositAddr = _
      rw [state, latchState_getStor]
      rfl
  | submission caller length _ _ _ storage _ _ _ _ =>
      simpa only [depositStorageUpdate, ite_eq_right caller, ite_eq_left length] using storage
  | feeRead caller empty _ _ _ storage _ _ =>
      have length : f.sevm.data.length ≠ 184 := by rw [empty]; decide
      simpa only [depositStorageUpdate, ite_eq_right caller, ite_eq_right length] using
        storage depositAddr

/-- Every `ExitSettled` arm updates `exitAddr` storage by `exitStorageUpdate`. -/
theorem exit_settled_storageUpdate {b : KeptBlock} {f : Exec.Frame}
    (settled : Corpus.Freeze.Builder.ExitSettled b f) :
    Devm.getStor f.post exitAddr =
      exitStorageUpdate (Devm.getStor f.pre exitAddr) f.sevm := by
  cases settled with
  | dequeue caller empty _ state _ _ _ =>
      rw [exitStorageUpdate, ite_eq_left caller, ite_eq_left empty]
      change f.post.state.getStor exitAddr = _
      rw [state, Delivery.sysState_getStor]
      rfl
  | latch caller nonempty _ state _ _ _ =>
      rw [exitStorageUpdate, ite_eq_left caller, ite_eq_right nonempty]
      change f.post.state.getStor exitAddr = _
      rw [state, latchState_getStor]
      rfl
  | submission caller length _ _ _ storage _ _ _ _ =>
      simpa only [exitStorageUpdate, ite_eq_right caller, ite_eq_left length] using storage
  | feeRead caller empty _ _ _ storage _ _ =>
      have length : f.sevm.data.length ≠ 48 := by rw [empty]; decide
      simpa only [exitStorageUpdate, ite_eq_right caller, ite_eq_right length] using
        storage exitAddr

/-- Exact guarded storage replay at `depositAddr` over any `CodesKept` history. -/
theorem deposit_history_storage_replay {cfg : ChainConfig} {start stop : BlockChain}
    {blocks : List KeptBlock} (kept : CodesKept cfg start blocks stop) :
    GuardedStorageReplay (fun incoming (f : Exec.Frame) => depositStorageUpdate incoming f.sevm)
      (fun incoming f => Devm.getStor f.pre depositAddr = incoming)
      (start.state.getStor depositAddr) (blocks.flatMap (KeptBlock.keptAt depositAddr))
      (stop.state.getStor depositAddr) := by
  have hc : (start.state.getCode depositAddr).toList ≠ [] := by
    rw [kept.deposit]
    exact Deposit.linked.runnable.1
  have hd : ¬ isValidDelegation (start.state.getCode depositAddr) := by
    rw [kept.deposit]
    exact Deposit.linked.runnable.2
  refine (kept.linked.chain hc hd).1.storageReplay
    (fun incoming f => depositStorageUpdate incoming f.sevm) ?_
  intro f hf
  obtain ⟨b, hb, member⟩ := List.mem_flatMap.mp hf
  exact deposit_settled_storageUpdate
    (BuilderRequestClassification.b_s2_deposit kept b hb f member)

/-- Exact guarded storage replay at `exitAddr` over any `CodesKept` history. -/
theorem exit_history_storage_replay {cfg : ChainConfig} {start stop : BlockChain}
    {blocks : List KeptBlock} (kept : CodesKept cfg start blocks stop) :
    GuardedStorageReplay (fun incoming (f : Exec.Frame) => exitStorageUpdate incoming f.sevm)
      (fun incoming f => Devm.getStor f.pre exitAddr = incoming)
      (start.state.getStor exitAddr) (blocks.flatMap (KeptBlock.keptAt exitAddr))
      (stop.state.getStor exitAddr) := by
  have hc : (start.state.getCode exitAddr).toList ≠ [] := by
    rw [kept.exit]
    exact Exit.linked.runnable.1
  have hd : ¬ isValidDelegation (start.state.getCode exitAddr) := by
    rw [kept.exit]
    exact Exit.linked.runnable.2
  refine (kept.linked.chain hc hd).1.storageReplay
    (fun incoming f => exitStorageUpdate incoming f.sevm) ?_
  intro f hf
  obtain ⟨b, hb, member⟩ := List.mem_flatMap.mp hf
  exact exit_settled_storageUpdate
    (BuilderRequestClassification.b_s2_exit kept b hb f member)

/-- **B-S3 unrestricted whole-storage fold.** Under `CodesKept` alone (no clean-history,
initialization, `systemEmpty`, or submission-cap premise), the final storage of both builder
contracts equals the deterministic fold over their kept frames. -/
theorem history_storage_fold {cfg : ChainConfig} {start stop : BlockChain}
    {blocks : List KeptBlock} (kept : CodesKept cfg start blocks stop) :
    stop.state.getStor depositAddr =
      depositStoreAfter (start.state.getStor depositAddr)
        (blocks.flatMap (KeptBlock.keptAt depositAddr)) ∧
    stop.state.getStor exitAddr =
      exitStoreAfter (start.state.getStor exitAddr)
        (blocks.flatMap (KeptBlock.keptAt exitAddr)) :=
  ⟨(deposit_history_storage_replay kept).fold_eq.symm,
    (exit_history_storage_replay kept).fold_eq.symm⟩

private theorem deposit_boundary_queue_eq {cfg : ChainConfig} {checkpoint stop : BlockChain}
    {blocks pre post : List KeptBlock} {b : KeptBlock}
    (ck : CodesKept cfg checkpoint blocks stop)
    (dClean : Deposit.Indexed.Clean cfg checkpoint blocks stop)
    (split : blocks = pre ++ b :: post) (am : b.fork = .amsterdam) :
    Deposit.Indexed.queueAtRequests b =
      Occurrence.storedQueue Deposit.Indexed.reading
        (depositStoreAfter (checkpoint.state.getStor depositAddr)
          (pre.flatMap (KeptBlock.keptAt depositAddr) ++
            (b.keptAt depositAddr).takeWhile (fun f => !Occurrence.isSystemFrame f))).get := by
  obtain ⟨fss, related, -, -⟩ := dClean.premises.frames Deposit.linked
  rw [split] at related
  obtain ⟨_, _, _, _, _, one, -⟩ := Blanc.List.forall₂_split related
  have hcount := one.2.2
  rw [ite_eq_left am] at hcount
  have replay := deposit_history_storage_replay ck
  rw [split, List.flatMap_append, List.flatMap_cons] at replay
  obtain ⟨f, found, guard⟩ := replay.find_guard_of_filter_one
    (left := pre.flatMap (KeptBlock.keptAt depositAddr)) (middle := b.keptAt depositAddr)
    (right := post.flatMap (KeptBlock.keptAt depositAddr)) Occurrence.isSystemFrame hcount
  have incoming : Devm.getStor f.pre depositAddr =
      depositStoreAfter (checkpoint.state.getStor depositAddr)
        (pre.flatMap (KeptBlock.keptAt depositAddr) ++
          (b.keptAt depositAddr).takeWhile (fun f => !Occurrence.isSystemFrame f)) := guard
  change (match (b.keptAt depositAddr).find? Occurrence.isSystemFrame with
    | some frame => Occurrence.storedQueue Deposit.Indexed.reading (Devm.getStor frame.pre depositAddr).get
    | none => []) = _
  rw [found]
  dsimp only
  rw [incoming]

private theorem exit_boundary_queue_eq {cfg : ChainConfig} {checkpoint stop : BlockChain}
    {blocks pre post : List KeptBlock} {b : KeptBlock}
    (ck : CodesKept cfg checkpoint blocks stop)
    (eClean : Exit.Indexed.Clean cfg checkpoint blocks stop)
    (split : blocks = pre ++ b :: post) (am : b.fork = .amsterdam) :
    Exit.Indexed.queueAtRequests b =
      Occurrence.storedQueue Exit.Indexed.reading
        (exitStoreAfter (checkpoint.state.getStor exitAddr)
          (pre.flatMap (KeptBlock.keptAt exitAddr) ++
            (b.keptAt exitAddr).takeWhile (fun f => !Occurrence.isSystemFrame f))).get := by
  obtain ⟨fss, related, -, -⟩ := eClean.premises.frames Exit.linked
  rw [split] at related
  obtain ⟨_, _, _, _, _, one, -⟩ := Blanc.List.forall₂_split related
  have hcount := one.2.2
  rw [ite_eq_left am] at hcount
  have replay := exit_history_storage_replay ck
  rw [split, List.flatMap_append, List.flatMap_cons] at replay
  obtain ⟨f, found, guard⟩ := replay.find_guard_of_filter_one
    (left := pre.flatMap (KeptBlock.keptAt exitAddr)) (middle := b.keptAt exitAddr)
    (right := post.flatMap (KeptBlock.keptAt exitAddr)) Occurrence.isSystemFrame hcount
  have incoming : Devm.getStor f.pre exitAddr =
      exitStoreAfter (checkpoint.state.getStor exitAddr)
        (pre.flatMap (KeptBlock.keptAt exitAddr) ++
          (b.keptAt exitAddr).takeWhile (fun f => !Occurrence.isSystemFrame f)) := guard
  change (match (b.keptAt exitAddr).find? Occurrence.isSystemFrame with
    | some frame => Occurrence.storedQueue Exit.Indexed.reading (Devm.getStor frame.pre exitAddr).get
    | none => []) = _
  rw [found]
  dsimp only
  rw [incoming]

/-- **B-S3 observed checkpoint storage & publication endpoint.** From an adopted
`BuilderCheckpointObservation` and clean numerical bounds, packages:
1. Both whole-storage folds from `checkpoint.state`,
2. Exact end-to-end FIFO delivery (`BuilderCheckpoint.observed_history_fifo`), and
3. Per-block request-boundary `storedQueue` publication from the guarded prefix before each
   block's first system frame for both builder contracts. -/
theorem observed_history_storage_exact {expectedStateRoot : B256} {cfg : ChainConfig}
    {checkpoint stop : BlockChain} {blocks : List KeptBlock}
    (obs : Corpus.Freeze.Builder.BuilderCheckpointObservation expectedStateRoot checkpoint)
    (kept : KeptHistory cfg checkpoint blocks stop) (clean : HistoryClean blocks)
    (budget : feesPaidAt blocks depositAddr ≤ 2 ^ 256)
    (few : (exitSubmitted blocks).length ≤ 2 ^ 64) :
    (stop.state.getStor depositAddr =
        depositStoreAfter (checkpoint.state.getStor depositAddr)
          (blocks.flatMap (KeptBlock.keptAt depositAddr)) ∧
      stop.state.getStor exitAddr =
        exitStoreAfter (checkpoint.state.getStor exitAddr)
          (blocks.flatMap (KeptBlock.keptAt exitAddr))) ∧
    (Deposit.Indexed.submissions blocks =
        Deposit.Indexed.emissions blocks ++ Deposit.Indexed.remainingQueue stop ∧
      Exit.Indexed.submissions blocks =
        Exit.Indexed.emissions blocks ++ Exit.Indexed.remainingQueue stop) ∧
    ∀ pre b post, blocks = pre ++ b :: post →
      let fsD := pre.flatMap (KeptBlock.keptAt depositAddr) ++
        (b.keptAt depositAddr).takeWhile (fun f => !Occurrence.isSystemFrame f)
      let sD := depositStoreAfter (checkpoint.state.getStor depositAddr) fsD
      let fsE := pre.flatMap (KeptBlock.keptAt exitAddr) ++
        (b.keptAt exitAddr).takeWhile (fun f => !Occurrence.isSystemFrame f)
      let sE := exitStoreAfter (checkpoint.state.getStor exitAddr) fsE
      ((Deposit.Indexed.blockEmissions b).flatten = ChainLink.blockDelivered 3 b ∧
        (b.fork ≠ .amsterdam → Deposit.Indexed.blockEmissions b = []) ∧
        (b.fork = .amsterdam →
          Deposit.Indexed.blockEmissions b =
            (Occurrence.storedQueue Deposit.Indexed.reading sD.get).take 64)) ∧
      ((Exit.Indexed.blockEmissions b).flatten = ChainLink.blockDelivered 4 b ∧
        (b.fork ≠ .amsterdam → Exit.Indexed.blockEmissions b = []) ∧
        (b.fork = .amsterdam →
          Exit.Indexed.blockEmissions b =
            (Occurrence.storedQueue Exit.Indexed.reading sE.get).take 16)) := by
  let ck := Corpus.Proofs.BuilderCheckpoint.codesKept_of_observed obs kept
  let dClean := Corpus.Proofs.BuilderCheckpoint.depositClean_of_observed obs kept clean budget
  let eClean := Corpus.Proofs.BuilderCheckpoint.exitClean_of_observed obs kept clean few
  refine ⟨history_storage_fold ck,
    Corpus.Proofs.BuilderCheckpoint.observed_history_fifo obs kept clean budget few, ?_⟩
  intro pre b post split
  dsimp only
  have hD := Deposit.Indexed.history_block dClean split
  have hE := Exit.Indexed.history_block eClean split
  refine ⟨⟨hD.1.1, fun ne => (hD.2.1 ne).1, fun am => ?_⟩,
    ⟨hE.1.1, fun ne => (hE.2.1 ne).1, fun am => ?_⟩⟩
  · rw [← deposit_boundary_queue_eq ck dClean split am]
    exact (hD.2.2 am).1
  · rw [← exit_boundary_queue_eq ck eClean split am]
    exact (hE.2.2 am).1

end Blanc.Composition.BuilderRequestPublic
