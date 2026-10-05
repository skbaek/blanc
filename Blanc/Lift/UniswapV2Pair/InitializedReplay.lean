import Blanc.Lift.UniswapV2Pair.Creation.DeployInit
import Blanc.Lift.UniswapV2Pair.ReplayWriterGas

/-! Replay and positive writer gas from the checkpoint established by the
actual CREATE2/initialize theorem. Configured-history authentication must still
produce the connected storage replay and its original source invocations. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The initialized deployment checkpoint carries the empty LP ledger. -/
theorem initializedState_ledger (factory : Adr) (domain : B256) (token0 token1 : Adr) :
    (initializedState factory domain token0 token1).Ledger :=
  (State.initialized_ledgerOn factory domain token0 token1).ledger

/-- One deployment checkpoint determines the carried model state, ledger,
ordered modular oracle folds and fee-off share-value laws. The same derived
final state and finite key set then support every accepted LP writer at its
closed physical gas cost. No later representation witness is an input. -/
theorem InitializedCheckpoint.replay_laws {U : WriterKey → Prop} {pre post : Stor}
    {factory token0 token1 : Adr} {domain : B256} {invs : List SourceInvocation}
    (checkpoint : InitializedCheckpoint pre factory domain token0 token1)
    (replay : PairStorageReplay U pre invs post)
    (answers : sourceReplayAnswers (initializedState factory domain token0 token1) invs)
    (inj : WriterInj U) (apart : WriterApart U) :
    ∃ finish K, runSourceInvocations (initializedState factory domain token0 token1) invs =
        some finish ∧
      (∀ k, K k → U k) ∧ WriterRep K post finish ∧ finish.Ledger ∧
      finish.price0CumulativeLast.toNat =
        ((initializedState factory domain token0 token1).price0CumulativeLast.toNat +
          oracleSum0 (sourceReplayUpdates (initializedState factory domain token0 token1) invs)) %
          2 ^ 256 ∧
      finish.price1CumulativeLast.toNat =
        ((initializedState factory domain token0 token1).price1CumulativeLast.toNat +
          oracleSum1 (sourceReplayUpdates (initializedState factory domain token0 token1) invs)) %
          2 ^ 256 ∧
      (∀ before after, (before, after) ∈
          sourceReplayEdges (initializedState factory domain token0 token1) invs →
        0 < before.totalSupply.toNat →
        before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
          after.reserve0.val * after.reserve1.val * before.totalSupply.toNat ^ 2) ∧
      ∀ (writer : LedgerWriter) (sevm : Sevm) (b : Devm) (current : Checkpoint)
        (invocation : List Nat) (G : Nat) (sourceFrame : Frame) (returndata : Bytes),
        b.getStor sevm.currentTarget = post → current.state = finish →
        (∀ k ∈ writer.keys sevm, U k) → sevm.data.length < 2 ^ 256 →
        writer.calldataSize ≤ sevm.data.length → sevm.code = code →
        CoveredFork sevm.benvStat.fork → Blanc.Sevm.selector sevm = writer.selector →
        gCallStipend < G →
        startImmediate current (writerContext sevm invocation) (writer.entry sevm) =
          some (.finished sourceFrame returndata) →
        SProg.RunExact cert.prog sevm (St b [] Mem.empty (G + writer.cost sevm b))
            (writer.post sevm b G) ∧
          Nonempty (Exec 0 sevm (St b [] Mem.empty (G + writer.cost sevm b))
            (.ok (writer.post sevm b G))) ∧
          writer.Result K current invocation sevm b (writer.post sevm b G) G := by
  obtain ⟨finish, K, realized, _, included, rep, ledger, oracle0, oracle1, product⟩ :=
    replay.model_laws (fun _ h => h.elim) checkpoint
      (initializedState_ledger factory domain token0 token1) answers
  refine ⟨finish, K, realized, included, rep, ledger, oracle0, oracle1, product, ?_⟩
  intro writer sevm b current invocation G sourceFrame returndata storageEq stateEq
    good representable length codeEq fork selectorEq residual accepted
  have incoming : WriterRep K (b.getStor sevm.currentTarget) current.state := by
    rw [storageEq, stateEq]
    exact rep
  exact writer.source_live incoming
    (Blanc.SlotFootprint.FreshKeys.of_universe inj apart included good)
    representable length codeEq fork selectorEq residual accepted

end Blanc.Lift.UniswapV2Pair
