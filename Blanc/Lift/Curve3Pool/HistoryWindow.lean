import Blanc.Lift.Curve3Pool.HistoryMid
import Blanc.ExecutionMidWindowIn

/-!
# Curve 3pool: the committed history over a window between two cuts

`pool_mid_history` over a window that stops right after a transaction of its last block rather than
at the block's end (`AccountingLadderAdmittedIn.midWindowIn`): the pool's replay from right after its
creation to right after another recorded transaction. The premises are those of the mid history that
runs on to the end of that block, so a window needs no premise of its own.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- The settlement-committed non-static pool frames of a window, in trace order. -/
def committedPoolFramesWindow {cfg : ChainConfig} {start : Benv} {pre post : BlockChain}
    (pool : Adr) (mid : MidHistoryTraceIn HistFork cfg start pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) : List Exec.Frame :=
  (mid.settledFrames ++ block.settledThroughCut cut).flatMap (poolFrameObs pool)

/-- **The pool model replays the committed window.** The statement of `pool_mid_history` with
`future` replaced by the state right after transaction `i` of the window's last block. -/
theorem pool_window_history {pool : Adr} {cfg : ChainConfig} {checkpoint : BlockChain}
    {start : Benv} {pre post : BlockChain} {s₀ : State}
    {full : ConfiguredHistoryTraceIn HistFork cfg checkpoint post}
    (mid : MidHistoryTraceIn HistFork cfg start pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (installed : some (start.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (start.state.getStor pool) s₀)
    (env : PoolMidEnv full (mid.step block) pool s₀.coins s₀.token) :
    some (cut.afterBenv.state.getCode pool).toList = poolSem.image ∧
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) =
        committedPoolFramesWindow pool mid block cut ∧
      (∀ i ∈ invs, i.Authentic pool) ∧ PoolEntries s₀ invs ∧
      ∃ s, PoolRun s₀ invs s ∧ runPool s₀ invs = some s ∧
        Checkpoint (cut.afterBenv.state.getStor pool) s ∧ s.coins = s₀.coins ∧
        s.token = s₀.token := by
  have capabilities := BodyStageCapabilities.historical
  have start' : poolSpec.StateInv pool start.state := ⟨installed, trivial, trivial⟩
  have admitted := pool_mid_trace_admitted env
  obtain ⟨⟨frames, replay, observed⟩, finishInv, -⟩ :=
    (poolLadderH (poolParties_keeps s₀.coins s₀.token) (pool_frame_refines_atH s₀.coins s₀.token) pool).midWindowIn mid block cut
      admitted.1 admitted.2 capabilities (mid.rewardCreditsFunded capabilities) start'
      pool_runtimeSafety rfl
  change PoolReplay (PoolParties s₀.coins s₀.token) pool (start.state.getStor pool).get frames
    (cut.afterBenv.state.getStor pool).get at replay
  change frames.flatMap (poolSubtreeFrames pool) =
    (mid.settledFrames ++ block.settledThroughCut cut).flatMap (poolFrameObs pool) at observed
  obtain ⟨invs, framesEq, auth, s, run, entries, σ', view, hc, -⟩ :=
    replay s₀ _ rfl initial ⟨rfl, rfl⟩
  obtain ⟨hcoins, htoken⟩ := run.coins_token
  refine ⟨finishInv.code, invs, ?_, auth, entries, s, run, run.runPool_eq,
    Checkpoint.of_get view hc, hcoins, htoken⟩
  rw [← framesEq, List.flatMap_map] at observed
  exact observed

end Blanc.Lift.Curve3Pool
