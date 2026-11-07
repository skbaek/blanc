import Blanc.Lift.Curve3Pool.AmpHistory
import Blanc.Lift.Curve3Pool.HistoryMid
import Blanc.ExecutionMidHistoryInFrameTime

/-!
# Curve 3pool: the amplification coefficient over the committed mid history (U5)

`AmpHistory.lean` over `pool_mid_history`. An invocation of the replay is a settled frame of the mid
history, so it ran at the header timestamp of the block that retained it
(`MidHistoryTraceIn.settledFrames_time`), and its recorded time is that timestamp (`EnvOf.time`).

* `pool_mid_invocation_time` — an authentic invocation ran at its block's header timestamp;
* `pool_mid_history_amp` — the U5 headline over the mid history.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.ExecutionTrace

/-- **An authentic invocation of the mid replay ran at its block's header timestamp**, and its recorded
time is that timestamp. -/
theorem pool_mid_invocation_time {pool : Adr} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} {trace : MidHistoryTraceIn HistFork cfg start future}
    {invs : List PoolInvocation}
    (hobs : invs.flatMap (fun i => poolSubtreeFrames pool i.frame) =
      committedPoolFramesMid pool trace)
    {i : PoolInvocation} (hi : i ∈ invs) (auth : i.Authentic pool) :
    ∃ blk : Block, (blk, i.frame) ∈ trace.blockFrames ∧
      i.env.time = blk.header.timestamp.toB256.toNat := by
  obtain ⟨blk, hb, ht⟩ := trace.settledFrames_time _ (pool_invocation_mem hobs hi auth)
  refine ⟨blk, hb, ?_⟩
  rw [auth.2.2.2.2.time, ← ht]
  rfl

/-- **U5 over the mid history.** In the committed mid replay, every invocation `i`, at the state `sᵢ` its
prefix reaches, ran at its block's header timestamp, which is its recorded time; at that time the model's
`_A()` is the stored linear interpolation (from the ramp start on, when `future_A` is a word and the
source's one product does not overflow) and the final `future_A` once the ramp has ended; and an accepted
`ramp_A` step meets the source's guards. -/
theorem pool_mid_history_amp {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {start : Benv} {s₀ : State}
    {full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : some (start.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (start.state.getStor pool) s₀)
    (env : PoolMidEnv full trace pool s₀.coins s₀.token) :
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFramesMid pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      (∃ s, PoolRun s₀ invs s ∧ Checkpoint (future.state.getStor pool) s) ∧
      ∀ (pre : List PoolInvocation) (i : PoolInvocation) (post : List PoolInvocation)
        (sᵢ : State), invs = pre ++ i :: post → PoolRun s₀ pre sᵢ →
        ∃ blk : Block, (blk, i.frame) ∈ trace.blockFrames ∧
          i.env.time = blk.header.timestamp.toB256.toNat ∧
          (sᵢ.initialATime ≤ i.env.time → sᵢ.futureA < StableSwapNewton.wordSize →
            (max sᵢ.futureA sᵢ.initialA - min sᵢ.futureA sᵢ.initialA) *
              (i.env.time - sᵢ.initialATime) < StableSwapNewton.wordSize →
            aChk sᵢ i.env.time = some (aInterp sᵢ i.env.time)) ∧
          (sᵢ.futureATime ≤ i.env.time → aChk sᵢ i.env.time = some sᵢ.futureA) ∧
          ∀ fA fT, decodeCall i.frame.sevm = .rampA fA fT → ∃ o,
            step sᵢ i.env (decodeCall i.frame.sevm) = some o ∧
            o.state.initialATime + minRampTime ≤ o.state.futureATime ∧ 0 < o.state.futureA ∧
            o.state.futureA < maxA ∧ aChk sᵢ i.env.time = some o.state.initialA ∧
            o.state.futureA ≤ o.state.initialA * maxAChange ∧
            o.state.initialA ≤ o.state.futureA * maxAChange := by
  obtain ⟨-, invs, hobs, auth, -, s, run, -, hc, -⟩ := pool_mid_history trace installed initial env
  refine ⟨invs, hobs, auth, ⟨s, run, hc⟩, ?_⟩
  intro pre i post sᵢ hsplit hpre
  have hi : i ∈ invs := by
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  obtain ⟨blk, hb, ht⟩ := pool_mid_invocation_time hobs hi (auth i hi)
  obtain ⟨o, hstep, -, -⟩ := PoolRun.split (hsplit ▸ run) hpre
  refine ⟨blk, hb, ht, fun h1 h2 h3 => aChk_eq_aInterp h1 h2 h3, aChk_of_le, ?_⟩
  intro fA fT hdec
  rw [hdec] at hstep
  exact ⟨o, hdec ▸ hstep, rampA_guards (pool_step_rampA hstep)⟩

end Blanc.Lift.Curve3Pool
