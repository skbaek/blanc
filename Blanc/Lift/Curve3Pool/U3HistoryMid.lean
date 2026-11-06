import Blanc.Lift.Curve3Pool.U3History
import Blanc.Lift.Curve3Pool.AmpHistoryMid

/-!
# Curve 3pool: the U3 bounds over the committed mid history at historical forks

`pool_history_u3` over `pool_mid_history`. The six bounds are the model's (`u3Step_of_step`); only the
history they are read along changes. An invocation's recorded time is the header timestamp of the block
that retained it (`pool_mid_invocation_time`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.ExecutionTrace

/-- **U3 along the mid history.** Every invocation of the replay, at the state its prefix reaches,
ran at its block's header timestamp, which is its recorded time, and is an accepted step with its raw
effect, whose result satisfies the six U3 bounds. -/
theorem pool_mid_history_u3 {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
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
        (∃ blk : Block, (blk, i.frame) ∈ trace.blockFrames ∧
          i.env.time = blk.header.timestamp.toB256.toNat) ∧
        ∃ o, step sᵢ i.env (decodeCall i.frame.sevm) = some o ∧
          RawEffect (Exec.Frame.rootDeriv i.frame) i.frame.post i.env o ∧
          U3Step sᵢ i.env (decodeCall i.frame.sevm) o := by
  obtain ⟨-, invs, hobs, auth, -, s, run, -, hc, -⟩ := pool_mid_history trace installed initial env
  refine ⟨invs, hobs, auth, ⟨s, run, hc⟩, ?_⟩
  intro pre i post sᵢ hsplit hpre
  have hi : i ∈ invs := by
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  obtain ⟨o, hstep, hraw, -⟩ := PoolRun.split (hsplit ▸ run) hpre
  exact ⟨pool_mid_invocation_time hobs hi (auth i hi), o, hstep, hraw, u3Step_of_step hstep⟩

end Blanc.Lift.Curve3Pool
