import Blanc.Lift.Curve3Pool.History
import Blanc.Lift.Curve3Pool.U5
import Blanc.ExecutionHistoryFrameTime

/-!
# Curve 3pool: the amplification coefficient over the committed history (U5, design §3.3)

Every invocation of the committed replay (`pool_history_committed_env`) is a settled frame of the
trace, so it ran at the header timestamp of the block that retained it
(`ConfiguredHistoryTrace.settledFrames_time`), and its recorded environment's time is that
timestamp (`EnvOf.time`).  At the state the replay reaches before it, the model's `_A()` is the
stored linear interpolation at that header time (`aChk_eq_aInterp`), the final `future_A` once the
ramp has ended (`aChk_of_le`), and an accepted `ramp_A` step satisfies the source's guards
(`rampA_guards`).

* `pool_invocation_settled`, `pool_invocation_time` — an authentic invocation of the replay is a
  settled frame, at its block's header timestamp;
* `pool_history_amp` — the U5 headline at history level;
* `pool_invocation_time_ne_parent` — the control: the timestamp is the header's, never the parent
  block's.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.ExecutionTrace

/-- A frame is its own first committed frame. -/
theorem pool_frame_mem_committedFrames (f : Exec.Frame) : f ∈ Exec.committedFrames f.run := by
  unfold Exec.committedFrames
  rw [dite_eq_left_of_eq_true (eq_true f.committed)]
  exact List.mem_cons_self ..

/-- **An authentic invocation of the replay is a settled frame of the trace.** -/
theorem pool_invocation_settled {pool : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {trace : ConfiguredHistoryTrace cfg checkpoint future}
    {invs : List PoolInvocation}
    (hobs : invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace)
    {i : PoolInvocation} (hi : i ∈ invs) (auth : i.Authentic pool) :
    i.frame ∈ trace.settledFrames := by
  have hself : i.frame ∈ poolSubtreeFrames pool i.frame := by
    unfold poolSubtreeFrames
    refine List.mem_flatMap.mpr ⟨i.frame, pool_frame_mem_committedFrames i.frame, ?_⟩
    unfold poolFrameObs
    simp only [auth.2.2.1, auth.2.2.2.1, and_self, ↓reduceIte, List.mem_singleton]
  have hmem : i.frame ∈ committedPoolFrames pool trace := hobs ▸ List.mem_flatMap.mpr ⟨i, hi, hself⟩
  obtain ⟨f, hf, hfo⟩ := List.mem_flatMap.mp hmem
  unfold poolFrameObs at hfo
  split at hfo
  · rw [List.mem_singleton] at hfo
    rw [hfo]
    exact hf
  · exact absurd hfo List.not_mem_nil

/-- **An authentic invocation ran at its block's header timestamp**, and its recorded time is that
timestamp. -/
theorem pool_invocation_time {pool : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {trace : ConfiguredHistoryTrace cfg checkpoint future}
    {invs : List PoolInvocation}
    (hobs : invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace)
    {i : PoolInvocation} (hi : i ∈ invs) (auth : i.Authentic pool) :
    ∃ blk : Block, (blk, i.frame) ∈ trace.blockFrames ∧
      i.env.time = blk.header.timestamp.toB256.toNat := by
  obtain ⟨blk, hb, ht⟩ := trace.settledFrames_time _ (pool_invocation_settled hobs hi auth)
  refine ⟨blk, hb, ?_⟩
  rw [auth.2.2.2.2.time, ← ht]
  rfl

/-- An accepted `ramp_A` step is the body's `rampA`. -/
theorem pool_step_rampA {s : State} {e : Env} {fA fT : Nat} {o : Out}
    (h : step s e (.rampA fA fT) = some o) : rampA s e fA fT = some o := by
  have h' : (if e.value = 0 then rampA s e fA fT else none) = some o := h
  split at h'
  · exact h'
  · exact absurd h' (by simp only [reduceCtorEq, not_false_eq_true])

/-- **U5 at history level.**  In the committed replay of `pool_history_committed_env`, every
invocation `i`, at the state `sᵢ` its prefix reaches, ran at its block's header timestamp, which is
its recorded time; at that time the model's `_A()` is the stored linear interpolation (from the
ramp start on, when `future_A` is a word and the source's one product does not overflow) and the
final `future_A` once the ramp has ended; and an accepted `ramp_A` step meets the source's guards. -/
theorem pool_history_amp {pool : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {s₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀)
    (env : PoolTraceEnv trace pool s₀.coins s₀.token) :
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
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
  obtain ⟨-, invs, hobs, auth, s, run, -, hc, -⟩ :=
    pool_history_committed_env trace installed initial env
  refine ⟨invs, hobs, auth, ⟨s, run, hc⟩, ?_⟩
  intro pre i post sᵢ hsplit hpre
  have hi : i ∈ invs := by
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  obtain ⟨blk, hb, ht⟩ := pool_invocation_time hobs hi (auth i hi)
  obtain ⟨o, hstep, -, -⟩ := PoolRun.split (hsplit ▸ run) hpre
  refine ⟨blk, hb, ht, fun h1 h2 h3 => aChk_eq_aInterp h1 h2 h3, aChk_of_le, ?_⟩
  intro fA fT hdec
  rw [hdec] at hstep
  exact ⟨o, hdec ▸ hstep, rampA_guards (pool_step_rampA hstep)⟩

/-- **The control: the recorded time is the header's, not the parent block's.**  A settled frame of
a configured block whose timestamp is a word, recorded with any environment it observed, never
carries the parent block's timestamp: substituting it in `pool_invocation_time` is refuted. -/
theorem pool_invocation_time_ne_parent {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTrace cfg pre post) {parent : Block}
    (head : pre.blocks.getLast? = some parent)
    (bound : block.block.header.timestamp < 2 ^ 256)
    {frame : Exec.Frame} (member : frame ∈ block.settledFrames) {e : Env}
    (henv : EnvOf (Exec.Frame.rootDeriv frame) e) :
    e.time ≠ parent.header.timestamp.toB256.toNat := by
  intro h
  rw [henv.time] at h
  exact block.settledFrame_time_ne_parent head bound member (B256.toNat_inj _ _ h)

end Blanc.Lift.Curve3Pool
