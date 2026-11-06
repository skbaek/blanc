import Blanc.Composition.Curve3Pool3CrvU3
import Blanc.Composition.Curve3PoolSupplyMid
import Blanc.Lift.Curve3Pool.AmpHistoryMid

/-!
# U3 over the pool and 3Crv together, past the minter cut, at historical forks

`pool_3crv_u3` (`Curve3Pool3CrvU3.lean`) over the walk of `pool_3crv_mid_history`:

* `pool_3crv_mid_u3` — every replayed invocation of a `MidHistoryTraceIn HistFork` ran at its block's
  header time and is an accepted step with its raw effect, and the six U3 bounds hold at 3Crv's ledger
  supplies at its frame's entry and post (`U3Ledger`), under the premises of `pool_3crv_mid_history`;
* `joint_mid_u3` — the same from `JointDeployment`'s minter cut, where the admin-fee side condition holds
  outright (`feeBounded_of_poolRun_init`).

The refutation companions (`U3Refute.lean`, `U4ExactnessRefute.lean`, `U4GetYRefute.lean`) are about the
model and are untouched here; they are not realised over a configured history.
-/

namespace Blanc.Composition.Curve3PoolSupply

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Crv Blanc.ExecutionTrace
open Blanc.Lift.Curve3Pool (PoolInvocation PoolRun poolSubtreeFrames)
open Blanc.Composition.Curve3Pool3CrvJoint (JointCheckpoint)

/-- **Composed U3 over a historical mid history.** Under `pool_3crv_mid_history`'s premises, every
replayed invocation ran at its block's header time and is an accepted step with its raw effect, the
supply it observed is 3Crv's ledger supply at its frame's entry (`SupplyObserved`), the model's post
supply `supplyAfter` from that supply is 3Crv's ledger supply at its frame's post, and the six U3 bounds
hold at those two ledger supplies (`U3Ledger`). The admin fees stay bounded along the replay when they
are bounded at the checkpoint state. -/
theorem pool_3crv_mid_u3 {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {start : Benv} {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Key → Prop}
    {full : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (poolInstalled : some (start.state.getCode pool).toList = Curve3Pool.poolSem.image)
    (c3Installed : some (start.state.getCode c3).toList = c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ start.state)
    (fresh : FreshKeys K₀ (midTouchedKeysIn c3 trace))
    (env : Curve3Pool.PoolMidEnv full trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress) :
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) =
        Curve3Pool.committedPoolFramesMid pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      (∃ s, PoolRun ps₀ invs s ∧ Curve3Pool.Checkpoint (future.state.getStor pool) s) ∧
      ∀ (pre : List PoolInvocation) (i : PoolInvocation) (post : List PoolInvocation)
        (sᵢ : Curve3Pool.State), invs = pre ++ i :: post → PoolRun ps₀ pre sᵢ →
        (∃ blk : Block, (blk, i.frame) ∈ trace.blockFrames ∧
          i.env.time = blk.header.timestamp.toB256.toNat) ∧
        (Curve3Pool.FeeBounded ps₀ → Curve3Pool.FeeBounded sᵢ) ∧
        ∃ o, Curve3Pool.step sᵢ i.env (Curve3Pool.decodeCall i.frame.sevm) = some o ∧
          Curve3Pool.RawEffect (Blanc.Exec.Frame.rootDeriv i.frame) i.frame.post i.env o ∧
          SupplyObserved c3 i ∧
          Curve3Pool.supplyAfter (supplyAt c3 i.frame.pre.state) o.calls =
            supplyAt c3 i.frame.post.state ∧
          Curve3Pool.U3Ledger sᵢ i.env (Curve3Pool.decodeCall i.frame.sevm) o
            (supplyAt c3 i.frame.pre.state) (supplyAt c3 i.frame.post.state) := by
  obtain ⟨-, -, invs, obs, auth, s, run, -, hc, -, -, -, -, -, -, -, perStep⟩ :=
    pool_3crv_mid_history trace poolInstalled c3Installed joint fresh env notSystem
  refine ⟨invs, obs, auth, ⟨s, run, hc⟩, ?_⟩
  intro pre i post sᵢ split hpre
  have hi : i ∈ invs := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨o, hstep, hraw, moved, observed⟩ := perStep pre i post sᵢ split hpre
  obtain ⟨after, ledger⟩ := u3Ledger_of_moved hstep moved observed
  exact ⟨Curve3Pool.pool_mid_invocation_time obs hi (auth i hi),
    fun h => PoolRun.keeps Curve3Pool.feeBounded_keeps hpre h, o, hstep, hraw, observed, after, ledger⟩

open Blanc.Composition.Curve3PoolJointRoot in
/-- **Composed U3 from the joint deployment, past the minter cut.** Over any historical mid history
starting right after the minter assignment of a `JointDeployment`, under its `PoolMidEnv` at the
constructor's coins and token and 3Crv's collision premise at the keys tracked at the cut: the checkpoint's
states are the replays `joint_root_replay` gives, and from them every replayed invocation ran at its
block's header time, with `admin_fee ≤ 10^10` outright, and the six U3 bounds hold at 3Crv's ledger
supplies. -/
theorem joint_mid_u3 (j : JointDeployment) {checkpoint future : BlockChain}
    {full : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future}
    (trace : MidHistoryTraceIn HistFork mainnetChainConfig j.minterCut.afterBenv future)
    (fresh : FreshKeys j.c3Keys (midTouchedKeysIn Curve3Crv.Creation.tokenAddress trace))
    (env : Curve3Pool.PoolMidEnv full trace Curve3Pool.Creation.poolAddress
      Curve3Pool.Creation.coinsN Curve3Pool.Creation.tokenN) :
    ∃ (invs₀ : List PoolInvocation) (ps : Curve3Pool.State) (cs : Blanc.Curve3Crv.State),
      invs₀.flatMap (fun i => poolSubtreeFrames Curve3Pool.Creation.poolAddress i.frame) =
        j.poolFrames ∧
      PoolRun (Curve3Pool.Creation.poolInitState Curve3Pool.Creation.deployTime.toNat) invs₀ ps ∧
      InvRunBy OwnerAnswerH (Curve3Crv.Creation.curveDeployedState Curve3Crv.Creation.deployer)
        j.c3Invocations cs ∧
      JointCheckpoint Curve3Pool.Creation.poolAddress Curve3Crv.Creation.tokenAddress ps cs j.c3Keys
        j.cutState ∧
      ∃ invs : List PoolInvocation,
        invs.flatMap (fun i => poolSubtreeFrames Curve3Pool.Creation.poolAddress i.frame) =
          Curve3Pool.committedPoolFramesMid Curve3Pool.Creation.poolAddress trace ∧
        (∀ i ∈ invs, i.Authentic Curve3Pool.Creation.poolAddress) ∧
        (∃ s, PoolRun ps invs s ∧
          Curve3Pool.Checkpoint (future.state.getStor Curve3Pool.Creation.poolAddress) s) ∧
        ∀ (pre : List PoolInvocation) (i : PoolInvocation) (post : List PoolInvocation)
          (sᵢ : Curve3Pool.State), invs = pre ++ i :: post → PoolRun ps pre sᵢ →
          (∃ blk : Block, (blk, i.frame) ∈ trace.blockFrames ∧
            i.env.time = blk.header.timestamp.toB256.toNat) ∧
          sᵢ.adminFee ≤ Curve3Pool.feeDen ∧
          ∃ o, Curve3Pool.step sᵢ i.env (Curve3Pool.decodeCall i.frame.sevm) = some o ∧
            Curve3Pool.RawEffect (Blanc.Exec.Frame.rootDeriv i.frame) i.frame.post i.env o ∧
            SupplyObserved Curve3Crv.Creation.tokenAddress i ∧
            Curve3Pool.supplyAfter (supplyAt Curve3Crv.Creation.tokenAddress i.frame.pre.state)
                o.calls = supplyAt Curve3Crv.Creation.tokenAddress i.frame.post.state ∧
            Curve3Pool.U3Ledger sᵢ i.env (Curve3Pool.decodeCall i.frame.sevm) o
              (supplyAt Curve3Crv.Creation.tokenAddress i.frame.pre.state)
              (supplyAt Curve3Crv.Creation.tokenAddress i.frame.post.state) := by
  obtain ⟨poolCode, c3Code, invs₀, ps, cs, obs₀, -, -, run₀, -, c3Run, joint⟩ := joint_root_replay j
  have hps := run₀.coins_token
  have envAt : Curve3Pool.PoolMidEnv full trace Curve3Pool.Creation.poolAddress ps.coins ps.token := by
    rw [hps.1, hps.2]
    exact env
  obtain ⟨invs, obs, auth, run, per⟩ :=
    pool_3crv_mid_u3 trace poolCode c3Code joint fresh envAt (by decide)
  refine ⟨invs₀, ps, cs, obs₀, run₀, c3Run, joint, invs, obs, auth, run, ?_⟩
  intro pre i post sᵢ split hpre
  obtain ⟨time, fee, rest⟩ := per pre i post sᵢ split hpre
  exact ⟨time, (fee (Curve3Pool.feeBounded_of_poolRun_init run₀)).le_feeDen, rest⟩

end Blanc.Composition.Curve3PoolSupply
