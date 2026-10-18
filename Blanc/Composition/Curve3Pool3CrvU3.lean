import Blanc.Composition.Curve3PoolSupply
import Blanc.Lift.Curve3Pool.U3History

/-!
# U3 over the pool and 3Crv together (composed U3)

`pool_history_u3` (`Lift/Curve3Pool/U3History.lean`) states the six U3 bounds of goal §11 for every
replayed invocation, with `T` the supply the frame observed (`EnvOf.supply`, a named answer until
U8).  `pool_3crv_u3` states them over the joint history of `pool_3crv_history`, where that answer is
3Crv's ledger supply: for every invocation, `T` is 3Crv's supply word at the entry of the frame's
`totalSupply()` child (`SupplyObserved`), and 3Crv's supply word moves from the frame's entry to its
post by exactly the invocation's own minted and burned amounts.

What this does **not** state: that `T` is 3Crv's supply at the *frame's* entry, so that the model's
`supplyAfter T o.calls` is 3Crv's supply at the frame's post.  That needs the `totalSupply()` child
to precede the frame's token `CALL` children, an order fact of the bytecode that the frame's raw
effect (`RawEffect`: `EnvOf` names the child by index, `CallsOf` lists the calls) does not record.
-/

namespace Blanc.Composition.Curve3PoolSupply

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Crv Blanc.ExecutionTrace
open Blanc.Lift.Curve3Pool (PoolInvocation PoolRun poolSubtreeFrames)

open Blanc.Composition.Curve3Pool3CrvJoint in
/-- **Composed U3.**  Under `pool_3crv_history`'s premises, every replayed invocation ran at its
block's header time and is an accepted step with its raw effect satisfying the six U3 bounds, the
supply it observed is 3Crv's ledger supply at the entry of its `totalSupply()` child, and 3Crv's
supply word at its frame's post is the word at its entry moved by its own minted and burned
amounts. -/
theorem pool_3crv_u3 {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = Curve3Pool.poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : FreshKeys K₀ (historyTouchedKeys c3 trace))
    (env : Curve3Pool.PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress) :
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) =
        Curve3Pool.committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      (∃ s, PoolRun ps₀ invs s ∧ Curve3Pool.Checkpoint (future.state.getStor pool) s) ∧
      ∀ (pre : List PoolInvocation) (i : PoolInvocation) (post : List PoolInvocation)
        (sᵢ : Curve3Pool.State), invs = pre ++ i :: post → PoolRun ps₀ pre sᵢ →
        (∃ blk : Block, (blk, i.frame) ∈ trace.blockFrames ∧
          i.env.time = blk.header.timestamp.toB256.toNat) ∧
        ∃ o, Curve3Pool.step sᵢ i.env (Curve3Pool.decodeCall i.frame.sevm) = some o ∧
          Curve3Pool.RawEffect (Blanc.Exec.Frame.rootDeriv i.frame) i.frame.post i.env o ∧
          Curve3Pool.U3Step sᵢ i.env (Curve3Pool.decodeCall i.frame.sevm) o ∧
          SupplyObserved c3 i ∧
          supplyAt c3 i.frame.post.state + callsBurned o.calls =
            supplyAt c3 i.frame.pre.state + callsMinted o.calls := by
  obtain ⟨-, invs, obs, auth, s, run, -, hc, -, -, -, -, -, -, -, perStep⟩ :=
    pool_3crv_history trace poolInstalled c3Installed joint fresh env notSystem
  refine ⟨invs, obs, auth, ⟨s, run, hc⟩, ?_⟩
  intro pre i post sᵢ split hpre
  have hi : i ∈ invs := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨o, hstep, hraw, moved, observed⟩ := perStep pre i post sᵢ split hpre
  exact ⟨Curve3Pool.pool_invocation_time obs hi (auth i hi), o, hstep, hraw,
    Curve3Pool.u3Step_of_step hstep, observed, moved⟩

end Blanc.Composition.Curve3PoolSupply
