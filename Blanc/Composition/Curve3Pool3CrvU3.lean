import Blanc.Composition.Curve3PoolSupply
import Blanc.Lift.Curve3Pool.U3Ledger

/-!
# U3 over the pool and 3Crv together (composed U3)

`pool_history_u3` (`Lift/Curve3Pool/U3History.lean`) states the six U3 bounds of goal §11 for every
replayed invocation, with `T` the supply the frame observed (`EnvOf.supply`, a named answer until
U8) and `T' = supplyAfter T o.calls`.  `pool_3crv_u3` states them over the joint history of
`pool_3crv_history` at **3Crv's ledger supply**: `T` is 3Crv's supply word at the entry of the
invocation's frame and `T'` its supply word at the frame's post (`U3Ledger`), with no supply premise.

The pieces:

* the observed supply is 3Crv's supply at the frame's entry (`SupplyObserved`): the frame reads it
  from a `totalSupply()` child that precedes every state-changing token child (`EnvOf.supply`'s
  `SupplyFirst`), and every child before it keeps 3Crv's supply word;
* 3Crv's supply word moves across the frame by the step's own minted and burned word amounts
  (`pool_3crv_history`); the amounts are words and go one way (`step_moves`: the model's checked
  arithmetic, the observed supply being a word, the decoded amount being a calldata word), so
  `supplyAfter` from the entry supply is the post supply (`supplyAfter_of_moved`).

The admin-fee premise `admin_fee ≤ 10^10` of four bounds stays in `U3Ledger`; it holds at every
replayed state when it holds at the checkpoint state (`FeeBounded`, kept by every step; the
constructor does not assert it).
-/

namespace Blanc.Composition.Curve3PoolSupply

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Crv Blanc.ExecutionTrace
open Blanc.Lift.Curve3Pool (PoolInvocation PoolRun poolSubtreeFrames)

/-- Word amounts are counted as themselves. -/
theorem calls_word : ∀ cs : List Curve3Pool.ExtCall, Curve3Pool.MovesWord cs →
    callsMinted cs = Curve3Pool.mintedRaw cs ∧ callsBurned cs = Curve3Pool.burnedRaw cs
  | [], _ => ⟨rfl, rfl⟩
  | .mint _ v :: cs, h => by
    obtain ⟨ihm, ihb⟩ := calls_word cs h.2
    simp only [callsMinted, callsBurned] at ihm ihb ⊢
    simp only [List.map_cons, List.sum_cons, callMinted, callBurned, wordAmt,
      B256.toNat_toB256_of_lt h.1, Curve3Pool.mintedRaw, Curve3Pool.burnedRaw, ihm, ihb,
      Nat.zero_add, and_self]
  | .burn _ v :: cs, h => by
    obtain ⟨ihm, ihb⟩ := calls_word cs h.2
    simp only [callsMinted, callsBurned] at ihm ihb ⊢
    simp only [List.map_cons, List.sum_cons, callMinted, callBurned, wordAmt,
      B256.toNat_toB256_of_lt h.1, Curve3Pool.mintedRaw, Curve3Pool.burnedRaw, ihm, ihb,
      Nat.zero_add, and_self]
  | .pull _ _ _ :: cs, h => by
    obtain ⟨ihm, ihb⟩ := calls_word cs h
    simp only [callsMinted, callsBurned] at ihm ihb ⊢
    simp only [List.map_cons, List.sum_cons, callMinted, callBurned, Curve3Pool.mintedRaw,
      Curve3Pool.burnedRaw, ihm, ihb, Nat.zero_add, and_self]
  | .push _ _ _ :: cs, h => by
    obtain ⟨ihm, ihb⟩ := calls_word cs h
    simp only [callsMinted, callsBurned] at ihm ihb ⊢
    simp only [List.map_cons, List.sum_cons, callMinted, callBurned, Curve3Pool.mintedRaw,
      Curve3Pool.burnedRaw, ihm, ihb, Nat.zero_add, and_self]

/-- **The model's post supply is the ledger's**: a supply word moved by a call list's word amounts,
one way, is `supplyAfter` of the list from the starting word. -/
theorem supplyAfter_of_moved {pre post : Nat} {cs : List Curve3Pool.ExtCall}
    (moved : post + callsBurned cs = pre + callsMinted cs) (words : Curve3Pool.MovesWord cs)
    (oneWay : Curve3Pool.OneWay cs) : Curve3Pool.supplyAfter pre cs = post := by
  obtain ⟨hm, hb⟩ := calls_word cs words
  rw [hm, hb] at moved
  rcases oneWay with h0 | h0
  · rw [h0] at moved
    have e := Curve3Pool.supplyAfter_exact cs pre (by omega)
    rw [h0] at e
    omega
  · rw [h0] at moved
    have e := Curve3Pool.supplyAfter_exact cs pre (by rw [h0]; exact Nat.zero_le _)
    rw [h0] at e
    omega

open Blanc.Composition.Curve3Pool3CrvJoint in
/-- **Composed U3.**  Under `pool_3crv_history`'s premises, every replayed invocation ran at its
block's header time and is an accepted step with its raw effect, the supply it observed is 3Crv's
ledger supply at its frame's entry (`SupplyObserved`), the model's post supply `supplyAfter` from
that supply is 3Crv's ledger supply at its frame's post, and the six U3 bounds hold at those two
ledger supplies (`U3Ledger`).  The admin fees stay bounded along the replay when they are bounded at
the checkpoint state. -/
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
        (Curve3Pool.FeeBounded ps₀ → Curve3Pool.FeeBounded sᵢ) ∧
        ∃ o, Curve3Pool.step sᵢ i.env (Curve3Pool.decodeCall i.frame.sevm) = some o ∧
          Curve3Pool.RawEffect (Blanc.Exec.Frame.rootDeriv i.frame) i.frame.post i.env o ∧
          SupplyObserved c3 i ∧
          Curve3Pool.supplyAfter (supplyAt c3 i.frame.pre.state) o.calls =
            supplyAt c3 i.frame.post.state ∧
          Curve3Pool.U3Ledger sᵢ i.env (Curve3Pool.decodeCall i.frame.sevm) o
            (supplyAt c3 i.frame.pre.state) (supplyAt c3 i.frame.post.state) := by
  obtain ⟨-, invs, obs, auth, s, run, -, hc, -, -, -, -, -, -, -, perStep⟩ :=
    pool_3crv_history trace poolInstalled c3Installed joint fresh env notSystem
  refine ⟨invs, obs, auth, ⟨s, run, hc⟩, ?_⟩
  intro pre i post sᵢ split hpre
  have hi : i ∈ invs := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨o, hstep, hraw, moved, observed⟩ := perStep pre i post sᵢ split hpre
  have hT : ∀ T, i.env.supply = some T → T = supplyAt c3 i.frame.pre.state :=
    fun T h => (observed T h).1
  obtain ⟨words, oneWay⟩ := Curve3Pool.step_moves hstep
    (fun T h => by rw [hT T h]; exact B256.toNat_lt _)
    (fun a j m h => Curve3Pool.decodeCall_oneCoin_word h)
  have after := supplyAfter_of_moved moved words oneWay
  exact ⟨Curve3Pool.pool_invocation_time obs hi (auth i hi),
    fun h => PoolRun.keeps Curve3Pool.feeBounded_keeps hpre h, o, hstep, hraw, observed, after,
    Curve3Pool.u3Ledger_of_step hstep hT after⟩

end Blanc.Composition.Curve3PoolSupply
