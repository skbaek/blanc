import Blanc.Composition.Curve3Pool3CrvCoinExactExit
import Blanc.Composition.Curve3PoolCalleeFloorProfiles
import Blanc.Lift.Curve3Pool.RemoveLiquidityFloorFrame

/-!
# `remove_liquidity` with the real coins, at the true gas minimum

`pool_3crv_removeLiquidity_live_floor_coins`: `pool_3crv_removeLiquidity_live_exact_coins` for every residual `R ≥ 2201`,
at the same cost, in place of `R ≥ 690720`. The message-level form. The floor `2201` is `rl_lock_sentry`; every
call's floor (`4900` for the pushes and the burn) is below what the frame still has to spend at that call.
-/

namespace Blanc.Composition.Curve3Pool3CrvLiteralWitness

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.ExecutionTrace Blanc.StableSwapNewton
open Blanc.Composition.Curve3Pool3CrvJoint (JointCheckpoint)
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Composition.Curve3PoolCalleeExactProfiles
open Blanc.Composition.Curve3Pool3CrvHeadlines
open Blanc.Composition.Curve3Pool3CrvExactAssembly
open Blanc.Composition.Curve3Pool3CrvHeadlinesExact
open Blanc.Composition.Curve3Pool3CrvInstance
open Blanc.Lift.Usdc

section Chain

variable {sevm : Sevm} {pre : Devm} {c3 : Adr} {σ : Stor}

/-- What the coin chain reads ignores execution gas. -/
theorem pinsFrom_stable (k : Nat) : GasStable (C3With c3 σ (pinsFrom sevm pre k)) :=
  fun _ _ h hd => ⟨⟨(h.getCode_eq _).symm.trans hd.1.1, (h.getStor_eq _).symm.trans hd.1.2⟩,
    fun j hj => pin_keep (hd.2 j hj) (h.getStor_eq _).symm (fun a => (h.getCode_eq a).symm)⟩

variable {T : B256}

/-- **The three pushes at their floor.** -/
theorem exit_pushesF (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : 2 ≤ sevm.depth) (hC : RealCoins sevm pre) (htc : ∀ j : Fin 3, coinOf sevm pre j ≠ c3)
    (hf0 : Blanc.Lift.Dai.MoveFits (pre.getStor (coinOf sevm pre 0)) sevm.currentTarget sevm.caller
      (balAt (pre.getStor sevm.currentTarget) 0 * rlAmt sevm / T))
    (hf1 : UsdcLive.MoveFits (pre.getStor (coinOf sevm pre 1)) sevm.currentTarget sevm.caller
      (balAt (pre.getStor sevm.currentTarget) 1 * rlAmt sevm / T))
    (hf2 : Blanc.Lift.Usdt.XferFits (pre.getStor (coinOf sevm pre 2)) sevm.currentTarget sevm.caller
      (balAt (pre.getStor sevm.currentTarget) 2 * rlAmt sevm / T)) :
    ∀ i, i < 3 → MutableFloorProfile sevm (C3With c3 σ (pinsFrom sevm pre i)) (C3With c3 σ (pinsFrom sevm pre (i + 1)))
      (coinAt (pre.getStor sevm.currentTarget) i)
      (transferSel ++ sevm.caller.toB256.toBytes ++ (balAt (pre.getStor sevm.currentTarget) i * rlAmt sevm / T).toBytes)
      RawCallOk 104744 4900 0x520 0x44 0x5c0 (exitPushD sevm (pre.getStor sevm.currentTarget) i)
      (exitPushN sevm (pre.getStor sevm.currentTarget) i) := by
  intro i hi
  have hD : (2 : Nat) ≤ sevm.depth := hdepth
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · exact Blanc.Composition.Curve3PoolDai.dai_coinPushFloor (by decide) hfork hstatic (by omega) (hC.prec 0) (hC.pool 0)
      (by decide) (by decide) (pinsFrom_stable _) (by decide) (by decide)
      (fun b hb => ⟨((hb.2 0 (le_refl _)).1 _).trans hC.dai, by have e : b.getStor (coinAt (pre.getStor sevm.currentTarget) 0).toAdr = pre.getStor (coinOf sevm pre 0) := (hb.2 0 (le_refl _)).2; rw [e]; exact hf0⟩)
      (fun b d hb hl => pins_leave (k := 0) hC (htc 0) hb hl)
  · exact UsdcLive.usdc22_coinPushFloor (by decide) hfork hstatic hdepth (hC.prec 1) (hC.pool 1)
      (by decide) (by decide) (pinsFrom_stable _) (by decide) (by decide)
      (fun b hb => ⟨((hb.2 1 (le_refl _)).1 _).trans hC.usdc, proxyAt_pinned hC (hb.2 1 (le_refl _)),
        by have e : b.getStor (coinAt (pre.getStor sevm.currentTarget) 1).toAdr = pre.getStor (coinOf sevm pre 1) := (hb.2 1 (le_refl _)).2; rw [e]; exact hf1⟩)
      (fun b d hb hl => pins_leave (k := 1) hC (htc 1) hb hl)
  · exact Blanc.Composition.Curve3PoolUsdt.usdt_coinPushFloor (by decide) hfork hstatic (by omega) (hC.prec 2) (hC.pool 2)
      (by decide) (by decide) (pinsFrom_stable _) (by decide) (by decide)
      (fun b hb => ⟨((hb.2 2 (le_refl _)).1 _).trans hC.usdt, by have e : b.getStor (coinAt (pre.getStor sevm.currentTarget) 2).toAdr = pre.getStor (coinOf sevm pre 2) := (hb.2 2 (le_refl _)).2; rw [e]; exact hC.live,
        by have e : b.getStor (coinAt (pre.getStor sevm.currentTarget) 2).toAdr = pre.getStor (coinOf sevm pre 2) := (hb.2 2 (le_refl _)).2; rw [e]; exact hf2⟩)
      (fun b d hb hl => pins_leave (k := 2) hC (htc 2) hb hl)

/-- **`remove_liquidity`'s floor premises from 3Crv's code.** -/
theorem rlFloorPremises_c3crv {V : Nat → Devm → Prop} {pushD : Nat → Devm → List B256 → Mem → Nat}
    {pushN : Nat → Devm → List B256 → Mem → Devm}
    (ht : (tokW sevm pre).toAdr = c3) (hne : sevm.currentTarget ≠ c3)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (htok : ¬ sevm.benvStat.rules.isPrecomp c3)
    (hT : (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T)
    (hburn : BurnFits (Devm.getStor pre c3) sevm.currentTarget sevm.caller.toB256 (rlAmt sevm))
    (hVs : ∀ k, C3Blind c3 (V k))
    (hVst : ∀ k σ', GasStable (C3With c3 σ' (V k)))
    (hpush : ∀ i, i < 3 → MutableFloorProfile sevm (C3With c3 (Devm.getStor pre c3) (V i))
      (C3With c3 (Devm.getStor pre c3) (V (i + 1))) (coinAt (pre.getStor sevm.currentTarget) i)
      (transferSel ++ sevm.caller.toB256.toBytes ++
        (balAt (pre.getStor sevm.currentTarget) i * rlAmt sevm / T).toBytes)
      RawCallOk 104744 4900 0x520 0x44 0x5c0 (pushD i) (pushN i)) :
    RLFloorPremises sevm pre T (rlC3W c3 (Devm.getStor pre c3)
      (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (rlAmt sevm)) V) 104744
      (rlC3Calls sevm pre pushD pushN) := by
  refine ⟨?_, fun b S M _ _ => supplyDebit_le (by decide) (by decide) b S M, fun i hi => ?_, ?_⟩
  · exact c3crv_supplyFloor (by decide) hfork hdepth (by rw [ht]; exact precomp_false htok) (by decide) (by decide)
      (hVst 0 _) (by decide) (by decide) (fun b hb => by rw [ht, hb.1.2]; exact ⟨hb.1.1, hT⟩)
      (fun b d hb hs hc => c3With_keep (hVs 0) hb hs hc)
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hpush 0 (by decide)
    · exact hpush 1 (by decide)
    · exact hpush 2 (by decide)
  · refine c3crv_burnFloor (by decide) hfork hstatic hdepth (by rw [ht]; exact precomp_false htok) (by decide)
      (by decide) (hVst 3 _) (by decide) (by decide) ?_ ?_
    · intro b hb
      rw [ht, hb.1.2]
      exact ⟨hb.1.1, fun h => hne h.symm, hburn⟩
    · rw [ht]
      exact fun b d hb ho hs hc => ⟨c3At_burn hb.1 hs hc, hVs 3 b d hb.2 ho hc⟩

end Chain

section Headline

variable {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop}

/-- **`remove_liquidity` with the real coins, at the true minimum**: as `pool_3crv_removeLiquidity_live_exact_coins`,
for every `R ≥ 2201`. -/
theorem pool_3crv_removeLiquidity_live_floor_coins
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state)
    {T : B256} (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : 2 ≤ (initSevm msg).depth)
    (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hcoins : RealCoins (initSevm msg) (initDevm msg))
    (hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256 (rlAmt (initSevm msg)))
    (hf0 : Blanc.Lift.Dai.MoveFits ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 0))
      msg.currentTarget msg.caller (balAt ((initDevm msg).getStor msg.currentTarget) 0 * rlAmt (initSevm msg) / T))
    (hf1 : UsdcLive.MoveFits ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 1))
      msg.currentTarget msg.caller (balAt ((initDevm msg).getStor msg.currentTarget) 1 * rlAmt (initSevm msg) / T))
    (hf2 : Blanc.Lift.Usdt.XferFits ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 2))
      msg.currentTarget msg.caller (balAt ((initDevm msg).getStor msg.currentTarget) 2 * rlAmt (initSevm msg) / T)) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∀ {o : Out}
        (_hcode : (initSevm msg).code = code)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidity)
        (_hstep : step s (rlEnv (initSevm msg) T) (decodeCall (initSevm msg)) = some o)
        (_hid : IdReady (initSevm msg) (initDevm msg)),
        ∀ R, 2201 ≤ R →
          R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg)
            (exitPushD (initSevm msg) ((initDevm msg).getStor msg.currentTarget))
            (exitPushN (initSevm msg) ((initDevm msg).getStor msg.currentTarget))) < 2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg)
              (exitPushD (initSevm msg) ((initDevm msg).getStor msg.currentTarget))
              (exitPushN (initSevm msg) ((initDevm msg).getStor msg.currentTarget))))))
              (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg)
              (exitPushD (initSevm msg) ((initDevm msg).getStor msg.currentTarget))
              (exitPushN (initSevm msg) ((initDevm msg).getStor msg.currentTarget)))))) (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg)
              (exitPushD (initSevm msg) ((initDevm msg).getStor msg.currentTarget))
              (exitPushN (initSevm msg) ((initDevm msg).getStor msg.currentTarget))))))
              (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg)
              (exitPushD (initSevm msg) ((initDevm msg).getStor msg.currentTarget))
              (exitPushN (initSevm msg) ((initDevm msg).getStor msg.currentTarget)))))) (.ok post),
            exec (initEvm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg)
              (exitPushD (initSevm msg) ((initDevm msg).getStor msg.currentTarget))
              (exitPushN (initSevm msg) ((initDevm msg).getStor msg.currentTarget)))))) =
              .ok post ∧
            post.gasLeft = R ∧
            RawEffect ⟨0, _, _, .ok post, exc⟩ post (rlEnv (initSevm msg) T) o ∧
            Checkpoint (post.getStor msg.currentTarget) o.state := by
  have ready := c3Ready_of_history trace poolInstalled c3Installed joint fresh env notSystem
    (pre := initDevm msg) state
  obtain ⟨-, s, hs, hck⟩ := pool_history_reached (sevm := initSevm msg) (pre := initDevm msg)
    trace poolInstalled joint.poolCk env target state
  refine ⟨s, hs, ready, ?_⟩
  intro o hcode hlen hcd hsel hstep hid
  have ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  have hpc := pool_code_ne_of_history (sevm := initSevm msg) (pre := initDevm msg) trace
    poolInstalled joint env target state
  have hne : (initSevm msg).currentTarget ≠ c3 := by
    show msg.currentTarget ≠ c3
    rw [target]; exact joint.apart
  subst ht
  have hdep0 : (initSevm msg).depth ≠ 0 := by omega
  have hpush := exit_pushesF (c3 := tokOf (initSevm msg) (initDevm msg))
    (σ := Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg))) (T := T)
    hfork hstatic hdepth hcoins hcoins.tok hf0 hf1 hf2
  subst target
  exact removeLiquidity_msg_floor _ hcode hfork hstatic hdep0 hlen hcd hsel hck hstep hc3.prec hcoins.prec hpc hid
    (fun k hk => by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
      all_goals exact c3With_wClosed hne (pinsFrom_wClosed hcoins _))
    ⟨⟨ready.1, rfl⟩, pinsFrom_entry 0⟩
    (rlFloorPremises_c3crv rfl hne hfork hstatic hdep0 hc3.prec hc3.supply hburn (pinsFrom_blind hcoins.tok)
      (fun k _ => pinsFrom_stable k) hpush)

end Headline

end Blanc.Composition.Curve3Pool3CrvLiteralWitness
