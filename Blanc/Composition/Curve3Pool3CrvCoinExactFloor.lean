import Blanc.Composition.Curve3Pool3CrvCoinExactSwap
import Blanc.Composition.Curve3PoolCalleeFloorProfiles
import Blanc.Lift.Curve3Pool.RemoveLiquidityFloorFrame
import Blanc.Lift.Curve3Pool.ExchangeFloorFrame

/-!
# `remove_liquidity` and `exchange` with the real coins, at the true gas minimum

`pool_3crv_removeLiquidity_live_floor_coins`: `pool_3crv_removeLiquidity_live_exact_coins` for every residual `R ≥ 2201`,
at the same cost, in place of `R ≥ 690720`. The message-level form. The floor `2201` is `rl_lock_sentry`; every
call's floor (`4900` for the pushes and the burn) is below what the frame still has to spend at that call.
`pool_3crv_exchange_live_floor_coins` likewise; its push's floor is `4650`, its pull's `5850`.
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

section Swap

variable {sevm : Sevm} {pre : Devm} {i j : Fin 3} {v : B256}

/-- What `exchange`'s world before the pull reads ignores execution gas. -/
theorem swapW0_stable : GasStable (swapW0 sevm pre i j) :=
  fun _ _ h hd => ⟨pin_keep hd.1 (h.getStor_eq _).symm (fun a => (h.getCode_eq a).symm),
    pin_keep hd.2 (h.getStor_eq _).symm (fun a => (h.getCode_eq a).symm)⟩

/-- What `exchange`'s world after the pull reads ignores execution gas. -/
theorem swapW1_stable : GasStable (swapW1 sevm pre i j) :=
  fun _ _ h hd => ⟨fun a => (h.getCode_eq a).symm.trans (hd.1 a), (h.getStor_eq _).symm.trans hd.2.1,
    pin_keep hd.2.2 (h.getStor_eq _).symm (fun a => (h.getCode_eq a).symm)⟩

/-- **`exchange_live_floor`'s premises with the real coins.** For `i ≠ j`, ledgers covering the pull of `exDx` and the
push of `v`, and a pulled USDT still undeprecated: the world chain's closure, the two balance reads when USDT is pulled,
the pull and the push, each at its floor, with `swapCalls`' debit and successor. -/
theorem exchange_coins_floor (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : 2 ≤ sevm.depth) (hC : RealCoins sevm pre) (hij : i ≠ j)
    (hpf : PullFitsK i (pre.getStor (coinOf sevm pre i)) sevm.caller sevm.currentTarget (exDx sevm))
    (hqf : PushFitsK j (pre.getStor (coinOf sevm pre j)) sevm.currentTarget sevm.caller v)
    (hlive : i = 2 → Blanc.Lift.Usdt.NotDeprecated
      (pulledK i (pre.getStor (coinOf sevm pre i)) sevm.caller sevm.currentTarget (exDx sevm))) :
    WClosed sevm (swapW0 sevm pre i j) ∧ WClosed sevm (swapW1 sevm pre i j) ∧ swapW0 sevm pre i j pre ∧
      WClosed sevm (fun _ => True) ∧
      (i = feeIndex →
        StaticWordFloorProfile sevm (swapW0 sevm pre i j) (swapW0 sevm pre i j)
          ((pre.getStor sevm.currentTarget).get (coinSlot i)) (balanceOfData sevm.currentTarget)
          (swapB1 sevm pre i) 129555 1000 0x3dc 0x24 0x440 (swapCalls sevm pre i j).balD1 (swapCalls sevm pre i j).balN1 ∧
        (∀ b S M, swapW0 sevm pre i j b → (M.read (0x3dc : B256).toNat (0x24 : B256).toNat).1 = balanceOfData sevm.currentTarget →
          (swapCalls sevm pre i j).balD1 b S M ≤ 8047) ∧
        StaticWordFloorProfile sevm (swapW1 sevm pre i j) (swapW1 sevm pre i j)
          ((pre.getStor sevm.currentTarget).get (coinSlot i)) (balanceOfData sevm.currentTarget)
          (swapB2 sevm pre i) 129555 1000 0x71c 0x24 0x780 (swapCalls sevm pre i j).balD2 (swapCalls sevm pre i j).balN2 ∧
        (∀ b S M, swapW1 sevm pre i j b → (M.read (0x71c : B256).toNat (0x24 : B256).toNat).1 = balanceOfData sevm.currentTarget →
          (swapCalls sevm pre i j).balD2 b S M ≤ 8047)) ∧
      MutableFloorProfile sevm (swapW0 sevm pre i j) (swapW1 sevm pre i j)
        ((pre.getStor sevm.currentTarget).get (coinSlot i))
        (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++ (exDx sevm).toBytes)
        RawCallOk 129555 5850 0x600 0x64 0x6c0 (swapCalls sevm pre i j).pullD (swapCalls sevm pre i j).pullN ∧
      MutableFloorProfile sevm (swapW1 sevm pre i j) (fun _ => True)
        ((pre.getStor sevm.currentTarget).get (coinSlot j))
        (transferSel ++ sevm.caller.toB256.toBytes ++ v.toBytes) RawCallOk 129555 4650 0xb60 0x44 0xc00
        (swapCalls sevm pre i j).pushD (swapCalls sevm pre i j).pushN := by
  have hcji : coinOf sevm pre j ≠ coinOf sevm pre i := hC.apart j i (Ne.symm hij)
  have hdep0 : sevm.depth ≠ 0 := by omega
  have keep0 : ∀ b d, swapW0 sevm pre i j b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → swapW0 sevm pre i j d :=
    fun b d hb hs hc => ⟨pin_keep hb.1 (hs _) hc, pin_keep hb.2 (hs _) hc⟩
  have keep1 : ∀ b d, swapW1 sevm pre i j b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
      (∀ a, d.getCode a = b.getCode a) → swapW1 sevm pre i j d :=
    fun b d hb hs hc => ⟨fun a => (hc a).trans (hb.1 a), (hs _).trans hb.2.1, pin_keep hb.2.2 (hs _) hc⟩
  have leave : ∀ {b d : Devm} {R : Prop},
      swapW0 sevm pre i j b →
      CoinLeaves (coinOf sevm pre i) (pulledK i (b.getStor (coinOf sevm pre i)) sevm.caller sevm.currentTarget (exDx sevm)) R b d →
      swapW1 sevm pre i j d := by
    intro b d R hb hl
    have e := hb.1.2
    refine ⟨fun a => (hl.code a).trans (hb.1.1 a), ?_, pin_keep hb.2 (hl.other _ hcji) hl.code⟩
    rw [hl.stor, e]
  refine ⟨WClosed.of_foreign fun b d hb hs hc =>
      ⟨pin_keep hb.1 (hs _ (hC.pool i)) hc, pin_keep hb.2 (hs _ (hC.pool j)) hc⟩,
    WClosed.of_foreign fun b d hb hs hc =>
      ⟨fun a => (hc a).trans (hb.1 a), (hs _ (hC.pool i)).trans hb.2.1, pin_keep hb.2.2 (hs _ (hC.pool j)) hc⟩,
    ⟨⟨fun _ => rfl, rfl⟩, ⟨fun _ => rfl, rfl⟩⟩,
    WClosed.of_foreign fun _ _ _ _ _ => trivial, ?_, ?_, ?_⟩
  · intro hfee
    have hi2 : i = 2 := hfee
    subst hi2
    refine ⟨Blanc.Composition.Curve3PoolUsdt.usdt_coinBalFloor (by decide) hfork hdep0 (hC.prec 2) (by decide) (by decide)
        swapW0_stable (by decide) (by decide) (fun b hb => ?_) (fun b d hb hs hc => keep0 b d hb hs hc),
      fun b S M _ _ => Blanc.Composition.Curve3PoolUsdt.usdt_balDebit_le (by decide) (by decide) b S M,
      Blanc.Composition.Curve3PoolUsdt.usdt_coinBalFloor (by decide) hfork hdep0 (hC.prec 2) (by decide) (by decide)
        swapW1_stable (by decide) (by decide) (fun b hb => ?_) (fun b d hb hs hc => keep1 b d hb hs hc),
      fun b S M _ _ => Blanc.Composition.Curve3PoolUsdt.usdt_balDebit_le (by decide) (by decide) b S M⟩
    · have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 2)).toAdr = pre.getStor (coinOf sevm pre 2) := hb.1.2
      exact ⟨(hb.1.1 _).trans hC.usdt, by rw [e]; exact hC.live, by rw [e]⟩
    · have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 2)).toAdr =
          pulledK 2 (pre.getStor (coinOf sevm pre 2)) sevm.caller sevm.currentTarget (exDx sevm) := hb.2.1
      exact ⟨(hb.1 _).trans hC.usdt, by rw [e]; exact hlive rfl, by rw [e]⟩
  · show MutableFloorProfile _ _ _ _ _ _ _ _ _ _ _ (swapPullD sevm _ i) (swapPullN sevm _ i)
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) i with rfl | rfl | rfl
    · exact Blanc.Composition.Curve3PoolDai.dai_coinPullFloor (by decide) hfork hstatic hdep0 (hC.prec 0) (hC.pool 0)
        (by decide) (by decide) swapW1_stable (by decide) (by decide)
        (fun b hb => ⟨(hb.1.1 _).trans hC.dai, by
          have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 0)).toAdr = pre.getStor (coinOf sevm pre 0) := hb.1.2
          rw [e]; exact hpf⟩)
        (fun b d hb hl => leave hb hl)
    · exact UsdcLive.usdc22_coinPullFloor (by decide) hfork hstatic hdepth (hC.prec 1) (hC.pool 1)
        (by decide) (by decide) swapW1_stable (by decide) (by decide)
        (fun b hb => ⟨(hb.1.1 _).trans hC.usdc, proxyAt_pinned hC hb.1, by
          have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 1)).toAdr = pre.getStor (coinOf sevm pre 1) := hb.1.2
          rw [e]; exact hpf⟩)
        (fun b d hb hl => leave hb hl)
    · exact Blanc.Composition.Curve3PoolUsdt.usdt_coinPullFloor (by decide) hfork hstatic hdep0 (hC.prec 2) (hC.pool 2)
        (by decide) (by decide) swapW1_stable (by decide) (by decide)
        (fun b hb => by
          have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 2)).toAdr = pre.getStor (coinOf sevm pre 2) := hb.1.2
          exact ⟨(hb.1.1 _).trans hC.usdt, by rw [e]; exact hC.live, by rw [e]; exact hpf⟩)
        (fun b d hb hl => leave hb hl)
  · show MutableFloorProfile _ _ _ _ _ _ _ _ _ _ _ (swapPushD sevm _ j) (swapPushN sevm _ j)
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl
    · exact Blanc.Composition.Curve3PoolDai.dai_coinPushFloor (by decide) hfork hstatic hdep0 (hC.prec 0) (hC.pool 0)
        (by decide) (by decide) (fun _ _ _ _ => trivial) (by decide) (by decide)
        (fun b hb => ⟨(hb.2.2.1 _).trans hC.dai, by
          have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 0)).toAdr = pre.getStor (coinOf sevm pre 0) := hb.2.2.2
          rw [e]; exact hqf⟩)
        (fun _ _ _ _ => trivial)
    · exact UsdcLive.usdc22_coinPushFloor (by decide) hfork hstatic hdepth (hC.prec 1) (hC.pool 1)
        (by decide) (by decide) (fun _ _ _ _ => trivial) (by decide) (by decide)
        (fun b hb => ⟨(hb.2.2.1 _).trans hC.usdc, proxyAt_pinned hC hb.2.2, by
          have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 1)).toAdr = pre.getStor (coinOf sevm pre 1) := hb.2.2.2
          rw [e]; exact hqf⟩)
        (fun _ _ _ _ => trivial)
    · exact Blanc.Composition.Curve3PoolUsdt.usdt_coinPushFloor (by decide) hfork hstatic hdep0 (hC.prec 2) (hC.pool 2)
        (by decide) (by decide) (fun _ _ _ _ => trivial) (by decide) (by decide)
        (fun b hb => by
          have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 2)).toAdr = pre.getStor (coinOf sevm pre 2) := hb.2.2.2
          exact ⟨(hb.2.2.1 _).trans hC.usdt, by rw [e]; exact hC.live, by rw [e]; exact hqf⟩)
        (fun _ _ _ _ => trivial)

/-- **`exchange` with the real coins, at the true minimum, at message level**: for every pair, every residual gas
`R ≥ 2201`, at the cost `exExactCost` of `swapCalls`. -/
theorem pool_3crv_exchange_live_floor_coins {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {ps₀ : Curve3Pool.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) ps₀)
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state)
    {i j : Fin 3} {v : B256} (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : 2 ≤ (initSevm msg).depth)
    (hC : RealCoins (initSevm msg) (initDevm msg)) (hij : i ≠ j)
    (hpf : PullFitsK i ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) i)) (initSevm msg).caller
      (initSevm msg).currentTarget (exDx (initSevm msg)))
    (hqf : PushFitsK j ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) j)) (initSevm msg).currentTarget
      (initSevm msg).caller v)
    (hlive : i = 2 → Blanc.Lift.Usdt.NotDeprecated
      (pulledK i ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) i)) (initSevm msg).caller
        (initSevm msg).currentTarget (exDx (initSevm msg))))
    (hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧
      ∀ {o : Out}
        (_hcode : (initSevm msg).code = code)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selExchange)
        (_hi : i.val = (exI (initSevm msg)).toNat) (_hj : j.val = (exJ (initSevm msg)).toNat)
        (_hstep : step s (exEnv (initSevm msg) i j (exBalOpt i (swapB1 (initSevm msg) (initDevm msg) i))
          (exBalOpt i (swapB2 (initSevm msg) (initDevm msg) i))) (decodeCall (initSevm msg)) = some o)
        (_hv : Nat.toB256 (exPushAmt o) = v)
        (_hid : IdReady (initSevm msg) (initDevm msg)),
    ∃ (x0 x1 x2 : B256) (amp w : Nat),
        xpChk ⟨(balAt ((initDevm msg).getStor msg.currentTarget) 0).toNat,
          (balAt ((initDevm msg).getStor msg.currentTarget) 1).toNat,
          (balAt ((initDevm msg).getStor msg.currentTarget) 2).toNat⟩ =
            some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
        aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
        (∃ (hi3 : (exI (initSevm msg)).toNat < 3) (hj3 : (exJ (initSevm msg)).toNat < 3),
          getYChk amp ⟨(exI (initSevm msg)).toNat, hi3⟩ ⟨(exJ (initSevm msg)).toNat, hj3⟩
            (exW3 x0 x1 x2 (exI (initSevm msg)).toNat + exCred (initSevm msg) (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) *
              exRate (exI (initSevm msg)).toNat / exR0).toNat (V3.mk x0.toNat x1.toNat x2.toNat).get =
            some w) ∧
        ∀ R, 2201 ≤ R →
          R + exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) amp w < 2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas
                (R + exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) amp w)))
              (initDevm (msg.withGas
                (R + exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) amp w))) (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas
                (R + exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) amp w)))
              (initDevm (msg.withGas
                (R + exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) amp w))) (.ok post),
            exec (initEvm (msg.withGas
              (R + exExactCost (initSevm msg) (initDevm msg) (swapCalls (initSevm msg) (initDevm msg) i j) x0 x1 x2 (swapB1 (initSevm msg) (initDevm msg) i) (swapB2 (initSevm msg) (initDevm msg) i) amp w))) = .ok post ∧
            post.gasLeft = R ∧ ∃ bp bq,
            pullIn (exEnv (initSevm msg) i j bp bq) i (exDx (initSevm msg)).toNat =
              pullIn (exEnv (initSevm msg) i j (exBalOpt i (swapB1 (initSevm msg) (initDevm msg) i)) (exBalOpt i (swapB2 (initSevm msg) (initDevm msg) i))) i
                (exDx (initSevm msg)).toNat ∧
            RawEffect ⟨0, _, _, .ok post, exc⟩ post (exEnv (initSevm msg) i j bp bq) o ∧
            Checkpoint (post.getStor msg.currentTarget) o.state := by
  obtain ⟨-, s, hs, hck⟩ := pool_history_reached (sevm := initSevm msg) (pre := initDevm msg)
    trace poolInstalled initial env target state
  refine ⟨s, hs, ?_⟩
  intro o hcode hlen hcd hsel hi hj hstep hv hid
  subst hv
  have hdep0 : (initSevm msg).depth ≠ 0 := by omega
  obtain ⟨hW0c, hW1c, hW0, hTc, hbal, hpull, hpush⟩ := exchange_coins_floor (v := Nat.toB256 (exPushAmt o))
    hfork hstatic hdepth hC hij hpf hqf hlive
  obtain ⟨x0, x1, x2, amp, w, hX, hA, hY, hl⟩ := exchange_msg_floor (swapCalls (initSevm msg) (initDevm msg) i j)
    hcode hfork hstatic hdep0 hlen hcd hsel hi hj hck hstep hC.prec hpc hid hW0c hW1c hW0 hbal hpull hTc hpush
  refine ⟨x0, x1, x2, amp, w, hX, hA, hY, fun R hR hGm hkeep => ?_⟩
  obtain ⟨post, exc, hE, hg, bp, bq, hpe, hraw, hckp, -⟩ := hl R hR hGm hkeep
  exact ⟨post, exc, hE, hg, bp, bq, hpe, hraw, hckp⟩

end Swap

end Blanc.Composition.Curve3Pool3CrvLiteralWitness
