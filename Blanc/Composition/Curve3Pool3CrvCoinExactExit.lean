import Blanc.Composition.Curve3Pool3CrvExactLiteralHeadlines
import Blanc.Composition.Curve3PoolDaiCoinExact
import Blanc.Composition.Curve3PoolUsdtCoinExact
import Blanc.Composition.Curve3PoolUsdcCoinExact

/-!
# `remove_liquidity` at exact gas with the real coins

`pool_3crv_removeLiquidity_live_exact_coins`: `pool_3crv_removeLiquidity_live_exact` with coin 0 DAI, coin 1 USDC's proxy
over `FiatTokenV2_2` and coin 2 USDT, at `U = 104744`, with their exact debits in the cost (`exitPushD`). The
message-level form: the transaction wrapper and `PoolCallsKeep` stay as the headline states them.
-/

namespace Blanc.Composition.Curve3Pool3CrvLiteralWitness

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.ExecutionTrace Blanc.StableSwapNewton
open Blanc.Composition.Curve3Pool3CrvJoint (JointCheckpoint)
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3Ready C3With C3Blind C3At)
open Blanc.Composition.Curve3Pool3CrvExactAssembly
open Blanc.Composition.Curve3Pool3CrvHeadlinesExact
open Blanc.Composition.Curve3Pool3CrvInstance
open Blanc.Lift.Usdc

section Coins

variable (sevm : Sevm) (pre : Devm)

/-- **The real coins at a frame's entry**: DAI, USDC's proxy over `FiatTokenV2_2`, an undeprecated USDT, at
distinct addresses that are no precompile, not the pool and not 3Crv. -/
structure RealCoins : Prop where
  dai : pre.getCode (coinOf sevm pre 0) = Blanc.Lift.Dai.code
  usdc : pre.getCode (coinOf sevm pre 1) = Proxy.code
  impl : UsdcLive.ProxyAt sevm pre (coinOf sevm pre 1) Impl.code
  usdt : pre.getCode (coinOf sevm pre 2) = Blanc.Lift.Usdt.code
  live : Blanc.Lift.Usdt.NotDeprecated (pre.getStor (coinOf sevm pre 2))
  prec : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp (coinOf sevm pre k)
  pool : ∀ k : Fin 3, coinOf sevm pre k ≠ sevm.currentTarget
  tok : ∀ k : Fin 3, coinOf sevm pre k ≠ tokOf sevm pre
  apart : ∀ j k : Fin 3, j ≠ k → coinOf sevm pre j ≠ coinOf sevm pre k

/-- A world where every code is as at the entry and coin `j`'s ledger is. -/
def Pin (j : Fin 3) (b : Devm) : Prop :=
  (∀ a, b.getCode a = pre.getCode a) ∧ b.getStor (coinOf sevm pre j) = pre.getStor (coinOf sevm pre j)

/-- **`remove_liquidity`'s coin chain with the real coins**: coins `k, …, 2` as at the entry. -/
def pinsFrom (k : Nat) (b : Devm) : Prop := ∀ j : Fin 3, k ≤ j.val → Pin sevm pre j b

end Coins

section Chain

variable {sevm : Sevm} {pre : Devm} {c3 : Adr} {σ : Stor}

theorem pin_keep {j : Fin 3} {b d : Devm} (h : Pin sevm pre j b)
    (hs : Devm.getStor d (coinOf sevm pre j) = Devm.getStor b (coinOf sevm pre j))
    (hc : ∀ a, d.getCode a = b.getCode a) : Pin sevm pre j d :=
  ⟨fun a => (hc a).trans (h.1 a), hs.trans h.2⟩

theorem pinsFrom_wClosed (h : RealCoins sevm pre) (k : Nat) : WClosed sevm (pinsFrom sevm pre k) :=
  WClosed.of_foreign fun _ _ hb hs hc j hj => pin_keep (hb j hj) (hs _ (h.pool j)) hc

theorem pinsFrom_blind (htc : ∀ j : Fin 3, coinOf sevm pre j ≠ c3) (k : Nat) :
    C3Blind c3 (pinsFrom sevm pre k) :=
  fun _ _ hb hs hc j hj => pin_keep (hb j hj) (hs _ (htc j)) hc

theorem pinsFrom_entry (k : Nat) : pinsFrom sevm pre k pre := fun _ _ => ⟨fun _ => rfl, rfl⟩

/-- What a coin child's clean leaving keeps of the chain. -/
theorem pins_leave {k : Fin 3} {b d : Devm} {σ' : Stor} {R : Prop} (hC : RealCoins sevm pre)
    (htc : coinOf sevm pre k ≠ c3) (hb : C3With c3 σ (pinsFrom sevm pre k.val) b)
    (hl : CoinLeaves (coinOf sevm pre k) σ' R b d) : C3With c3 σ (pinsFrom sevm pre (k.val + 1)) d :=
  ⟨c3At_keep' hb.1 (hl.other _ (Ne.symm htc)) hl.code, fun j hj =>
    pin_keep (hb.2 j (by omega)) (hl.other _ (hC.apart j k (fin3_ne_of_lt (by omega)))) hl.code⟩

/-- `ProxyAt` from a world pinned to the entry. -/
theorem proxyAt_pinned {b : Devm} (hC : RealCoins sevm pre) (h : Pin sevm pre 1 b) :
    UsdcLive.ProxyAt sevm b (coinOf sevm pre 1) Impl.code := by
  have hv : ∀ k, b.getStorVal (coinOf sevm pre 1) k = pre.getStorVal (coinOf sevm pre 1) k := by
    intro k
    rw [getStorVal_eq_getStor, getStorVal_eq_getStor]
    exact congrArg (fun σ => Stor.get σ k) h.2
  exact ⟨hC.impl.undel, by rw [hv, h.1]; exact hC.impl.code, by rw [hv]; exact hC.impl.prec,
    by rw [hv]; exact hC.impl.admin⟩

end Chain

/-! ## `remove_liquidity`'s three pushes -/

section Exit

/-- `remove_liquidity`'s push debits with the real coins. -/
noncomputable def exitPushD (sevm : Sevm) (σ : Stor) (i : Nat) : Devm → List B256 → Mem → Nat :=
  if i = 0 then coinDebit Blanc.Lift.Dai.xferG sevm (coinAt σ 0) 0x520 0x44 0x5c0
  else if i = 1 then coinDebit UsdcLive.xferG sevm (coinAt σ 1) 0x520 0x44 0x5c0
  else coinDebit Blanc.Lift.Usdt.xferG sevm (coinAt σ 2) 0x520 0x44 0x5c0

/-- `remove_liquidity`'s push successors with the real coins. -/
noncomputable def exitPushN (sevm : Sevm) (σ : Stor) (i : Nat) : Devm → List B256 → Mem → Devm :=
  if i = 0 then coinNext (fun s p => Blanc.Lift.Dai.xferPost s p 0) sevm (coinAt σ 0) 0x520 0x44 0x5c0
  else if i = 1 then coinNext (UsdcLive.proxyCanon 1 (fun s p => UsdcLive.implXferPost s p 0)) sevm (coinAt σ 1)
    0x520 0x44 0x5c0
  else coinNext (fun s p => Blanc.Lift.Usdt.xferPost s p 0) sevm (coinAt σ 2) 0x520 0x44 0x5c0

variable {sevm : Sevm} {pre : Devm} {c3 : Adr} {σ : Stor} {T : B256}

/-- **The three exact pushes with the real coins, along the chain.** -/
theorem exit_pushes (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : 2 ≤ sevm.depth) (hC : RealCoins sevm pre) (htc : ∀ j : Fin 3, coinOf sevm pre j ≠ c3)
    (hf0 : Blanc.Lift.Dai.MoveFits (pre.getStor (coinOf sevm pre 0)) sevm.currentTarget sevm.caller
      (balAt (pre.getStor sevm.currentTarget) 0 * rlAmt sevm / T))
    (hf1 : UsdcLive.MoveFits (pre.getStor (coinOf sevm pre 1)) sevm.currentTarget sevm.caller
      (balAt (pre.getStor sevm.currentTarget) 1 * rlAmt sevm / T))
    (hf2 : Blanc.Lift.Usdt.XferFits (pre.getStor (coinOf sevm pre 2)) sevm.currentTarget sevm.caller
      (balAt (pre.getStor sevm.currentTarget) 2 * rlAmt sevm / T)) :
    ∀ i, i < 3 → MutableCallProfile sevm (C3With c3 σ (pinsFrom sevm pre i)) (C3With c3 σ (pinsFrom sevm pre (i + 1)))
      (coinAt (pre.getStor sevm.currentTarget) i)
      (transferSel ++ sevm.caller.toB256.toBytes ++ (balAt (pre.getStor sevm.currentTarget) i * rlAmt sevm / T).toBytes)
      RawCallOk 104744 0x520 0x44 0x5c0 (exitPushD sevm (pre.getStor sevm.currentTarget) i)
      (exitPushN sevm (pre.getStor sevm.currentTarget) i) := by
  intro i hi
  have hD : (2 : Nat) ≤ sevm.depth := hdepth
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · exact Blanc.Composition.Curve3PoolDai.dai_coinPushExact hfork hstatic (by omega) (hC.prec 0) (hC.pool 0)
      (by decide) (by decide) (by decide)
      (fun b hb => ⟨((hb.2 0 (le_refl _)).1 _).trans hC.dai, by have e : b.getStor (coinAt (pre.getStor sevm.currentTarget) 0).toAdr = pre.getStor (coinOf sevm pre 0) := (hb.2 0 (le_refl _)).2; rw [e]; exact hf0⟩)
      (fun b d hb hl => pins_leave (k := 0) hC (htc 0) hb hl)
  · exact UsdcLive.usdc22_coinPushExact hfork hstatic hdepth (hC.prec 1) (hC.pool 1)
      (by decide) (by decide) (by decide)
      (fun b hb => ⟨((hb.2 1 (le_refl _)).1 _).trans hC.usdc, proxyAt_pinned hC (hb.2 1 (le_refl _)),
        by have e : b.getStor (coinAt (pre.getStor sevm.currentTarget) 1).toAdr = pre.getStor (coinOf sevm pre 1) := (hb.2 1 (le_refl _)).2; rw [e]; exact hf1⟩)
      (fun b d hb hl => pins_leave (k := 1) hC (htc 1) hb hl)
  · exact Blanc.Composition.Curve3PoolUsdt.usdt_coinPushExact hfork hstatic (by omega) (hC.prec 2) (hC.pool 2)
      (by decide) (by decide) (by decide)
      (fun b hb => ⟨((hb.2 2 (le_refl _)).1 _).trans hC.usdt, by have e : b.getStor (coinAt (pre.getStor sevm.currentTarget) 2).toAdr = pre.getStor (coinOf sevm pre 2) := (hb.2 2 (le_refl _)).2; rw [e]; exact hC.live,
        by have e : b.getStor (coinAt (pre.getStor sevm.currentTarget) 2).toAdr = pre.getStor (coinOf sevm pre 2) := (hb.2 2 (le_refl _)).2; rw [e]; exact hf2⟩)
      (fun b d hb hl => pins_leave (k := 2) hC (htc 2) hb hl)

end Exit

section Headline

variable {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop}

/-- **`pool_3crv_removeLiquidity_live_exact` with the real coins**: DAI, USDC's proxy over V2_2, an undeprecated
USDT, at `U = 104744`, the coins' debits in the cost. The world conditions are hypotheses; `hkeep`, the model step
and the residual gas are the headline's. -/
theorem pool_3crv_removeLiquidity_live_exact_coins
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
        ∀ R, 167000 + 5 * 104744 ≤ R →
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
  obtain ⟨s, hs, ready, hlive⟩ := pool_3crv_removeLiquidity_live_exact trace poolInstalled
    c3Installed joint fresh env notSystem target state
  have ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  have hpc := pool_code_ne_of_history (sevm := initSevm msg) (pre := initDevm msg) trace
    poolInstalled joint env target state
  subst ht
  have hdep0 : (initSevm msg).depth ≠ 0 := by omega
  have hpush := exit_pushes (c3 := tokOf (initSevm msg) (initDevm msg))
    (σ := Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg))) (T := T)
    hfork hstatic hdepth hcoins hcoins.tok hf0 hf1 hf2
  exact ⟨s, hs, ready, fun hcode hlen hcd hsel hstep hid => hlive _ _ hcode hfork hstatic hdep0 hlen hcd
    hsel hstep hc3.prec hcoins.prec hpc hid (by decide) hc3.supply hburn
    (fun k _ => pinsFrom_wClosed hcoins k) (pinsFrom_entry 0) (pinsFrom_blind hcoins.tok) hpush⟩

end Headline

end Blanc.Composition.Curve3Pool3CrvLiteralWitness
