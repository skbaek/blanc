import Blanc.Composition.Curve3Pool3CrvHeadlinesExact
import Blanc.Composition.Curve3Pool3CrvExactLiteralWitness

/-!
# The composed exact headlines with their coin and 3Crv hypotheses discharged

Each composed exact headline (`Curve3Pool3CrvHeadlinesExact.lean`) applied to the witness data of
`Curve3Pool3CrvExactLiteralWitness.lean`: over the same history, under the world conditions of the
witnesses (`Token20` coins whose ledgers cover the calls, 3Crv's code with supply `T`, 3Crv
accepting the burn or mint), there is a coin chain `V`, `U = 80000` and coin debit/next functions
meeting the headline's callee and coin-chain hypotheses as stated (the conjunction is restated in
the headline's text), and the headline's conclusion then holds under only the hypotheses this file
does not discharge: `_hcode`, `_hlen`, `_hcd`, `_hsel`, the model step `_hstep`, `_hpc`, `_hid`,
the residual-gas headroom on `R`, the no-wrap bound and the per-execution keep premise. `_hfork`,
`_hstatic`, `_hdepth` are world conditions here.

* `pool_3crv_removeLiquidity_live_exact_literal`, `pool_3crv_addLiquidity_live_exact_literal`,
  `pool_3crv_removeLiquidityImbalance_live_exact_literal`,
  `pool_3crv_removeLiquidityOneCoin_live_exact_literal`;
* `pool_3crv_*_live_entry_literal`: the same for the sufficient-gas composed rows
  (`Curve3Pool3CrvHeadlines.pool_3crv_*_live_entry`), whose remaining hypotheses are `_hcode`,
  `_hlen`, `_hcd`, `_hsel`, `_hstep`, `_hpc`, `_hid`, `_hkeep` and the gas bounds `_hG`, `_hGm`.

For `remove_liquidity_one_coin`, `_hi` (which coin the call data names) also stays a premise; it
fixes the coin `i` whose `Token20` facts are assumed.
-/

namespace Blanc.Composition.Curve3Pool3CrvLiteralWitness

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.ExecutionTrace Blanc.StableSwapNewton
open Blanc.Composition.Curve3Pool3CrvJoint (JointCheckpoint)
open Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3Ready C3With C3Blind)
open Blanc.Composition.Curve3Pool3CrvExactAssembly
open Blanc.Composition.Curve3Pool3CrvHeadlinesExact
open Blanc.Composition.Curve3Pool3CrvInstance

section Joint

variable {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop}

/-- **`pool_3crv_removeLiquidity_live_exact` with its coin and 3Crv hypotheses discharged.** -/
theorem pool_3crv_removeLiquidity_live_exact_literal
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state)
    {T : B256} (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0)
    (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hcoins : T20Coins (initSevm msg) (initDevm msg))
    (hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
      (rlAmt (initSevm msg)))
    (hfits : ∀ k : Fin 3, T20MoveFits
      ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) k)) msg.currentTarget
      msg.caller (balAt ((initDevm msg).getStor msg.currentTarget) k * rlAmt (initSevm msg) / T)) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∃ (V : Nat → Devm → Prop) (U : Nat) (pushD : Nat → Devm → List B256 → Mem → Nat)
        (pushN : Nat → Devm → List B256 → Mem → Devm),
          (¬ (initSevm msg).benvStat.rules.isPrecomp c3 ∧
          (∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
              (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr) ∧
          70000 ≤ U ∧
          (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T ∧
          BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
              (rlAmt (initSevm msg)) ∧
          (∀ k, k ≤ 3 → WClosed (initSevm msg) (V k)) ∧ V 0 (initDevm msg) ∧
          (∀ k, C3Blind c3 (V k)) ∧
          (∀ i, i < 3 → MutableCallProfile (initSevm msg)
              (C3With c3 (Devm.getStor (initDevm msg) c3) (V i))
              (C3With c3 (Devm.getStor (initDevm msg) c3) (V (i + 1)))
              (coinAt ((initDevm msg).getStor msg.currentTarget) i)
              (transferSel ++ msg.caller.toB256.toBytes ++
                (balAt ((initDevm msg).getStor msg.currentTarget) i * rlAmt (initSevm msg) / T).toBytes)
              RawCallOk U 0x520 0x44 0x5c0 (pushD i) (pushN i))) ∧
      ∀ {o : Out}
        (_hcode : (initSevm msg).code = code)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidity)
        (_hstep : step s (rlEnv (initSevm msg) T) (decodeCall (initSevm msg)) = some o)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg)),
        ∀ R, 167000 + 5 * U ≤ R →
          R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN) < 2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN))))
              (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN)))) (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN))))
              (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN)))) (.ok post),
            exec (initEvm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN)))) =
              .ok post ∧
            post.gasLeft = R ∧
            RawEffect ⟨0, _, _, .ok post, exc⟩ post (rlEnv (initSevm msg) T) o ∧
            Checkpoint (post.getStor msg.currentTarget) o.state := by
  obtain ⟨s, hs, ready, hlive⟩ := pool_3crv_removeLiquidity_live_exact trace poolInstalled
    c3Installed joint fresh env notSystem target state
  have ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  obtain ⟨V, U, pushD, pushN, htok, hcoin, hU, hT, hburn', hVc, hVb, hVs, hpush⟩ :=
    removeLiquidity_exact_literal_witness ht hfork hstatic hdepth hc3 hcoins hburn hfits
  exact ⟨s, hs, ready, V, U, pushD, pushN,
    ⟨htok, hcoin, hU, hT, hburn', hVc, hVb, hVs, hpush⟩,
    fun hcode hlen hcd hsel hstep hpc hid => hlive pushD pushN hcode hfork hstatic hdepth hlen hcd
      hsel hstep htok hcoin hpc hid hU hT hburn' hVc hVb hVs hpush⟩

/-- **`pool_3crv_addLiquidity_live_exact` with its coin and 3Crv hypotheses discharged**; the
world after the mint, `C3With σm (V 3)`, carries the fee coin's pulled ledger. -/
theorem pool_3crv_addLiquidity_live_exact_literal
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state)
    {T : B256} (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0)
    (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hcoins : T20Coins (initSevm msg) (initDevm msg))
    (hfits : ∀ k : Fin 3, alAmt (initSevm msg) k.val ≠ 0 → T20PullFits
      ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) k)) msg.caller
      msg.currentTarget msg.currentTarget (alAmt (initSevm msg) k.val)) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∀ {o : Out}, MintFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
        (Nat.toB256 (alMintAmt o)) →
      ∃ (B1 B2 : B256) (V : Nat → Devm → Prop) (U : Nat)
        (pullD : Nat → Devm → List B256 → Mem → Nat) (pullN : Nat → Devm → List B256 → Mem → Devm)
        (balBD balAD : Devm → List B256 → Mem → Nat) (balBN balAN : Devm → List B256 → Mem → Devm),
          (¬ (initSevm msg).benvStat.rules.isPrecomp c3 ∧
          (∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
              (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr) ∧
          70000 ≤ U ∧
          (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T ∧
          MintFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
              (Nat.toB256 (alMintAmt o)) ∧
          (∀ k, k ≤ 3 → WClosed (initSevm msg) (V k)) ∧ V 0 (initDevm msg) ∧
          (∀ k, C3Blind c3 (V k)) ∧
          (∀ k : Fin 3, alAmt (initSevm msg) k.val = 0 → ∀ b, V k b → V (k + 1) b) ∧
          (∀ k, k < 3 → alAmt (initSevm msg) k ≠ 0 →
              MutableCallProfile (initSevm msg) (C3With c3 (Devm.getStor (initDevm msg) c3) (V k))
                (C3With c3 (Devm.getStor (initDevm msg) c3) (V (k + 1)))
                (coinAt ((initDevm msg).getStor msg.currentTarget) k)
                (transferFromSel ++ msg.caller.toB256.toBytes ++ msg.currentTarget.toB256.toBytes ++
                  (alAmt (initSevm msg) k).toBytes) RawCallOk U 0x760 0x64 0x820 (pullD k) (pullN k)) ∧
          (alAmt (initSevm msg) 2 ≠ 0 →
              StaticWordCallProfile (initSevm msg) (C3With c3 (Devm.getStor (initDevm msg) c3) (V 2))
                (C3With c3 (Devm.getStor (initDevm msg) c3) (V 2))
                (coinAt ((initDevm msg).getStor msg.currentTarget) 2)
                (balanceOfData msg.currentTarget) B1 U 0x53c 0x24 0x5a0 balBD balBN) ∧
          (alAmt (initSevm msg) 2 ≠ 0 →
              StaticWordCallProfile (initSevm msg) (C3With c3 (Devm.getStor (initDevm msg) c3) (V 3))
                (C3With c3 (Devm.getStor (initDevm msg) c3) (V 3))
                (coinAt ((initDevm msg).getStor msg.currentTarget) 2)
                (balanceOfData msg.currentTarget) B2 U 0x87c 0x24 0x8e0 balAD balAN)) ∧
      ∀ (_hcode : (initSevm msg).code = code)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selAddLiquidity)
        (_hstep : step s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat)
          (decodeCall (initSevm msg)) = some o)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg)),
        ∃ (amp v0 v1 v2 : Nat) (xa xb xc : V3) (f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256),
          aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
          xpChk ⟨(alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2
              0).toNat,
            (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 1).toNat,
            (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2
              2).toNat⟩ = some xb ∧
          getDChk xb.get amp 1 = some v1 ∧
          (T ≠ 0 →
            xpChk ⟨(balAt ((initDevm msg).getStor msg.currentTarget) 0).toNat,
              (balAt ((initDevm msg).getStor msg.currentTarget) 1).toNat,
              (balAt ((initDevm msg).getStor msg.currentTarget) 2).toNat⟩ = some xa ∧
            getDChk xa.get amp 1 = some v0 ∧
            RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
              (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
              (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 0)
              (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 0)
              f0 s0 x0 ∧
            RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
              (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
              (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 1)
              (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 1)
              f1 s1 x1 ∧
            RliFeeIter (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot))
              (((initDevm msg).getStor msg.currentTarget).get adminFeeSlot) (Nat.toB256 v0)
              (Nat.toB256 v1) (balAt ((initDevm msg).getStor msg.currentTarget) 2)
              (alLiveNew (initSevm msg) (alOld ((initDevm msg).getStor msg.currentTarget)) B1 B2 2)
              f2 s2 x2 ∧
            xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc ∧ getDChk xc.get amp 1 = some v2) ∧
          ∀ R, 100000 + 5 * U ≤ R →
          costAddLiquidity s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat) (argV3 (initSevm msg) 0) +
              7 * U ≤
            R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0
              s1 s2 x0 x1 x2 →
          R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1
              s2 x0 x1 x2 + 6000 < 2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN)
                amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)))
              (initDevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) amp T B1 B2 xa xb
                xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c' ∈ Exec.childFrames exc, c'.post.getCode 4 = c'.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN)
                amp T B1 B2 xa xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)))
              (initDevm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) amp T B1 B2 xa xb
                xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) (.ok post),
            exec (initEvm (msg.withGas (R + alExactCost (initSevm msg) (initDevm msg) (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) amp T B1 B2 xa
              xb xc v0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2))) = .ok post ∧
            post.gasLeft = R ∧
            ∃ e : Env, e.supply = some T.toNat ∧ step s e (decodeCall (initSevm msg)) = some o ∧
              RawEffect ⟨0, _, _, .ok post, exc⟩ post e o ∧
              Checkpoint (post.getStor msg.currentTarget) o.state := by
  obtain ⟨s, hs, ready, hlive⟩ := pool_3crv_addLiquidity_live_exact trace poolInstalled
    c3Installed joint fresh env notSystem target state
  have ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  refine ⟨s, hs, ready, fun {o} hmint => ?_⟩
  obtain ⟨B1, B2, V, U, pullD, pullN, balBD, balAD, balBN, balAN, htok, hcoin, hU, hT, hmint',
    hVc, hVb, hVs, hskip, hpull, hbalB, hbalA⟩ :=
    addLiquidity_exact_literal_witness ht hfork hstatic hdepth hc3 hcoins hmint hfits
  exact ⟨B1, B2, V, U, pullD, pullN, balBD, balAD, balBN, balAN,
    ⟨htok, hcoin, hU, hT, hmint', hVc, hVb, hVs, hskip, hpull, hbalB, hbalA⟩,
    fun hcode hlen hcd hsel hstep hpc hid => hlive pullD pullN balBD balAD balBN balAN hcode hfork
      hstatic hdepth hlen hcd hsel hstep htok hcoin hpc hid hU hT hmint' hVc hVb hVs hskip hpull
      hbalB hbalA⟩

/-- **`pool_3crv_removeLiquidityImbalance_live_exact` with its coin and 3Crv hypotheses
discharged.** -/
theorem pool_3crv_removeLiquidityImbalance_live_exact_literal
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state)
    {T : B256} (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0)
    (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hcoins : T20Coins (initSevm msg) (initDevm msg))
    (hfits : ∀ k : Fin 3, rliAmt (initSevm msg) k.val ≠ 0 → T20MoveFits
      ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) k)) msg.currentTarget
      msg.caller (rliAmt (initSevm msg) k.val)) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∀ {o : Out}, BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
        (Nat.toB256 (rliBurnAmt o)) →
      ∃ (V : Nat → Devm → Prop) (U : Nat) (pushD : Nat → Devm → List B256 → Mem → Nat)
        (pushN : Nat → Devm → List B256 → Mem → Devm),
          (¬ (initSevm msg).benvStat.rules.isPrecomp c3 ∧
          (∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
              (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr) ∧
          70000 ≤ U ∧
          (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T ∧
          BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
              (Nat.toB256 (rliBurnAmt o)) ∧
          (∀ k, k ≤ 3 → WClosed (initSevm msg) (V k)) ∧ V 0 (initDevm msg) ∧
          (∀ k, C3Blind c3 (V k)) ∧
          (∀ k : Fin 3, rliAmt (initSevm msg) k.val = 0 → ∀ b, V k b → V (k + 1) b) ∧
          (∀ k, k < 3 → rliAmt (initSevm msg) k ≠ 0 →
              MutableCallProfile (initSevm msg)
                (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
                  (Nat.toB256 (rliBurnAmt o))) (V k))
                (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
                  (Nat.toB256 (rliBurnAmt o))) (V (k + 1)))
                (((initDevm msg).getStor msg.currentTarget).get (coinsBase + Nat.toB256 k))
                (transferSel ++ msg.caller.toB256.toBytes ++ (rliAmt (initSevm msg) k).toBytes)
                RawCallOk U 0xaa0 0x44 0xb40 (pushD k) (pushN k))) ∧
      ∀ (_hcode : (initSevm msg).code = code)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityImbalance)
        (_hstep : step s (rliEnvW (initSevm msg) T.toNat) (decodeCall (initSevm msg)) = some o)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg)),
        ∃ w : RliWords, RliWordsPin (initSevm msg) (initDevm msg) s w ∧
          ∀ R, 66000 + 3 * U ≤ R →
            costImbalance s (rliEnvW (initSevm msg) T.toNat) (argV3 (initSevm msg) 0) + 5 * U ≤
              R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w →
            R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w + 3000 < 2 ^ 256 →
            (∀ post (exc : Exec 0
                (initSevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w)))
                (initDevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w)))
                (.ok post)),
              PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
                ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
            ∃ post, ∃ exc : Exec 0
                (initSevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w)))
                (initDevm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w)))
                (.ok post),
              exec (initEvm (msg.withGas (R + rliExactCost (initSevm msg) (initDevm msg) (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) T w))) =
                .ok post ∧
              post.gasLeft = R ∧
              RawEffect ⟨0, _, _, .ok post, exc⟩ post (rliEnvW (initSevm msg) T.toNat) o ∧
              Checkpoint (post.getStor msg.currentTarget) o.state ∧ C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
                (Nat.toB256 (rliBurnAmt o))) (V 3) post := by
  obtain ⟨s, hs, ready, hlive⟩ := pool_3crv_removeLiquidityImbalance_live_exact trace
    poolInstalled c3Installed joint fresh env notSystem target state
  have ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  refine ⟨s, hs, ready, fun {o} hburn => ?_⟩
  obtain ⟨V, U, pushD, pushN, htok, hcoin, hU, hT, hburn', hVc, hVb, hVs, hskip, hpush⟩ :=
    removeLiquidityImbalance_exact_literal_witness ht hfork hstatic hdepth hc3 hcoins hburn hfits
  exact ⟨V, U, pushD, pushN, ⟨htok, hcoin, hU, hT, hburn', hVc, hVb, hVs, hskip, hpush⟩,
    fun hcode hlen hcd hsel hstep hpc hid => hlive pushD pushN hcode hfork hstatic hdepth hlen hcd
      hsel hstep htok hcoin hpc hid hU hT hburn' hVc hVb hVs hskip hpush⟩

/-- **`pool_3crv_removeLiquidityOneCoin_live_exact` with its coin and 3Crv hypotheses
discharged**, for the coin `i` the call data names (`_hi` stays a premise: it fixes `i`). -/
theorem pool_3crv_removeLiquidityOneCoin_live_exact_literal
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state)
    {T : B256} (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0)
    (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
      (coinOf (initSevm msg) (initDevm msg) k))
    (hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
      (ocAmt (initSevm msg))) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∀ {o : Out} {i : Fin 3} (_hi : i.val = (ocI (initSevm msg)).toNat),
        (initDevm msg).getCode (coinOf (initSevm msg) (initDevm msg) i) =
          VyperNonreentrantDeployed.Token20.code →
        coinOf (initSevm msg) (initDevm msg) i ≠ msg.currentTarget →
        coinOf (initSevm msg) (initDevm msg) i ≠ c3 →
        T20MoveFits ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) i))
          msg.currentTarget msg.caller (Nat.toB256 (ocPushAmt o)) →
      ∃ (V : Nat → Devm → Prop) (U : Nat) (pushD : Devm → List B256 → Mem → Nat)
        (pushN : Devm → List B256 → Mem → Devm),
          (¬ (initSevm msg).benvStat.rules.isPrecomp c3 ∧
          (∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
              (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr) ∧
          70000 ≤ U ∧
          (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T ∧
          BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
              (ocAmt (initSevm msg)) ∧
          (∀ k, k ≤ 1 → WClosed (initSevm msg) (V k)) ∧ V 0 (initDevm msg) ∧
          C3Blind c3 (V 0) ∧
          MutableCallProfile (initSevm msg)
              (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
                (ocAmt (initSevm msg))) (V 0))
              (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
                (ocAmt (initSevm msg))) (V 1))
              (((initDevm msg).getStor msg.currentTarget).get (coinsBase + ocI (initSevm msg)))
              (transferSel ++ msg.caller.toB256.toBytes ++ (Nat.toB256 (ocPushAmt o)).toBytes)
              RawCallOk U 0x540 0x44 0x5e0 pushD pushN) ∧
      ∀ (_hcode : (initSevm msg).code = code)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityOneCoin)
        (_hstep : step s (ocEnv (initSevm msg) i T.toNat) (decodeCall (initSevm msg)) = some o)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg)),
        ∃ (amp : Nat) (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) (hi3 : (ocI (initSevm msg)).toNat < 3),
          aChk s (initSevm msg).benvStat.time.toNat = some amp ∧
          xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
          getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1 = some D0.toNat ∧
          getYDChk amp ⟨(ocI (initSevm msg)).toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
            (D0 - ocAmt (initSevm msg) * D0 / T).toNat = some y.toNat ∧
          CwStep (Bytes.toB256 [0] = ocI (initSevm msg)) x0 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
            (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x0 r0 ∧
          CwStep (Bytes.toB256 [1] = ocI (initSevm msg)) x1 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
            (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x1 r1 ∧
          CwStep (Bytes.toB256 [2] = ocI (initSevm msg)) x2 (D0 - ocAmt (initSevm msg) * D0 / T) D0 y
            (cwFee (((initDevm msg).getStor msg.currentTarget).get feeSlot)) x2 r2 ∧
          getYDChk amp ⟨(ocI (initSevm msg)).toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
            (D0 - ocAmt (initSevm msg) * D0 / T).toNat = some y2.toNat ∧
          ∀ R, 131000 + 3 * U ≤ R →
          R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2 + 2000 <
            2 ^ 256 →
          (∀ post (exc : Exec 0 (initSevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (initDevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (.ok post)),
            PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
              ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
          ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (initDevm (msg.withGas
                (R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2)))
              (.ok post),
            exec (initEvm (msg.withGas
              (R + ocExactCost (initSevm msg) (initDevm msg) T (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) amp x0 x1 x2 D0 y r0 r1 r2 y2))) =
              .ok post ∧
            post.gasLeft = R ∧ ∃ T' : Nat,
            RawEffect ⟨0, _, _, .ok post, exc⟩ post (ocEnv (initSevm msg) i T') o ∧
            Checkpoint (post.getStor msg.currentTarget) o.state ∧ C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
              (ocAmt (initSevm msg))) (V 1) post := by
  obtain ⟨s, hs, ready, hlive⟩ := pool_3crv_removeLiquidityOneCoin_live_exact trace
    poolInstalled c3Installed joint fresh env notSystem target state
  have ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  refine ⟨s, hs, ready, fun {o i} hi hcode hpool htc hfits => ?_⟩
  obtain ⟨V, U, pushD, pushN, htok, hcoin', hU, hT, hburn', hVc, hVb, hVs, hpush⟩ :=
    removeLiquidityOneCoin_exact_literal_witness ht hfork hstatic hdepth hc3 hi hcoin hcode hpool
      htc hburn hfits
  exact ⟨V, U, pushD, pushN, ⟨htok, hcoin', hU, hT, hburn', hVc, hVb, hVs, hpush⟩,
    fun hcode' hlen hcd hsel hstep hpc hid => hlive pushD pushN hcode' hfork hstatic hdepth hlen
      hcd hsel hi hstep htok hcoin' hpc hid hU hT hburn' hVc hVb hVs hpush⟩

end Joint

/-! ## The sufficient-gas composed rows -/

section Bounded

variable {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop}
  {sevm : Sevm} {pre : Devm}

/-- **`pool_3crv_removeLiquidity_live_entry` with its coin and 3Crv hypotheses discharged.** -/
theorem pool_3crv_removeLiquidity_live_entry_literal
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state)
    {T : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T)
    (hcoins : T20Coins sevm pre)
    (hburn : BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (rlAmt sevm))
    (hfits : ∀ k : Fin 3, T20MoveFits (pre.getStor (coinOf sevm pre k)) sevm.currentTarget
      sevm.caller (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T)) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∃ (V : Nat → Devm → Prop) (U : Nat),
        (¬ sevm.benvStat.rules.isPrecomp c3 ∧
        (∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
            ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) ∧
        70000 ≤ U ∧
        (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T ∧
        BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (rlAmt sevm) ∧
        (∀ k, k ≤ 3 → WClosed sevm (V k)) ∧ V 0 pre ∧ (∀ k, C3Blind c3 (V k)) ∧
        (∀ k : Fin 3, CoinPushOkAt sevm (C3With c3 (Devm.getStor pre c3) (V k))
            (C3With c3 (Devm.getStor pre c3) (V (k + 1)))
            ((pre.getStor sevm.currentTarget).get (coinSlot k))
            (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T) U 0x520 0x5c0)) ∧
      ∀ {o : Out} {G : Nat} (_hcode : sevm.code = code)
        (_hlen : 4 ≤ sevm.data.length)
        (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidity)
        (_hstep : step s (rlEnv sevm T) (decodeCall sevm) = some o)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty)
        (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hG : 167000 + 5 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rlEnv sevm T) o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state := by
  obtain ⟨s, hs, ready, hlive⟩ :=
    Curve3Pool3CrvHeadlines.pool_3crv_removeLiquidity_live_entry trace poolInstalled
    c3Installed joint fresh env notSystem target state
  have ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  obtain ⟨V, U, htok, hcoin, hU, hT, hburn', hVc, hVb, hVs, hpush⟩ :=
    removeLiquidity_entry_literal_witness ht hfork hstatic hdepth hc3 hcoins hburn hfits
  exact ⟨s, hs, ready, V, U, ⟨htok, hcoin, hU, hT, hburn', hVc, hVb, hVs, hpush⟩,
    fun hcode hlen hcd hsel hstep hpc hid hkeep hG hGm => hlive hcode hfork hstatic hdepth hlen
      hcd hsel hstep htok hcoin hpc hid hkeep hU hT hburn' hVc hVb hVs hpush hG hGm⟩

/-- **`pool_3crv_addLiquidity_live_entry` with its coin and 3Crv hypotheses discharged**; the fee
coin's pulled ledger is carried in `V 3`. -/
theorem pool_3crv_addLiquidity_live_entry_literal
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state)
    {T : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T)
    (hcoins : T20Coins sevm pre)
    (hfits : ∀ k : Fin 3, alAmt sevm k.val ≠ 0 → T20PullFits (pre.getStor (coinOf sevm pre k))
      sevm.caller sevm.currentTarget sevm.currentTarget (alAmt sevm k.val)) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out}, MintFits (Devm.getStor pre c3) pool sevm.caller.toB256
        (Nat.toB256 (alMintAmt o)) →
      ∃ (B1 B2 : B256) (V : Nat → Devm → Prop) (U : Nat),
        (¬ sevm.benvStat.rules.isPrecomp c3 ∧
        (∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
            ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) ∧
        70000 ≤ U ∧
        (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T ∧
        MintFits (Devm.getStor pre c3) pool sevm.caller.toB256 (Nat.toB256 (alMintAmt o)) ∧
        (∀ k, k ≤ 3 → WClosed sevm (V k)) ∧ V 0 pre ∧ (∀ k, C3Blind c3 (V k)) ∧
        (∀ k : Fin 3, k ≠ feeIndex → alAmt sevm k.val ≠ 0 →
            CoinPullOkAt sevm (C3With c3 (Devm.getStor pre c3) (V k))
              (C3With c3 (Devm.getStor pre c3) (V (k + 1)))
              ((pre.getStor sevm.currentTarget).get (coinSlot k)) (alAmt sevm k.val) U 0x760 0x820) ∧
        (∀ k : Fin 3, alAmt sevm k.val = 0 → ∀ b, V k b → V (k + 1) b) ∧
        (alAmt sevm 2 ≠ 0 →
            CoinBalOkAt sevm (C3With c3 (Devm.getStor pre c3) (V 2))
              (C3With c3 (Devm.getStor pre c3) (V 2))
              ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B1 U 0x53c 0x5a0 ∧
            CoinPullOkAt sevm (C3With c3 (Devm.getStor pre c3) (V 2))
              (C3With c3 (Devm.getStor pre c3) (V 3))
              ((pre.getStor sevm.currentTarget).get (coinSlot 2)) (alAmt sevm 2) U 0x760 0x820 ∧
            CoinBalOkAt sevm (C3With c3 (Devm.getStor pre c3) (V 3))
              (C3With c3 (Devm.getStor pre c3) (V 3))
              ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B2 U 0x87c 0x8e0)) ∧
      ∀ {G : Nat} (_hcode : sevm.code = code)
        (_hlen : 4 ≤ sevm.data.length)
        (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selAddLiquidity)
        (_hstep : step s (alEnvW sevm T.toNat B1.toNat B2.toNat) (decodeCall sevm) = some o)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty)
        (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hG : costAddLiquidity s (alEnvW sevm T.toNat B1.toNat B2.toNat) (argV3 sevm 0) + 7 * U ≤
          G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ e : Env,
          e.supply = some T.toNat ∧ step s e (decodeCall sevm) = some o ∧
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post e o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state := by
  obtain ⟨s, hs, ready, hlive⟩ :=
    Curve3Pool3CrvHeadlines.pool_3crv_addLiquidity_live_entry trace poolInstalled
    c3Installed joint fresh env notSystem target state
  have ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  refine ⟨s, hs, ready, fun {o} hmint => ?_⟩
  obtain ⟨B1, B2, V, U, htok, hcoin, hU, hT, hmint', hVc, hVb, hVs, hpull, hskip, hfee⟩ :=
    addLiquidity_entry_literal_witness ht hfork hstatic hdepth hc3 hcoins hmint hfits
  exact ⟨B1, B2, V, U, ⟨htok, hcoin, hU, hT, hmint', hVc, hVb, hVs, hpull, hskip, hfee⟩,
    fun hcode hlen hcd hsel hstep hpc hid hkeep hG hGm => hlive hcode hfork hstatic hdepth hlen
      hcd hsel hstep htok hcoin hpc hid hkeep hU hT hmint' hVc hVb hVs hpull hskip hfee hG hGm⟩

/-- **`pool_3crv_removeLiquidityImbalance_live_entry` with its coin and 3Crv hypotheses
discharged.** -/
theorem pool_3crv_removeLiquidityImbalance_live_entry_literal
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state)
    {T : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T)
    (hcoins : T20Coins sevm pre)
    (hfits : ∀ k : Fin 3, rliAmt sevm k.val ≠ 0 → T20MoveFits (pre.getStor (coinOf sevm pre k))
      sevm.currentTarget sevm.caller (rliAmt sevm k.val)) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out}, BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256
        (Nat.toB256 (rliBurnAmt o)) →
      ∃ (V : Nat → Devm → Prop) (U : Nat),
        (¬ sevm.benvStat.rules.isPrecomp c3 ∧
        (∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
            ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) ∧
        70000 ≤ U ∧
        (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T ∧
        BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (Nat.toB256 (rliBurnAmt o)) ∧
        (∀ k, k ≤ 3 → WClosed sevm (V k)) ∧ V 0 pre ∧ (∀ k, C3Blind c3 (V k)) ∧
        (∀ k : Fin 3, rliAmt sevm k.val ≠ 0 →
            CoinPushOkAt sevm
              (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256
                (Nat.toB256 (rliBurnAmt o))) (V k))
              (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256
                (Nat.toB256 (rliBurnAmt o))) (V (k + 1)))
              ((pre.getStor sevm.currentTarget).get (coinSlot k)) (rliAmt sevm k.val) U 0xaa0 0xb40) ∧
        (∀ k : Fin 3, rliAmt sevm k.val = 0 → ∀ b, V k b → V (k + 1) b)) ∧
      ∀ {G : Nat} (_hcode : sevm.code = code)
        (_hlen : 4 ≤ sevm.data.length)
        (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
        (_hstep : step s (rliEnvW sevm T.toNat) (decodeCall sevm) = some o)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty)
        (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hG : costImbalance s (rliEnvW sevm T.toNat) (argV3 sevm 0) + 5 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rliEnvW sevm T.toNat)
            o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧
          C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256
            (Nat.toB256 (rliBurnAmt o))) (V 3) post := by
  obtain ⟨s, hs, ready, hlive⟩ :=
    Curve3Pool3CrvHeadlines.pool_3crv_removeLiquidityImbalance_live_entry trace poolInstalled
    c3Installed joint fresh env notSystem target state
  have ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  refine ⟨s, hs, ready, fun {o} hburn => ?_⟩
  obtain ⟨V, U, htok, hcoin, hU, hT, hburn', hVc, hVb, hVs, hpush, hskip⟩ :=
    removeLiquidityImbalance_entry_literal_witness ht hfork hstatic hdepth hc3 hcoins hburn hfits
  exact ⟨V, U, ⟨htok, hcoin, hU, hT, hburn', hVc, hVb, hVs, hpush, hskip⟩,
    fun hcode hlen hcd hsel hstep hpc hid hkeep hG hGm => hlive hcode hfork hstatic hdepth hlen
      hcd hsel hstep htok hcoin hpc hid hkeep hU hT hburn' hVc hVb hVs hpush hskip hG hGm⟩

/-- **`pool_3crv_removeLiquidityOneCoin_live_entry` with its coin and 3Crv hypotheses discharged**,
for the coin `i` the call data names (`_hi` stays a premise: it fixes `i`). -/
theorem pool_3crv_removeLiquidityOneCoin_live_entry_literal
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state)
    {T : B256} (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp (coinOf sevm pre k))
    (hburn : BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (ocAmt sevm)) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out} {i : Fin 3} (_hi : i.val = (ocI sevm).toNat),
        pre.getCode (coinOf sevm pre i) = VyperNonreentrantDeployed.Token20.code →
        coinOf sevm pre i ≠ sevm.currentTarget → coinOf sevm pre i ≠ c3 →
        T20MoveFits (pre.getStor (coinOf sevm pre i)) sevm.currentTarget sevm.caller
          (Nat.toB256 (ocPushAmt o)) →
      ∃ (V : Nat → Devm → Prop) (U : Nat),
        (¬ sevm.benvStat.rules.isPrecomp c3 ∧
        (∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
            ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) ∧
        70000 ≤ U ∧
        (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T ∧
        BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (ocAmt sevm) ∧
        (∀ k, k ≤ 1 → WClosed sevm (V k)) ∧ V 0 pre ∧ C3Blind c3 (V 0) ∧
        CoinPushOkAt sevm
            (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 0))
            (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 1))
            ((pre.getStor sevm.currentTarget).get (coinSlot i)) (Nat.toB256 (ocPushAmt o)) U
            0x540 0x5e0) ∧
      ∀ {G : Nat} (_hcode : sevm.code = code)
        (_hlen : 4 ≤ sevm.data.length)
        (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
        (_hstep : step s (ocEnv sevm i T.toNat) (decodeCall sevm) = some o)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty)
        (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hG : costOneCoin s (ocEnv sevm i T.toNat) (ocAmt sevm).toNat i + 3 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 2000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ T' : Nat,
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (ocEnv sevm i T') o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧
          C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 1)
            post := by
  obtain ⟨s, hs, ready, hlive⟩ :=
    Curve3Pool3CrvHeadlines.pool_3crv_removeLiquidityOneCoin_live_entry trace poolInstalled
    c3Installed joint fresh env notSystem target state
  have ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  refine ⟨s, hs, ready, fun {o i} hi hcode hpool htc hfits => ?_⟩
  obtain ⟨V, U, htok, hcoin', hU, hT, hburn', hVc, hVb, hVs, hpush⟩ :=
    removeLiquidityOneCoin_entry_literal_witness ht hfork hstatic hdepth hc3 hcoin hcode hpool htc hburn hfits
  exact ⟨V, U, ⟨htok, hcoin', hU, hT, hburn', hVc, hVb, hVs, hpush⟩,
    fun hcode' hlen hcd hsel hstep hpc hid hkeep hG hGm => hlive hcode' hfork hstatic hdepth hlen
      hcd hsel hi hstep htok hcoin' hpc hid hkeep hU hT hburn' hVc hVb hVs hpush hG hGm⟩

end Bounded

end Blanc.Composition.Curve3Pool3CrvLiteralWitness
