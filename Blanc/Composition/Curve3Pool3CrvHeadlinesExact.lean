import Blanc.Composition.Curve3Pool3CrvExactAssembly

/-!
# Curve 3pool composed with 3Crv: the exact-gas headlines at message entry (U6/U8)

The exact twins of `Curve3Pool3CrvHeadlines.lean`'s composed entry forms. Over one configured
history from a joint checkpoint, for a message `msg` to the pool whose state is the future state:
the replayed state `s` is chosen once, 3Crv is ready at the entry (`C3Ready`), and each entry that
calls 3Crv executes with exact gas, its 3Crv calls answered by the deployed 3Crv's own named exact
profiles (`Curve3Pool3CrvExactAssembly.lean`), so no 3Crv exactness premise remains: 3Crv's state
is stated once on the entry (supply `T`, `BurnFits`/`MintFits`), and the closed cost `c`
(`rlExactCost`/`alExactCost`/`rliExactCost`/`ocExactCost` at `rlC3Calls`/… of the base message)
is fixed before the residual gas. The coin calls keep their exact profiles over the caller's
coin chain `V` (environment premises, as in the bounded rows), and `hkeep` stays an
entry-execution premise.

* `pool_3crv_removeLiquidity_live_exact`, `pool_3crv_addLiquidity_live_exact`,
  `pool_3crv_removeLiquidityImbalance_live_exact`, `pool_3crv_removeLiquidityOneCoin_live_exact`;
* `exchange` calls no 3Crv function: its composed statement is
  `Curve3Pool.pool_history_exchange_live_exact`.
-/

namespace Blanc.Composition.Curve3Pool3CrvHeadlinesExact

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.ExecutionTrace Blanc.StableSwapNewton
open Blanc.Composition.Curve3Pool3CrvJoint (JointCheckpoint)
open Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3Ready C3With C3Blind c3Ready_of_history
  c3With_wClosed)
open Blanc.Composition.Curve3Pool3CrvExactAssembly

section Joint

variable {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop}

/-- **Composed U6, exact gas at message entry: `remove_liquidity`.** The 3Crv calls are 3Crv's own
named profiles (`rlC3Calls`), so their debits are closed functions of the base message; the coin
calls keep their exact profiles as environment premises over the caller's coin chain `V`. -/
theorem pool_3crv_removeLiquidity_live_exact
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∀ {o : Out} {T : B256} {V : Nat → Devm → Prop} {U : Nat}
        (pushD : Nat → Devm → List B256 → Mem → Nat) (pushN : Nat → Devm → List B256 → Mem → Devm)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false) (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidity)
        (_hstep : step s (rlEnv (initSevm msg) T) (decodeCall (initSevm msg)) = some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T)
        (_hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
          (rlAmt (initSevm msg)))
        (_hVc : ∀ k, k ≤ 3 → WClosed (initSevm msg) (V k)) (_hVb : V 0 (initDevm msg))
        (_hVs : ∀ k, C3Blind c3 (V k))
        (_hpush : ∀ i, i < 3 → MutableCallProfile (initSevm msg)
          (C3With c3 (Devm.getStor (initDevm msg) c3) (V i))
          (C3With c3 (Devm.getStor (initDevm msg) c3) (V (i + 1)))
          (coinAt ((initDevm msg).getStor msg.currentTarget) i)
          (transferSel ++ msg.caller.toB256.toBytes ++
            (balAt ((initDevm msg).getStor msg.currentTarget) i * rlAmt (initSevm msg) / T).toBytes)
          RawCallOk U 0x520 0x44 0x5c0 (pushD i) (pushN i)),
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
  have ready := c3Ready_of_history trace poolInstalled c3Installed joint fresh env notSystem
    (pre := initDevm msg) state
  obtain ⟨s, hs, hlive⟩ := pool_history_removeLiquidity_live_exact trace poolInstalled joint.poolCk env
    target state
  refine ⟨s, hs, ready, ?_⟩
  intro o T V U pushD pushN hcode hfork hstatic hdepth hlen hcd hsel hstep htok hcoin hpc hid hU hT
    hburn hVc hVb hVs hpush
  have ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  have hne : (initSevm msg).currentTarget ≠ c3 := by
    show msg.currentTarget ≠ c3
    rw [target]; exact joint.apart
  subst target
  exact hlive _ hcode hfork hstatic hdepth hlen hcd hsel hstep (by rw [ht]; exact htok) hcoin hpc hid
    (fun k hk => by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
      all_goals exact c3With_wClosed hne (hVc _ (by decide)))
    ⟨⟨ready.1, rfl⟩, hVb⟩
    (rlExactPremises_c3crv ht hne hfork hstatic hdepth htok hU hT hburn hVs hpush)

/-- **Composed U6, exact gas at message entry: `add_liquidity`.** The 3Crv calls are 3Crv's own
named profiles (`alC3Calls`), so their debits are closed functions of the base message; the coin
calls keep their exact profiles as environment premises over the caller's coin chain `V`. -/
theorem pool_3crv_addLiquidity_live_exact
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∀ {o : Out} {T B1 B2 : B256} {V : Nat → Devm → Prop} {U : Nat}
        (pullD : Nat → Devm → List B256 → Mem → Nat) (pullN : Nat → Devm → List B256 → Mem → Devm)
        (balBD balAD : Devm → List B256 → Mem → Nat) (balBN balAN : Devm → List B256 → Mem → Devm)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false) (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selAddLiquidity)
        (_hstep : step s (alEnvW (initSevm msg) T.toNat B1.toNat B2.toNat)
          (decodeCall (initSevm msg)) = some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T)
        (_hmint : MintFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
          (Nat.toB256 (alMintAmt o)))
        (_hVc : ∀ k, k ≤ 3 → WClosed (initSevm msg) (V k)) (_hVb : V 0 (initDevm msg))
        (_hVs : ∀ k, C3Blind c3 (V k))
        (_hskip : ∀ k : Fin 3, alAmt (initSevm msg) k.val = 0 → ∀ b, V k b → V (k + 1) b)
        (_hpull : ∀ k, k < 3 → alAmt (initSevm msg) k ≠ 0 →
          MutableCallProfile (initSevm msg) (C3With c3 (Devm.getStor (initDevm msg) c3) (V k))
            (C3With c3 (Devm.getStor (initDevm msg) c3) (V (k + 1)))
            (coinAt ((initDevm msg).getStor msg.currentTarget) k)
            (transferFromSel ++ msg.caller.toB256.toBytes ++ msg.currentTarget.toB256.toBytes ++
              (alAmt (initSevm msg) k).toBytes) RawCallOk U 0x760 0x64 0x820 (pullD k) (pullN k))
        (_hbalB : alAmt (initSevm msg) 2 ≠ 0 →
          StaticWordCallProfile (initSevm msg) (C3With c3 (Devm.getStor (initDevm msg) c3) (V 2))
            (C3With c3 (Devm.getStor (initDevm msg) c3) (V 2))
            (coinAt ((initDevm msg).getStor msg.currentTarget) 2)
            (balanceOfData msg.currentTarget) B1 U 0x53c 0x24 0x5a0 balBD balBN)
        (_hbalA : alAmt (initSevm msg) 2 ≠ 0 →
          StaticWordCallProfile (initSevm msg) (C3With c3 (Devm.getStor (initDevm msg) c3) (V 3))
            (C3With c3 (Devm.getStor (initDevm msg) c3) (V 3))
            (coinAt ((initDevm msg).getStor msg.currentTarget) 2)
            (balanceOfData msg.currentTarget) B2 U 0x87c 0x24 0x8e0 balAD balAN),
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
  have ready := c3Ready_of_history trace poolInstalled c3Installed joint fresh env notSystem
    (pre := initDevm msg) state
  obtain ⟨s, hs, hlive⟩ := pool_history_addLiquidity_live_exact trace poolInstalled joint.poolCk env
    target state
  refine ⟨s, hs, ready, ?_⟩
  intro o T B1 B2 V U pullD pullN balBD balAD balBN balAN hcode hfork hstatic hdepth hlen hcd hsel
    hstep htok hcoin hpc hid hU hT hmint hVc hVb hVs hskip hpull hbalB hbalA
  have ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  have hne : (initSevm msg).currentTarget ≠ c3 := by
    show msg.currentTarget ≠ c3
    rw [target]; exact joint.apart
  subst target
  exact hlive _ hcode hfork hstatic hdepth hlen hcd hsel hstep (by rw [ht]; exact htok) hcoin hpc hid
    (fun k hk => by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
      all_goals exact c3With_wClosed hne (hVc _ (by decide)))
    ⟨⟨ready.1, rfl⟩, hVb⟩
    (fun k hz b hb => match k, hz, hb with
      | ⟨0, _⟩, hz, hb => ⟨hb.1, hskip 0 hz b hb.2⟩
      | ⟨1, _⟩, hz, hb => ⟨hb.1, hskip 1 hz b hb.2⟩
      | ⟨2, _⟩, hz, hb => ⟨hb.1, hskip 2 hz b hb.2⟩)
    (alExactPremises_c3crv ht hne hfork hstatic hdepth htok hU hT hmint hVs hpull hbalB hbalA)

/-- **Composed U6, exact gas at message entry: `remove_liquidity_imbalance`.** The 3Crv calls are 3Crv's own
named profiles (`rliC3Calls`), so their debits are closed functions of the base message; the coin
calls keep their exact profiles as environment premises over the caller's coin chain `V`. -/
theorem pool_3crv_removeLiquidityImbalance_live_exact
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∀ {o : Out} {T : B256} {V : Nat → Devm → Prop} {U : Nat}
        (pushD : Nat → Devm → List B256 → Mem → Nat) (pushN : Nat → Devm → List B256 → Mem → Devm)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false) (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityImbalance)
        (_hstep : step s (rliEnvW (initSevm msg) T.toNat) (decodeCall (initSevm msg)) = some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T)
        (_hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
          (Nat.toB256 (rliBurnAmt o)))
        (_hVc : ∀ k, k ≤ 3 → WClosed (initSevm msg) (V k)) (_hVb : V 0 (initDevm msg))
        (_hVs : ∀ k, C3Blind c3 (V k))
        (_hskip : ∀ k : Fin 3, rliAmt (initSevm msg) k.val = 0 → ∀ b, V k b → V (k + 1) b)
        (_hpush : ∀ k, k < 3 → rliAmt (initSevm msg) k ≠ 0 →
          MutableCallProfile (initSevm msg)
            (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
              (Nat.toB256 (rliBurnAmt o))) (V k))
            (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
              (Nat.toB256 (rliBurnAmt o))) (V (k + 1)))
            (((initDevm msg).getStor msg.currentTarget).get (coinsBase + Nat.toB256 k))
            (transferSel ++ msg.caller.toB256.toBytes ++ (rliAmt (initSevm msg) k).toBytes)
            RawCallOk U 0xaa0 0x44 0xb40 (pushD k) (pushN k)),
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
  have ready := c3Ready_of_history trace poolInstalled c3Installed joint fresh env notSystem
    (pre := initDevm msg) state
  obtain ⟨s, hs, hlive⟩ := pool_history_removeLiquidityImbalance_live_exact trace poolInstalled joint.poolCk env
    target state
  refine ⟨s, hs, ready, ?_⟩
  intro o T V U pushD pushN hcode hfork hstatic hdepth hlen hcd hsel hstep htok hcoin hpc hid hU hT
    hburn hVc hVb hVs hskip hpush
  have ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  have hne : (initSevm msg).currentTarget ≠ c3 := by
    show msg.currentTarget ≠ c3
    rw [target]; exact joint.apart
  subst target
  exact hlive _ hcode hfork hstatic hdepth hlen hcd hsel hstep (by rw [ht]; exact htok) hcoin hpc hid
    (fun k hk => by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
      all_goals exact c3With_wClosed hne (hVc _ (by decide)))
    ⟨⟨ready.1, rfl⟩, hVb⟩
    (rliExactPremises_c3crv ht hne hfork hstatic hdepth htok hU hT hburn hVs hpush)
    (fun k hz b hb => ⟨hb.1, hskip k hz b hb.2⟩)

/-- **Composed U6, exact gas at message entry: `remove_liquidity_one_coin`.** The 3Crv calls are 3Crv's own
named profiles (`ocC3Calls`), so their debits are closed functions of the base message; the coin
calls keep their exact profiles as environment premises over the caller's coin chain `V`. -/
theorem pool_3crv_removeLiquidityOneCoin_live_exact
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {msg : Msg} (target : msg.currentTarget = pool) (state : msg.benv.state = future.state) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 (initDevm msg) ∧
      ∀ {o : Out} {i : Fin 3} {T : B256} {V : Nat → Devm → Prop} {U : Nat}
        (pushD : Devm → List B256 → Mem → Nat) (pushN : Devm → List B256 → Mem → Devm)
        (_hcode : (initSevm msg).code = code)
        (_hfork : CoveredFork (initSevm msg).benvStat.fork)
        (_hstatic : (initSevm msg).isStatic = false) (_hdepth : (initSevm msg).depth ≠ 0)
        (_hlen : 4 ≤ (initSevm msg).data.length) (_hcd : (initSevm msg).data.length < 2 ^ 256)
        (_hsel : Sevm.selector (initSevm msg) = selRemoveLiquidityOneCoin)
        (_hi : i.val = (ocI (initSevm msg)).toNat)
        (_hstep : step s (ocEnv (initSevm msg) i T.toNat) (decodeCall (initSevm msg)) = some o)
        (_htok : ¬ (initSevm msg).benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
          (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
        (_hid : IdReady (initSevm msg) (initDevm msg))
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor (initDevm msg) c3).get Curve3Crv.vySupplySlot = T)
        (_hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
          (ocAmt (initSevm msg)))
        (_hVc : ∀ k, k ≤ 1 → WClosed (initSevm msg) (V k)) (_hVb : V 0 (initDevm msg))
        (_hVs : C3Blind c3 (V 0))
        (_hpush : MutableCallProfile (initSevm msg)
          (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
            (ocAmt (initSevm msg))) (V 0))
          (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
            (ocAmt (initSevm msg))) (V 1))
          (((initDevm msg).getStor msg.currentTarget).get (coinsBase + ocI (initSevm msg)))
          (transferSel ++ msg.caller.toB256.toBytes ++ (Nat.toB256 (ocPushAmt o)).toBytes) RawCallOk
          U 0x540 0x44 0x5e0 pushD pushN),
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
  have ready := c3Ready_of_history trace poolInstalled c3Installed joint fresh env notSystem
    (pre := initDevm msg) state
  obtain ⟨s, hs, hlive⟩ := pool_history_removeLiquidityOneCoin_live_exact trace poolInstalled joint.poolCk env
    target state
  refine ⟨s, hs, ready, ?_⟩
  intro o i T V U pushD pushN hcode hfork hstatic hdepth hlen hcd hsel hi hstep htok hcoin hpc hid hU
    hT hburn hVc hVb hVs hpush
  have ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  have hne : (initSevm msg).currentTarget ≠ c3 := by
    show msg.currentTarget ≠ c3
    rw [target]; exact joint.apart
  subst target
  exact hlive _ hcode hfork hstatic hdepth hlen hcd hsel hi hstep (by rw [ht]; exact htok) hcoin hpc
    hid (c3With_wClosed hne (hVc 0 (by decide))) (c3With_wClosed hne (hVc 0 (by decide)))
    ⟨⟨ready.1, rfl⟩, hVb⟩ (c3With_wClosed hne (hVc 1 (by decide)))
    (ocExactPremises_c3crv ht hne hfork hstatic hdepth htok hU hT hburn hVs hpush)

end Joint

end Blanc.Composition.Curve3Pool3CrvHeadlinesExact
