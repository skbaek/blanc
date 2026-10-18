import Blanc.Composition.Curve3Pool3CrvU3
import Blanc.Composition.Curve3PoolCalleeLive
import Blanc.Lift.Curve3Pool.HistoryLive

/-!
# Curve 3pool composed with 3Crv: the headlines (U8e)

Over one configured history from a joint checkpoint (`JointCheckpoint`: the pool's checkpoint,
3Crv's layout invariant, the pool's token is 3Crv, 3Crv's minter is the pool):

* **Composed U6** — `pool_3crv_addLiquidity_live`, `pool_3crv_removeLiquidity_live`,
  `pool_3crv_removeLiquidityImbalance_live`, `pool_3crv_removeLiquidityOneCoin_live`: the history
  liveness wrappers of `HistoryLive.lean` with every 3Crv callee premise (`SupplyOkAt`,
  `MintOkAt`, `BurnOkAt`, `SupplyOk`, `BurnOk`) discharged by the deployed 3Crv
  (`Curve3PoolCalleeLive.lean`).  What remains of 3Crv is a fact about the call-site worlds `W`
  already describes for the coins: 3Crv's code at 3Crv, its supply word `T`, and 3Crv's acceptance
  of the amount (`MintFits` / `BurnFits`), with `W` closed under the 3Crv call.  The history
  supplies those facts at the frame's pre-state (`C3Ready`: 3Crv's code, the pool is 3Crv's
  minter, the pool's token is 3Crv).  `exchange` calls no 3Crv function; its history wrapper
  `pool_history_exchange_live` is already the composed statement.  Coin premises remain, per
  coin, with their own environment.
* **Composed U3** — `pool_3crv_u3` (`Curve3Pool3CrvU3.lean`) at 3Crv's ledger supplies, and
  `pool_3crv_u3_deployed`: from the recorded deployment state the admin-fee side condition of
  `U3Ledger` holds at every replayed state (`feeBounded_of_poolRun_init`).
* **U8 control** — `Curve3CrvToken.control_mutant_no_supplyFacet` (`Curve3CrvTokenCore.lean`): a
  mutated 3Crv whose `mint` skips the minter check accepts a non-minter mint, so it has no
  minter/supply facet with 3Crv's projections; the supply identity of `pool_3crv_history` rests on
  the minter rule.
-/

namespace Blanc.Composition.Curve3Pool3CrvHeadlines

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.ExecutionTrace
open Blanc.Composition.Curve3Pool3CrvJoint (JointCheckpoint)
open Blanc.Composition.Curve3PoolCalleeLive

/-- **3Crv as the pool's frame sees it**: 3Crv's code at `c3`, the pool `pool` is 3Crv's minter,
and the pool's token slot names `c3`. -/
def C3Ready (pool c3 : Adr) (pre : Devm) : Prop :=
  pre.getCode c3 = Curve3Crv.code ∧
    (Devm.getStor pre c3).get Curve3Crv.vyMinterSlot = pool.toB256 ∧
    ((Devm.getStor pre pool).get tokenSlot).toAdr = c3

theorem precomp_false {p : Prop} (h : ¬ p) : p = (false = true) :=
  propext ⟨fun hp => absurd hp h, fun hf => absurd hf Bool.false_ne_true⟩

section Joint

variable {pool c3 : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {ps₀ : Curve3Pool.State} {cs₀ : Blanc.Curve3Crv.State} {K₀ : Curve3Crv.Key → Prop}

/-- **The history gives `C3Ready` at every frame of the future state.** -/
theorem c3Ready_of_history (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress) {pre : Devm} (state : pre.state = future.state) :
    C3Ready pool c3 pre := by
  obtain ⟨-, -, -, -, s, -, -, hck, -, htoken, cs, -, hinv, hminter, -⟩ :=
    Curve3PoolSupply.pool_3crv_history trace poolInstalled c3Installed joint fresh env notSystem
  obtain ⟨hcode, -⟩ := Curve3Crv.c3crv_history_committed_derived trace c3Installed joint.c3 fresh
  have hst : ∀ a, Devm.getStor pre a = future.state.getStor a := fun a => by
    show pre.state.getStor a = _
    rw [state]
  refine ⟨?_, ?_, ?_⟩
  · show pre.state.getCode c3 = _
    rw [state]
    exact Curve3PoolSupply.c3crv_code_of_image hcode
  · rw [hst, hinv.minter, hminter]
  · rw [hst]
    have htok := hck.abs.token
    rw [htoken, joint.tokenIs] at htok
    have hw : (future.state.getStor pool).get tokenSlot = c3.toB256 :=
      B256.toNat_inj _ _ (htok.trans (by
        simp only [B256.toNat, B128.toNat, Adr.toB256, UInt64.toNat_zero, Nat.zero_shiftLeft,
          UInt32.toNat_toUInt64, Nat.zero_or, Adr.toNat]))
    rw [hw, toAdr_toB256]

/-- **Composed U6: `remove_liquidity` is live at every reachable state of the joint history**, its
3Crv `totalSupply()` and `burnFrom` calls discharged by the deployed 3Crv. -/
theorem pool_3crv_removeLiquidity_live (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out} {T : B256} {W : Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidity)
        (_hstep : step s (rlEnv sevm T) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hckeep : ∀ k : Fin 3,
          CallKeeps sevm ((pre.getStor sevm.currentTarget).get (coinSlot k)))
        (_hsk : StaticKeeps sevm ((pre.getStor sevm.currentTarget).get tokenSlot))
        (_htk : CallKeeps sevm ((pre.getStor sevm.currentTarget).get tokenSlot))
        (_hWc : WClosed sevm W) (_hWb : W pre) (_hU : 70000 ≤ U)
        (_hc3 : ∀ b, W b → b.getCode c3 = Curve3Crv.code ∧
          (Devm.getStor b c3).get Curve3Crv.vySupplySlot = T ∧
          BurnFits (Devm.getStor b c3) pool sevm.caller.toB256 (rlAmt sevm))
        (_hWs : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
          (∀ a, d.getCode a = b.getCode a) → W d)
        (_hWx : ∀ b d, W b → (∀ a, a ≠ c3 → Devm.getStor d a = Devm.getStor b a) →
          Devm.getStor d c3 = burnStor (Devm.getStor b c3) sevm.caller.toB256 (rlAmt sevm) →
          (∀ a, d.getCode a = b.getCode a) → W d)
        (_hpush : ∀ k : Fin 3, CoinPushOk sevm W
          ((pre.getStor sevm.currentTarget).get (coinSlot k))
          (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T) U)
        (_hG : 167000 + 5 * U ≤ G) (_hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rlEnv sevm T) o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state := by
  have ready := c3Ready_of_history trace poolInstalled c3Installed joint fresh env notSystem state
  obtain ⟨s, hs, hlive⟩ := pool_history_removeLiquidity_live trace poolInstalled joint.poolCk env
    target state
  refine ⟨s, hs, ready, ?_⟩
  intro o T W U G hcode hfork hstatic hdepth hlen hcd hsel hstep htok hcoin hpc hid hckeep hsk htk
    hWc hWb hU hc3 hWs hWx hpush hG hGm
  have ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  refine hlive hcode hfork hstatic hdepth hlen hcd hsel hstep (by rw [ht]; exact htok) hcoin hpc
    hid hckeep hsk htk hWc hWb ?_ hpush ?_ hG hGm
  · exact c3crv_supplyOk hfork hdepth (by rw [ht]; exact precomp_false htok) hU
      (fun b hb => by rw [ht]; exact ⟨(hc3 b hb).1, (hc3 b hb).2.1⟩) hWs
  · exact c3crv_burnOk hfork hstatic hdepth (by rw [ht]; exact precomp_false htok) hU
      (fun b hb => by
        rw [ht, target]
        exact ⟨(hc3 b hb).1, fun h => joint.apart h.symm, (hc3 b hb).2.2⟩)
      (by rw [ht]; exact hWx)

/-- **Composed U6: `add_liquidity` is live at every reachable state of the joint history**, its
3Crv `totalSupply()` and `mint` calls discharged by the deployed 3Crv. -/
theorem pool_3crv_addLiquidity_live (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out} {T B1 B2 : B256} {W W' Wm : Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selAddLiquidity)
        (_hstep : step s (alEnvW sevm T.toNat B1.toNat B2.toNat) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hWc : WClosed sevm W) (_hW'c : WClosed sevm W') (_hWmc : WClosed sevm Wm)
        (_hWb : W pre) (_hU : 70000 ≤ U)
        (_hc3 : ∀ b, W b → b.getCode c3 = Curve3Crv.code ∧
          (Devm.getStor b c3).get Curve3Crv.vySupplySlot = T)
        (_hWs : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
          (∀ a, d.getCode a = b.getCode a) → W d)
        (_hm3 : ∀ b, (if alAmt sevm 2 = 0 then W else W') b → b.getCode c3 = Curve3Crv.code ∧
          MintFits (Devm.getStor b c3) pool sevm.caller.toB256 (Nat.toB256 (alMintAmt o)))
        (_hWm : ∀ b d, (if alAmt sevm 2 = 0 then W else W') b →
          (∀ a, a ≠ c3 → Devm.getStor d a = Devm.getStor b a) →
          Devm.getStor d c3 =
            mintStor (Devm.getStor b c3) sevm.caller.toB256 (Nat.toB256 (alMintAmt o)) →
          (∀ a, d.getCode a = b.getCode a) → Wm d)
        (_hpull : ∀ k : Fin 3, k ≠ feeIndex → alAmt sevm k.val ≠ 0 →
          CoinPullOkAt sevm W W ((pre.getStor sevm.currentTarget).get (coinSlot k))
            (alAmt sevm k.val) U 0x760 0x820)
        (_hfee : alAmt sevm 2 ≠ 0 →
          CoinBalOkAt sevm W W ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B1 U
            0x53c 0x5a0 ∧
          CoinPullOkAt sevm W W' ((pre.getStor sevm.currentTarget).get (coinSlot 2))
            (alAmt sevm 2) U 0x760 0x820 ∧
          CoinBalOkAt sevm W' W' ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B2 U
            0x87c 0x8e0)
        (_hG : costAddLiquidity s (alEnvW sevm T.toNat B1.toNat B2.toNat) (argV3 sevm 0) + 7 * U ≤
          G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ e : Env,
          e.supply = some T.toNat ∧ step s e (decodeCall sevm) = some o ∧
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post e o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state := by
  have ready := c3Ready_of_history trace poolInstalled c3Installed joint fresh env notSystem state
  obtain ⟨s, hs, hlive⟩ := pool_history_addLiquidity_live trace poolInstalled joint.poolCk env
    target state
  refine ⟨s, hs, ready, ?_⟩
  intro o T B1 B2 W W' Wm U G hcode hfork hstatic hdepth hlen hcd hsel hstep htok hcoin hpc hid
    hkeep hWc hW'c hWmc hWb hU hc3 hWs hm3 hWm hpull hfee hG hGm
  have ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  refine hlive hcode hfork hstatic hdepth hlen hcd hsel hstep (by rw [ht]; exact htok) hcoin hpc
    hid hkeep hWc hW'c hWmc hWb ?_ hpull hfee ?_ hG hGm
  · exact c3crv_supplyOkAt hfork hdepth (by rw [ht]; exact precomp_false htok) hU (by decide)
      (by decide) (fun b hb => by rw [ht]; exact hc3 b hb) hWs
  · exact c3crv_mintOkAt hfork hstatic hdepth (by rw [ht]; exact precomp_false htok) hU
      (by decide) (by decide)
      (fun b hb => by
        rw [ht, target]
        exact ⟨(hm3 b hb).1, fun h => joint.apart h.symm, (hm3 b hb).2⟩)
      (by rw [ht]; exact hWm)

/-- **Composed U6: `remove_liquidity_imbalance` is live at every reachable state of the joint
history**, its 3Crv `totalSupply()` and `burnFrom` calls discharged by the deployed 3Crv. -/
theorem pool_3crv_removeLiquidityImbalance_live (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out} {T : B256} {W W' : Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
        (_hstep : step s (rliEnvW sevm T.toNat) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hWc : WClosed sevm W) (_hW'c : WClosed sevm W') (_hWb : W pre) (_hU : 70000 ≤ U)
        (_hc3 : ∀ b, W b → b.getCode c3 = Curve3Crv.code ∧
          (Devm.getStor b c3).get Curve3Crv.vySupplySlot = T ∧
          BurnFits (Devm.getStor b c3) pool sevm.caller.toB256 (Nat.toB256 (rliBurnAmt o)))
        (_hWs : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
          (∀ a, d.getCode a = b.getCode a) → W d)
        (_hWx : ∀ b d, W b → (∀ a, a ≠ c3 → Devm.getStor d a = Devm.getStor b a) →
          Devm.getStor d c3 =
            burnStor (Devm.getStor b c3) sevm.caller.toB256 (Nat.toB256 (rliBurnAmt o)) →
          (∀ a, d.getCode a = b.getCode a) → W' d)
        (_hpush : ∀ k : Fin 3, rliAmt sevm k.val ≠ 0 → CoinPushOkAt sevm W' W'
          ((pre.getStor sevm.currentTarget).get (coinSlot k)) (rliAmt sevm k.val) U 0xaa0 0xb40)
        (_hG : costImbalance s (rliEnvW sevm T.toNat) (argV3 sevm 0) + 5 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rliEnvW sevm T.toNat)
            o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state := by
  have ready := c3Ready_of_history trace poolInstalled c3Installed joint fresh env notSystem state
  obtain ⟨s, hs, hlive⟩ := pool_history_removeLiquidityImbalance_live trace poolInstalled joint.poolCk env
    target state
  refine ⟨s, hs, ready, ?_⟩
  intro o T W W' U G hcode hfork hstatic hdepth hlen hcd hsel hstep htok hcoin hpc hid hkeep hWc
    hW'c hWb hU hc3 hWs hWx hpush hG hGm
  have ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  refine hlive hcode hfork hstatic hdepth hlen hcd hsel hstep (by rw [ht]; exact htok) hcoin hpc
    hid hkeep hWc hW'c hWb ?_ ?_ hpush hG hGm
  · exact c3crv_supplyOkAt hfork hdepth (by rw [ht]; exact precomp_false htok) hU (by decide)
      (by decide) (fun b hb => by rw [ht]; exact ⟨(hc3 b hb).1, (hc3 b hb).2.1⟩) hWs
  · exact c3crv_burnOkAt hfork hstatic hdepth (by rw [ht]; exact precomp_false htok) hU
      (by decide) (by decide)
      (fun b hb => by
        rw [ht, target]
        exact ⟨(hc3 b hb).1, fun h => joint.apart h.symm, (hc3 b hb).2.2⟩)
      (by rw [ht]; exact hWx)

/-- **Composed U6: `remove_liquidity_one_coin` is live at every reachable state of the joint
history**, its 3Crv `totalSupply()` and `burnFrom` calls discharged by the deployed 3Crv. -/
theorem pool_3crv_removeLiquidityOneCoin_live (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out} {i : Fin 3} {T : B256} {W W' : Devm → Prop} {U G : Nat}
        (_hcode : sevm.code = code) (_hfork : CoveredFork sevm.benvStat.fork)
        (_hstatic : sevm.isStatic = false) (_hdepth : sevm.depth ≠ 0)
        (_hlen : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
        (_hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
        (_hi : i.val = (ocI sevm).toNat)
        (_hstep : step s (ocEnv sevm i T.toNat) (decodeCall sevm) = some o)
        (_htok : ¬ sevm.benvStat.rules.isPrecomp c3)
        (_hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
        (_hpc : pre.getCode sevm.currentTarget ≠ .empty) (_hid : IdReady sevm pre)
        (_hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
            ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
        (_hWc : WClosed sevm W) (_hW'c : WClosed sevm W') (_hWb : W pre) (_hU : 70000 ≤ U)
        (_hc3 : ∀ b, W b → b.getCode c3 = Curve3Crv.code ∧
          (Devm.getStor b c3).get Curve3Crv.vySupplySlot = T ∧
          BurnFits (Devm.getStor b c3) pool sevm.caller.toB256 (ocAmt sevm))
        (_hWs : ∀ b d, W b → (∀ a, Devm.getStor d a = Devm.getStor b a) →
          (∀ a, d.getCode a = b.getCode a) → W d)
        (_hWx : ∀ b d, W b → (∀ a, a ≠ c3 → Devm.getStor d a = Devm.getStor b a) →
          Devm.getStor d c3 = burnStor (Devm.getStor b c3) sevm.caller.toB256 (ocAmt sevm) →
          (∀ a, d.getCode a = b.getCode a) → W' d)
        (_hpush : CoinPushOkAt sevm W' W' ((pre.getStor sevm.currentTarget).get (coinSlot i))
          (Nat.toB256 (ocPushAmt o)) U 0x540 0x5e0)
        (_hG : costOneCoin s (ocEnv sevm i T.toNat) (ocAmt sevm).toNat i + 3 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 2000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ T' : Nat,
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (ocEnv sevm i T') o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state := by
  have ready := c3Ready_of_history trace poolInstalled c3Installed joint fresh env notSystem state
  obtain ⟨s, hs, hlive⟩ := pool_history_removeLiquidityOneCoin_live trace poolInstalled joint.poolCk env
    target state
  refine ⟨s, hs, ready, ?_⟩
  intro o i T W W' U G hcode hfork hstatic hdepth hlen hcd hsel hi hstep htok hcoin hpc hid hkeep
    hWc hW'c hWb hU hc3 hWs hWx hpush hG hGm
  have ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  refine hlive hcode hfork hstatic hdepth hlen hcd hsel hi hstep (by rw [ht]; exact htok) hcoin
    hpc hid hkeep hWc hW'c hWb ?_ ?_ hpush hG hGm
  · exact c3crv_supplyOkAt hfork hdepth (by rw [ht]; exact precomp_false htok) hU (by decide)
      (by decide) (fun b hb => by rw [ht]; exact ⟨(hc3 b hb).1, (hc3 b hb).2.1⟩) hWs
  · exact c3crv_burnOkAt hfork hstatic hdepth (by rw [ht]; exact precomp_false htok) hU
      (by decide) (by decide)
      (fun b hb => by
        rw [ht, target]
        exact ⟨(hc3 b hb).1, fun h => joint.apart h.symm, (hc3 b hb).2.2⟩)
      (by rw [ht]; exact hWx)

/-- **Composed U3 from the deployment.**  `pool_3crv_u3` over a joint history whose pool checkpoint
state is the recorded deployment state `Creation.poolInitState t₀`: the admin-fee side condition of
`U3Ledger` (`admin_fee ≤ 10^10`) holds at every replayed state (`feeBounded_of_poolRun_init`), so
the six U3 bounds hold at 3Crv's ledger supplies with no fee premise. -/
theorem pool_3crv_u3_deployed {t₀ : Nat} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 (Creation.poolInitState t₀) cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool (Creation.poolInitState t₀).coins
      (Creation.poolInitState t₀).token)
    (notSystem : pool ≠ systemAddress) :
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      (∃ s, PoolRun (Creation.poolInitState t₀) invs s ∧
        Checkpoint (future.state.getStor pool) s) ∧
      ∀ (pre : List PoolInvocation) (i : PoolInvocation) (post : List PoolInvocation)
        (sᵢ : Curve3Pool.State), invs = pre ++ i :: post →
        PoolRun (Creation.poolInitState t₀) pre sᵢ →
        (∃ blk : Block, (blk, i.frame) ∈ trace.blockFrames ∧
          i.env.time = blk.header.timestamp.toB256.toNat) ∧
        sᵢ.adminFee ≤ feeDen ∧
        ∃ o, step sᵢ i.env (decodeCall i.frame.sevm) = some o ∧
          RawEffect (Blanc.Exec.Frame.rootDeriv i.frame) i.frame.post i.env o ∧
          Curve3PoolSupply.SupplyObserved c3 i ∧
          supplyAfter (Curve3PoolSupply.supplyAt c3 i.frame.pre.state) o.calls =
            Curve3PoolSupply.supplyAt c3 i.frame.post.state ∧
          U3Ledger sᵢ i.env (decodeCall i.frame.sevm) o
            (Curve3PoolSupply.supplyAt c3 i.frame.pre.state)
            (Curve3PoolSupply.supplyAt c3 i.frame.post.state) := by
  obtain ⟨invs, obs, auth, run, per⟩ :=
    Curve3PoolSupply.pool_3crv_u3 trace poolInstalled c3Installed joint fresh env notSystem
  refine ⟨invs, obs, auth, run, fun pre i post sᵢ split hpre => ?_⟩
  obtain ⟨time, -, rest⟩ := per pre i post sᵢ split hpre
  exact ⟨time, (feeBounded_of_poolRun_init hpre).le_feeDen, rest⟩

/-- **U8 control** (`Curve3CrvToken.control_mutant_no_supplyFacet`): a mutated 3Crv whose `mint`
skips the minter check has no minter/supply facet with 3Crv's projections. -/
theorem u8_control :
    ¬ ∃ F : Token.SupplyFacet Curve3CrvToken.mutantBook,
      F.minter = (·.minter) ∧ F.mintOf = Curve3CrvToken.c3crvMintOf :=
  Curve3CrvToken.control_mutant_no_supplyFacet

end Joint

end Blanc.Composition.Curve3Pool3CrvHeadlines
