import Blanc.Composition.Curve3Pool3CrvU3
import Blanc.Composition.Curve3PoolCalleeLive
import Blanc.Lift.Curve3Pool.HistoryLive

/-!
# Curve 3pool composed with 3Crv: the headlines (U8e)

Over one configured history from a joint checkpoint (`JointCheckpoint`: the pool's checkpoint,
3Crv's layout invariant, the pool's token is 3Crv, 3Crv's minter is the pool):

* **Composed U6** — `pool_3crv_{addLiquidity,removeLiquidity,removeLiquidityImbalance,
  removeLiquidityOneCoin}_live_entry`: the history liveness wrappers of `HistoryLive.lean` with
  every 3Crv callee premise (`SupplyOkAt`, `MintOkAt`, `BurnOkAt`, `SupplyOk`, `BurnOkTo`)
  discharged by the deployed 3Crv (`Curve3PoolCalleeLive.lean`) over worlds whose 3Crv part is
  fixed (`C3At c3 (pre.getStor c3)` and its post-mint / post-burn storage, `WClosed` proved by
  `c3At_wClosed`), so 3Crv's state is stated once on `pre` (supply `T`, `MintFits` /
  `BurnFits`).  The history supplies the rest at the frame's pre-state (`C3Ready`: 3Crv's code,
  the pool is 3Crv's minter, the pool's token is 3Crv).  The per-coin premises remain, over the
  caller's coin world chain `V 0 → V 1 → …` (`C3With`): each state-changing coin call moves to the
  next world.  `exchange` calls no 3Crv function; its history wrapper `pool_history_exchange_live`
  is already the composed statement.
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

/-! ## Composed U6 with 3Crv's state stated once, at the frame's entry

The history wrappers of `HistoryLive.lean` ask the caller for a world chain `W 0 → W 1 → …`
describing 3Crv and the coins at each call site.  Here the 3Crv part is fixed: `C3At c3 σ` is the
set of worlds whose 3Crv code is 3Crv's and whose 3Crv storage is `σ`; `σ` is the frame entry's
3Crv storage `pre.getStor c3` up to the 3Crv call and `mintStor …` / `burnStor …` of it after.
This is sound because the frame reads 3Crv's supply first (`SupplyFirst`: no state-changing child
precedes the `totalSupply()` read), the pool's own steps write only the pool's storage
(`c3At_wClosed`), and the coin children keep 3Crv's storage and code (the per-coin premises are
stated over these worlds, so a coin call must leave 3Crv as it found it: the R1 per-coin
environment premise).  So 3Crv's acceptance of the call (supply `T`, `MintFits`, `BurnFits`) is a
fact about `pre` alone.

The coin part is the caller's own chain `V 0 → V 1 → …` (`C3With c3 σ (V k)`): coin `k`'s
state-changing call moves `V k` to `V (k + 1)`, a skipped call stays (`V k ⊆ V (k + 1)`), and `V`
must not read 3Crv's storage (`C3Blind`), so 3Crv's own calls keep it.  A positive transfer
changes a coin's ledger, so no single coin world closed under it is satisfiable by an honest coin.
(`removeLiquidity_premises_satisfiable` and its siblings in `Curve3Pool3CrvLiveWitness.lean`
instantiate the frame theorems' world chains with `Token20` coins and the deployed 3Crv, of the
`C3At c3 σ ∧ coins-as-at-entry` shape these entry forms take.) -/

/-- **The worlds whose 3Crv is as given**: 3Crv's code at `c3` and 3Crv's storage `σ`. -/
def C3At (c3 : Adr) (σ : Stor) (b : Devm) : Prop :=
  b.getCode c3 = Curve3Crv.code ∧ Devm.getStor b c3 = σ

/-- **The pool's own steps keep 3Crv**: they write only the frame's own storage. -/
theorem c3At_wClosed {sevm : Sevm} {c3 : Adr} {σ : Stor} (hne : sevm.currentTarget ≠ c3) :
    WClosed sevm (C3At c3 σ) where
  st _ _ _ _ h := h
  sload b k h :=
    ⟨(afterSload_getCode sevm b k c3).trans h.1, (afterSload_getStor sevm b k c3).trans h.2⟩
  sstore b k v h :=
    ⟨(afterSstore_getCode sevm b k v c3).trans h.1,
      (afterSstore_getStor_ne sevm b k v c3 hne).trans h.2⟩
  sha _ _ _ hp h := ⟨(hp.code c3).trans h.1, (hp.stor c3).trans h.2⟩
  log _ _ h := h

/-- A world with the same storage and code is in `C3At c3 σ` too. -/
theorem c3At_keep {c3 : Adr} {σ : Stor} {b d : Devm} (h : C3At c3 σ b)
    (hs : ∀ a, Devm.getStor d a = Devm.getStor b a) (hc : ∀ a, d.getCode a = b.getCode a) :
    C3At c3 σ d :=
  ⟨(hc c3).trans h.1, (hs c3).trans h.2⟩

/-- 3Crv's `mint(d, v)` moves `C3At c3 σ` to `C3At c3 (mintStor σ d v)`. -/
theorem c3At_mint {c3 : Adr} {σ : Stor} {x v : B256} {b d : Devm} (h : C3At c3 σ b)
    (hs : Devm.getStor d c3 = mintStor (Devm.getStor b c3) x v)
    (hc : ∀ a, d.getCode a = b.getCode a) : C3At c3 (mintStor σ x v) d :=
  ⟨(hc c3).trans h.1, hs.trans (by rw [h.2])⟩

/-- 3Crv's `burnFrom(f, v)` moves `C3At c3 σ` to `C3At c3 (burnStor σ f v)`. -/
theorem c3At_burn {c3 : Adr} {σ : Stor} {x v : B256} {b d : Devm} (h : C3At c3 σ b)
    (hs : Devm.getStor d c3 = burnStor (Devm.getStor b c3) x v)
    (hc : ∀ a, d.getCode a = b.getCode a) : C3At c3 (burnStor σ x v) d :=
  ⟨(hc c3).trans h.1, hs.trans (by rw [h.2])⟩

/-- **A world with 3Crv as given and the caller's coin facts `V`.** -/
def C3With (c3 : Adr) (σ : Stor) (V : Devm → Prop) (b : Devm) : Prop :=
  C3At c3 σ b ∧ V b

/-- **`V` does not read 3Crv's storage**: it survives a step that keeps every account's code and
every account's storage but 3Crv's (what a 3Crv call does). -/
def C3Blind (c3 : Adr) (V : Devm → Prop) : Prop :=
  ∀ b d, V b → (∀ a, a ≠ c3 → Devm.getStor d a = Devm.getStor b a) →
    (∀ a, d.getCode a = b.getCode a) → V d

theorem c3With_wClosed {sevm : Sevm} {c3 : Adr} {σ : Stor} {V : Devm → Prop}
    (hne : sevm.currentTarget ≠ c3) (hV : WClosed sevm V) : WClosed sevm (C3With c3 σ V) where
  st b S M G h := ⟨(c3At_wClosed hne).st b S M G h.1, hV.st b S M G h.2⟩
  sload b k h := ⟨(c3At_wClosed hne).sload b k h.1, hV.sload b k h.2⟩
  sstore b k v h := ⟨(c3At_wClosed hne).sstore b k v h.1, hV.sstore b k v h.2⟩
  sha b b' rd hp h := ⟨(c3At_wClosed hne).sha b b' rd hp h.1, hV.sha b b' rd hp h.2⟩
  log b l h := ⟨(c3At_wClosed hne).log b l h.1, hV.log b l h.2⟩

/-- A static 3Crv call keeps `C3With c3 σ V`. -/
theorem c3With_keep {c3 : Adr} {σ : Stor} {V : Devm → Prop} {b d : Devm} (hV : C3Blind c3 V)
    (h : C3With c3 σ V b) (hs : ∀ a, Devm.getStor d a = Devm.getStor b a)
    (hc : ∀ a, d.getCode a = b.getCode a) : C3With c3 σ V d :=
  ⟨c3At_keep h.1 hs hc, hV b d h.2 (fun a _ => hs a) hc⟩

/-- **Composed U6, entry form: `remove_liquidity`.** 3Crv's state is stated once on `pre` (supply
`T`, `BurnFits`); coin `k`'s push moves the coin chain from `V k` to `V (k + 1)` over 3Crv's entry
storage. -/
theorem pool_3crv_removeLiquidity_live_entry
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out} {T : B256} {V : Nat → Devm → Prop} {U G : Nat}
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
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T)
        (_hburn : BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (rlAmt sevm))
        (_hVc : ∀ k, k ≤ 3 → WClosed sevm (V k)) (_hVb : V 0 pre) (_hVs : ∀ k, C3Blind c3 (V k))
        (_hpush : ∀ k : Fin 3, CoinPushOkAt sevm (C3With c3 (Devm.getStor pre c3) (V k))
          (C3With c3 (Devm.getStor pre c3) (V (k + 1)))
          ((pre.getStor sevm.currentTarget).get (coinSlot k))
          (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T) U 0x520 0x5c0)
        (_hG : 167000 + 5 * U ≤ G) (_hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rlEnv sevm T) o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state := by
  have ready := c3Ready_of_history trace poolInstalled c3Installed joint fresh env notSystem state
  obtain ⟨s, hs, hlive⟩ := pool_history_removeLiquidity_live trace poolInstalled joint.poolCk env
    target state
  refine ⟨s, hs, ready, ?_⟩
  intro o T V U G hcode hfork hstatic hdepth hlen hcd hsel hstep htok hcoin hpc hid hckeep hsk htk
    hU hT hburn hVc hVb hVs hpush hG hGm
  have ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  have hne : sevm.currentTarget ≠ c3 := by rw [target]; exact joint.apart
  let σ := Devm.getStor pre c3
  let σb := burnStor σ sevm.caller.toB256 (rlAmt sevm)
  let W : Nat → Devm → Prop := fun j => match j with
    | 4 => C3With c3 σb (V 3)
    | j => C3With c3 σ (V j)
  refine hlive (W := W) hcode hfork hstatic hdepth hlen hcd hsel hstep (by rw [ht]; exact htok)
    hcoin hpc hid hckeep hsk htk ?_ ⟨⟨ready.1, rfl⟩, hVb⟩ ?_ ?_ ?_ hG hGm
  · intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    all_goals exact c3With_wClosed hne (hVc _ (by decide))
  · exact c3crv_supplyOk hfork hdepth (by rw [ht]; exact precomp_false htok) hU
      (fun b hb => by rw [ht, hb.1.2]; exact ⟨hb.1.1, hT⟩)
      (fun b d hb hs hc => c3With_keep (hVs 0) hb hs hc)
  · intro k
    match k with
    | ⟨0, _⟩ => exact hpush 0
    | ⟨1, _⟩ => exact hpush 1
    | ⟨2, _⟩ => exact hpush 2
  · refine (c3crv_burnOkAt (ii := 0x61c) (oi := 0x6a0) hfork hstatic hdepth
      (by rw [ht]; exact precomp_false htok) hU (by decide) (by decide) ?_ ?_).burnOkTo
    · intro b hb
      rw [ht, target, hb.1.2]
      exact ⟨hb.1.1, fun h => joint.apart h.symm, hburn⟩
    · rw [ht]
      exact fun b d hb ho hs hc => ⟨c3At_burn hb.1 hs hc, hVs 3 b d hb.2 ho hc⟩

/-- **Composed U6, entry form: `add_liquidity`.** 3Crv's state is stated once on `pre` (supply
`T`, `MintFits` for the minted amount); coin `k`'s pull moves the coin chain from `V k` to
`V (k + 1)` over 3Crv's entry storage, the fee coin's two balance reads in `V 2` and `V 3`. -/
theorem pool_3crv_addLiquidity_live_entry
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out} {T B1 B2 : B256} {V : Nat → Devm → Prop} {U G : Nat}
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
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T)
        (_hmint : MintFits (Devm.getStor pre c3) pool sevm.caller.toB256
          (Nat.toB256 (alMintAmt o)))
        (_hVc : ∀ k, k ≤ 3 → WClosed sevm (V k)) (_hVb : V 0 pre) (_hVs : ∀ k, C3Blind c3 (V k))
        (_hpull : ∀ k : Fin 3, k ≠ feeIndex → alAmt sevm k.val ≠ 0 →
          CoinPullOkAt sevm (C3With c3 (Devm.getStor pre c3) (V k))
            (C3With c3 (Devm.getStor pre c3) (V (k + 1)))
            ((pre.getStor sevm.currentTarget).get (coinSlot k)) (alAmt sevm k.val) U 0x760 0x820)
        (_hskip : ∀ k : Fin 3, alAmt sevm k.val = 0 → ∀ b, V k b → V (k + 1) b)
        (_hfee : alAmt sevm 2 ≠ 0 →
          CoinBalOkAt sevm (C3With c3 (Devm.getStor pre c3) (V 2))
            (C3With c3 (Devm.getStor pre c3) (V 2))
            ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B1 U 0x53c 0x5a0 ∧
          CoinPullOkAt sevm (C3With c3 (Devm.getStor pre c3) (V 2))
            (C3With c3 (Devm.getStor pre c3) (V 3))
            ((pre.getStor sevm.currentTarget).get (coinSlot 2)) (alAmt sevm 2) U 0x760 0x820 ∧
          CoinBalOkAt sevm (C3With c3 (Devm.getStor pre c3) (V 3))
            (C3With c3 (Devm.getStor pre c3) (V 3))
            ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B2 U 0x87c 0x8e0)
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
  intro o T B1 B2 V U G hcode hfork hstatic hdepth hlen hcd hsel hstep htok hcoin hpc hid hkeep hU
    hT hmint hVc hVb hVs hpull hskip hfee hG hGm
  have ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  have hne : sevm.currentTarget ≠ c3 := by rw [target]; exact joint.apart
  let σ := Devm.getStor pre c3
  let σm := mintStor σ sevm.caller.toB256 (Nat.toB256 (alMintAmt o))
  let W : Nat → Devm → Prop := fun j => match j with
    | 4 => C3With c3 σm (V 3)
    | j => C3With c3 σ (V j)
  refine hlive (W := W) hcode hfork hstatic hdepth hlen hcd hsel hstep (by rw [ht]; exact htok)
    hcoin hpc hid hkeep ?_ ⟨⟨ready.1, rfl⟩, hVb⟩ ?_ ?_ ?_ hfee ?_ hG hGm
  · intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
    all_goals exact c3With_wClosed hne (hVc _ (by decide))
  · exact c3crv_supplyOkAt hfork hdepth (by rw [ht]; exact precomp_false htok) hU (by decide)
      (by decide) (fun b hb => by rw [ht, hb.1.2]; exact ⟨hb.1.1, hT⟩)
      (fun b d hb hs hc => c3With_keep (hVs 0) hb hs hc)
  · intro k
    match k with
    | ⟨0, _⟩ => exact hpull 0
    | ⟨1, _⟩ => exact hpull 1
    | ⟨2, _⟩ => exact hpull 2
  · intro k hz b hb
    match k, hz, hb with
    | ⟨0, _⟩, hz, hb => exact ⟨hb.1, hskip 0 hz b hb.2⟩
    | ⟨1, _⟩, hz, hb => exact ⟨hb.1, hskip 1 hz b hb.2⟩
    | ⟨2, _⟩, hz, hb => exact ⟨hb.1, hskip 2 hz b hb.2⟩
  · refine c3crv_mintOkAt hfork hstatic hdepth (by rw [ht]; exact precomp_false htok) hU
      (by decide) (by decide) ?_ ?_
    · intro b hb
      rw [ht, target, hb.1.2]
      exact ⟨hb.1.1, fun h => joint.apart h.symm, hmint⟩
    · rw [ht]
      exact fun b d hb ho hs hc => ⟨c3At_mint hb.1 hs hc, hVs 3 b d hb.2 ho hc⟩

/-- **Composed U6, entry form: `remove_liquidity_imbalance`.** 3Crv's state is stated once on `pre`
(supply `T`, `BurnFits` for the burned amount); coin `k`'s push (when its amount is nonzero) moves
the coin chain from `V k` to `V (k + 1)` over the burned 3Crv storage; the frame ends in
`V 3`. -/
theorem pool_3crv_removeLiquidityImbalance_live_entry
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out} {T : B256} {V : Nat → Devm → Prop} {U G : Nat}
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
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T)
        (_hburn : BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256
          (Nat.toB256 (rliBurnAmt o)))
        (_hVc : ∀ k, k ≤ 3 → WClosed sevm (V k)) (_hVb : V 0 pre) (_hVs : ∀ k, C3Blind c3 (V k))
        (_hpush : ∀ k : Fin 3, rliAmt sevm k.val ≠ 0 →
          CoinPushOkAt sevm
            (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256
              (Nat.toB256 (rliBurnAmt o))) (V k))
            (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256
              (Nat.toB256 (rliBurnAmt o))) (V (k + 1)))
            ((pre.getStor sevm.currentTarget).get (coinSlot k)) (rliAmt sevm k.val) U 0xaa0 0xb40)
        (_hskip : ∀ k : Fin 3, rliAmt sevm k.val = 0 → ∀ b, V k b → V (k + 1) b)
        (_hG : costImbalance s (rliEnvW sevm T.toNat) (argV3 sevm 0) + 5 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rliEnvW sevm T.toNat)
            o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧
          C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256
            (Nat.toB256 (rliBurnAmt o))) (V 3) post := by
  have ready := c3Ready_of_history trace poolInstalled c3Installed joint fresh env notSystem state
  obtain ⟨s, hs, hlive⟩ := pool_history_removeLiquidityImbalance_live trace poolInstalled
    joint.poolCk env target state
  refine ⟨s, hs, ready, ?_⟩
  intro o T V U G hcode hfork hstatic hdepth hlen hcd hsel hstep htok hcoin hpc hid hkeep hU hT
    hburn hVc hVb hVs hpush hskip hG hGm
  have ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  have hne : sevm.currentTarget ≠ c3 := by rw [target]; exact joint.apart
  let σ := Devm.getStor pre c3
  let σb := burnStor σ sevm.caller.toB256 (Nat.toB256 (rliBurnAmt o))
  let W : Nat → Devm → Prop := fun j => match j with
    | 0 => C3With c3 σ (V 0)
    | j + 1 => C3With c3 σb (V j)
  refine hlive (W := W) hcode hfork hstatic hdepth hlen hcd hsel hstep (by rw [ht]; exact htok)
    hcoin hpc hid hkeep ?_ ⟨⟨ready.1, rfl⟩, hVb⟩ ?_ ?_ hpush
    (fun k hz b hb => ⟨hb.1, hskip k hz b hb.2⟩) hG hGm
  · intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
    all_goals exact c3With_wClosed hne (hVc _ (by decide))
  · exact c3crv_supplyOkAt hfork hdepth (by rw [ht]; exact precomp_false htok) hU (by decide)
      (by decide) (fun b hb => by rw [ht, hb.1.2]; exact ⟨hb.1.1, hT⟩)
      (fun b d hb hs hc => c3With_keep (hVs 0) hb hs hc)
  · refine c3crv_burnOkAt hfork hstatic hdepth (by rw [ht]; exact precomp_false htok) hU
      (by decide) (by decide) ?_ ?_
    · intro b hb
      rw [ht, target, hb.1.2]
      exact ⟨hb.1.1, fun h => joint.apart h.symm, hburn⟩
    · rw [ht]
      exact fun b d hb ho hs hc => ⟨c3At_burn hb.1 hs hc, hVs 0 b d hb.2 ho hc⟩

/-- **Composed U6, entry form: `remove_liquidity_one_coin`.** 3Crv's state is stated once on `pre`
(supply `T`, `BurnFits` for `_token_amount`); the coin push moves the coin chain from `V 0` to
`V 1` over the burned 3Crv storage; the frame ends in `V 1`. -/
theorem pool_3crv_removeLiquidityOneCoin_live_entry
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (poolInstalled : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (c3Installed : some (checkpoint.state.getCode c3).toList = Curve3Crv.c3crvSem.image)
    (joint : JointCheckpoint pool c3 ps₀ cs₀ K₀ checkpoint.state)
    (fresh : Curve3Crv.FreshKeys K₀ (Curve3Crv.historyTouchedKeys c3 trace))
    (env : PoolTraceEnv trace pool ps₀.coins ps₀.token)
    (notSystem : pool ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} (target : sevm.currentTarget = pool)
    (state : pre.state = future.state) :
    ∃ s, PoolHistoryAt trace pool ps₀ s ∧ C3Ready pool c3 pre ∧
      ∀ {o : Out} {i : Fin 3} {T : B256} {V : Nat → Devm → Prop} {U G : Nat}
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
        (_hU : 70000 ≤ U)
        (_hT : (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T)
        (_hburn : BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (ocAmt sevm))
        (_hVc : ∀ k, k ≤ 1 → WClosed sevm (V k)) (_hVb : V 0 pre) (_hVs : C3Blind c3 (V 0))
        (_hpush : CoinPushOkAt sevm
          (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 0))
          (C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 1))
          ((pre.getStor sevm.currentTarget).get (coinSlot i)) (Nat.toB256 (ocPushAmt o)) U
          0x540 0x5e0)
        (_hG : costOneCoin s (ocEnv sevm i T.toNat) (ocAmt sevm).toNat i + 3 * U ≤ G)
        (_hGm : (St pre [] Mem.empty G).gasMeasure + 2000 < 2 ^ 256),
        ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ T' : Nat,
          RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (ocEnv sevm i T') o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧
          C3With c3 (burnStor (Devm.getStor pre c3) sevm.caller.toB256 (ocAmt sevm)) (V 1)
            post := by
  have ready := c3Ready_of_history trace poolInstalled c3Installed joint fresh env notSystem state
  obtain ⟨s, hs, hlive⟩ := pool_history_removeLiquidityOneCoin_live trace poolInstalled
    joint.poolCk env target state
  refine ⟨s, hs, ready, ?_⟩
  intro o i T V U G hcode hfork hstatic hdepth hlen hcd hsel hi hstep htok hcoin hpc hid hkeep hU hT
    hburn hVc hVb hVs hpush hG hGm
  have ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3 := by
    rw [target]; exact ready.2.2
  have hne : sevm.currentTarget ≠ c3 := by rw [target]; exact joint.apart
  refine hlive (W := C3With c3 (Devm.getStor pre c3) (V 0)) hcode hfork hstatic hdepth hlen hcd
    hsel hi hstep (by rw [ht]; exact htok) hcoin hpc hid hkeep
    (c3With_wClosed hne (hVc 0 (by decide))) (c3With_wClosed hne (hVc 0 (by decide)))
    ⟨⟨ready.1, rfl⟩, hVb⟩ ?_ ?_ (c3With_wClosed hne (hVc 1 (by decide))) hpush hG hGm
  · exact c3crv_supplyOkAt hfork hdepth (by rw [ht]; exact precomp_false htok) hU (by decide)
      (by decide) (fun b hb => by rw [ht, hb.1.2]; exact ⟨hb.1.1, hT⟩)
      (fun b d hb hs hc => c3With_keep hVs hb hs hc)
  · refine c3crv_burnOkAt hfork hstatic hdepth (by rw [ht]; exact precomp_false htok) hU
      (by decide) (by decide) ?_ ?_
    · intro b hb
      rw [ht, target, hb.1.2]
      exact ⟨hb.1.1, fun h => joint.apart h.symm, hburn⟩
    · rw [ht]
      exact fun b d hb ho hs hc => ⟨c3At_burn hb.1 hs hc, hVs b d hb.2 ho hc⟩

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
