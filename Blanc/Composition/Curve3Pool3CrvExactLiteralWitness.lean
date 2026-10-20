import Blanc.Composition.Curve3Pool3CrvLiveWitness
import Blanc.Composition.Curve3Pool3CrvCoinExact
import Blanc.Composition.Curve3Pool3CrvExactAssembly

/-!
# The composed exact headlines' coin and 3Crv hypotheses, witnessed as stated

`Curve3Pool3CrvExactWitness.lean` shows each exact premise bundle holds along the bounded witness
worlds (`rlWorld`, `alWorld`, …) with a hand-built call data `P`. The composed exact headlines
(`Curve3Pool3CrvHeadlinesExact.lean`) instead take a caller's coin chain `V`, state the coin
profiles over `C3With c3 σ (V k)`, and consume the bundle through `*ExactPremises_c3crv` at
`rlC3W c3 σ σb V`/`alC3W`/`rliC3W` with `P := rlC3Calls …`/`alC3Calls …`/…. Here, for each of the
four entries, under the same world conditions the bounded witnesses use (`Token20` coins whose
ledgers cover the calls, `T20Coins`; 3Crv with its code and supply `T`, `C3Entry`; 3Crv accepting
the burn or mint), a concrete coin chain `V` that never mentions 3Crv's storage, `U = 80000` and
the coin debit/next functions satisfy, jointly and in the headline's own text, every hypothesis of
the headline's inner binder about the callees and the coin chain:
`_htok`, `_hcoin`, `_hU`, `_hT`, `_hburn`/`_hmint`, `_hVc`, `_hVb`, `_hVs`, `_hskip` (where present)
and the coin profiles `_hpush`/`_hpull`/`_hbalB`/`_hbalA`.

* `coinsFrom`: coins `k, …, 2` as at the entry (the chain of `remove_liquidity` and
  `remove_liquidity_imbalance`);
* `alCoins`: `coinsFrom` plus, at `k = 3`, the fee coin's ledger as its pull leaves it, so
  `C3With σm (alCoins 3)` (the world after the mint) carries the fee-ledger clause by construction;
* `ocCoins`: coin `i` as at the entry, then anything;
* `<entry>_exact_literal_witness`: the headline's hypotheses as a conjunction;
* `<entry>_exact_literal_premises`: that witness fed through `*ExactPremises_c3crv`, giving the
  exact bundle at the headline's own world chain and call data, with the chain's closedness and
  entry world;
* `<entry>_entry_literal_witness`: the same chains meeting the sufficient-gas composed rows'
  (`pool_3crv_*_live_entry`) coin and 3Crv hypotheses, the exact `Token20` profiles forgotten to
  bounded success.

The model step, the amounts' agreement with the model's outputs, `IdReady` and the gas headroom
are not discharged here.
-/

namespace Blanc.Composition.Curve3Pool3CrvLiteralWitness

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCalleeExactProfiles
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3At C3With C3Blind)
open Blanc.Composition.Curve3Pool3CrvExactAssembly
open Blanc.Composition.Curve3Pool3CrvInstance

/-! ## Coin chains -/

section Chains

variable (sevm : Sevm) (pre : Devm)

/-- **Coins `k, …, 2` as at the entry** (`Token20`'s code and their entry ledgers). -/
def coinsFrom (k : Nat) (b : Devm) : Prop :=
  ∀ j : Fin 3, k ≤ j.val → CoinPinned sevm pre j b

/-- **`add_liquidity`'s coin chain**: coins `k, …, 2` as at the entry and, after the fee coin's
pull (`k = 3`, nonzero amount), the fee coin's ledger as the pull leaves it. -/
def alCoins (k : Nat) (b : Devm) : Prop :=
  coinsFrom sevm pre k b ∧
    (k = 3 → alAmt sevm 2 ≠ 0 →
      b.getCode (coinOf sevm pre 2) = VyperNonreentrantDeployed.Token20.code ∧
        b.getStor (coinOf sevm pre 2) = alFeeStor sevm pre)

/-- **`remove_liquidity_one_coin`'s coin chain**: coin `i` as at the entry, then anything. -/
def ocCoins (i : Fin 3) : Nat → Devm → Prop
  | 0 => CoinPinned sevm pre i
  | _ + 1 => fun _ => True

end Chains

section ChainFacts

variable {sevm : Sevm} {pre : Devm} {c3 : Adr}

theorem coinsFrom_wClosed (hcoins : T20Coins sevm pre) (k : Nat) :
    WClosed sevm (coinsFrom sevm pre k) :=
  WClosed.of_foreign fun _ _ hb hs hc j hj =>
    coinPinned_keep (hb j hj) (hs _ (hcoins.pool j)) hc

theorem coinsFrom_blind (htc : ∀ j : Fin 3, coinOf sevm pre j ≠ c3) (k : Nat) :
    C3Blind c3 (coinsFrom sevm pre k) :=
  fun _ _ hb hs hc j hj => coinPinned_keep (hb j hj) (hs _ (htc j)) hc

theorem coinsFrom_entry (hcoins : T20Coins sevm pre) (k : Nat) : coinsFrom sevm pre k pre :=
  fun j _ => ⟨hcoins.code j, rfl⟩

theorem alCoins_wClosed (hcoins : T20Coins sevm pre) (k : Nat) :
    WClosed sevm (alCoins sevm pre k) :=
  WClosed.of_foreign fun _ _ hb hs hc =>
    ⟨fun j hj => coinPinned_keep (hb.1 j hj) (hs _ (hcoins.pool j)) hc,
      fun h3 ha => ⟨(hc _).trans (hb.2 h3 ha).1, (hs _ (hcoins.pool 2)).trans (hb.2 h3 ha).2⟩⟩

theorem alCoins_blind (htc : ∀ j : Fin 3, coinOf sevm pre j ≠ c3) (k : Nat) :
    C3Blind c3 (alCoins sevm pre k) :=
  fun _ _ hb hs hc =>
    ⟨fun j hj => coinPinned_keep (hb.1 j hj) (hs _ (htc j)) hc,
      fun h3 ha => ⟨(hc _).trans (hb.2 h3 ha).1, (hs _ (htc 2)).trans (hb.2 h3 ha).2⟩⟩

theorem alCoins_entry (hcoins : T20Coins sevm pre) : alCoins sevm pre 0 pre :=
  ⟨coinsFrom_entry hcoins 0, fun h => absurd h (by decide)⟩

theorem ocCoins_wClosed {i : Fin 3} (hpool : coinOf sevm pre i ≠ sevm.currentTarget) :
    ∀ k, WClosed sevm (ocCoins sevm pre i k)
  | 0 => WClosed.of_foreign fun _ _ hb hs hc => coinPinned_keep hb (hs _ hpool) hc
  | _ + 1 => WClosed.of_foreign fun _ _ _ _ _ => trivial

theorem ocCoins_blind {i : Fin 3} (htc : coinOf sevm pre i ≠ c3) :
    C3Blind c3 (ocCoins sevm pre i 0) :=
  fun _ _ hb hs hc => coinPinned_keep hb (hs _ htc) hc

end ChainFacts

/-! ## The coin calls along the chains, from `Token20`'s code -/

section CoinCalls

variable {sevm : Sevm} {pre : Devm} {c3 : Adr} {σ : Stor}

/-- **Coin `k`'s push moves `C3With c3 σ (coinsFrom k)` to `C3With c3 σ (coinsFrom (k + 1))`.** -/
theorem coinsFrom_pushExact (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hcoins : T20Coins sevm pre)
    {k : Fin 3} {amt ii oi : B256} (htc : coinOf sevm pre k ≠ c3)
    (hii : ii.toNat + 0x44 ≤ 3104) (hoi : oi.toNat + 32 ≤ 3104)
    (hfits : T20MoveFits (pre.getStor (coinOf sevm pre k)) sevm.currentTarget sevm.caller amt) :
    CoinPushExactAt sevm (C3With c3 σ (coinsFrom sevm pre k.val))
      (C3With c3 σ (coinsFrom sevm pre (k.val + 1)))
      ((pre.getStor sevm.currentTarget).get (coinSlot k)) amt 80000 ii oi :=
  token20_coinPushExactAt hfork hstatic hdepth (hcoins.prec k) rfl (hcoins.pool k) (le_refl _) hii
    hoi (fun b hb => ⟨(hb.2 k (le_refl _)).1, by rw [(hb.2 k (le_refl _)).2]; exact hfits⟩)
    (fun b d hb hl => ⟨c3At_keep' hb.1 (hl.other _ (Ne.symm htc)) hl.code, fun j hj =>
      coinPinned_keep (hb.2 j (by omega))
        (hl.other _ (hcoins.apart j k (fin3_ne_of_lt (by omega)))) hl.code⟩)

end CoinCalls

theorem alCoins_keep {sevm : Sevm} {pre b d : Devm} {c3 : Adr} {σ : Stor} {k : Nat}
    (hb : C3With c3 σ (alCoins sevm pre k) b) (hs : ∀ a, Devm.getStor d a = Devm.getStor b a)
    (hc : ∀ a, d.getCode a = b.getCode a) : C3With c3 σ (alCoins sevm pre k) d :=
  ⟨c3At_keep' hb.1 (hs _) hc, fun j hj => coinPinned_keep (hb.2.1 j hj) (hs _) hc,
    fun h3 ha => ⟨(hc _).trans (hb.2.2 h3 ha).1, (hs _).trans (hb.2.2 h3 ha).2⟩⟩

section CoinCallsAL

variable {sevm : Sevm} {pre : Devm} {c3 : Adr} {σ : Stor}

/-- **Coin `k`'s pull moves `C3With c3 σ (alCoins k)` to `C3With c3 σ (alCoins (k + 1))`**; after
the fee coin's pull the chain records the fee coin's pulled ledger. -/
theorem alCoins_pullExact (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0) (hcoins : T20Coins sevm pre)
    {k : Fin 3} (htc : coinOf sevm pre k ≠ c3)
    (hfits : T20PullFits (pre.getStor (coinOf sevm pre k)) sevm.caller sevm.currentTarget
      sevm.currentTarget (alAmt sevm k.val)) :
    CoinPullExactAt sevm (C3With c3 σ (alCoins sevm pre k.val))
      (C3With c3 σ (alCoins sevm pre (k.val + 1)))
      ((pre.getStor sevm.currentTarget).get (coinSlot k)) (alAmt sevm k.val) 80000 0x760 0x820 := by
  refine token20_coinPullExactAt hfork hstatic hdepth (hcoins.prec k) rfl (hcoins.pool k)
    (le_refl _) (by decide) (by decide)
    (fun b hb => ⟨(hb.2.1 k (le_refl _)).1, by rw [(hb.2.1 k (le_refl _)).2]; exact hfits⟩)
    (fun b d hb hl => ⟨c3At_keep' hb.1 (hl.other _ (Ne.symm htc)) hl.code, fun j hj =>
      coinPinned_keep (hb.2.1 j (by omega))
        (hl.other _ (hcoins.apart j k (fin3_ne_of_lt (by omega)))) hl.code, fun h3 _ => ?_⟩)
  obtain rfl : k = 2 := Fin.ext (by omega)
  exact ⟨(hl.code _).trans (hb.2.1 2 (le_refl _)).1, by rw [hl.stor, (hb.2.1 2 (le_refl _)).2]; rfl⟩

end CoinCallsAL

/-! ## `remove_liquidity` -/

/-- **`pool_3crv_removeLiquidity_live_exact`'s coin and 3Crv hypotheses, witnessed as stated**:
the chain `V := coinsFrom` (coins `k, …, 2` as at the entry), `U = 80000` and `Token20`'s own
transfer debits and successors satisfy `_htok`, `_hcoin`, `_hU`, `_hT`, `_hburn`, `_hVc`, `_hVb`,
`_hVs` and `_hpush` in the headline's text. -/
theorem removeLiquidity_exact_literal_witness {msg : Msg} {pool c3 : Adr} {T : B256}
    (ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3)
    (hfork : CoveredFork (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false)
    (hdepth : (initSevm msg).depth ≠ 0) (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hcoins : T20Coins (initSevm msg) (initDevm msg))
    (hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
      (rlAmt (initSevm msg)))
    (hfits : ∀ k : Fin 3, T20MoveFits
      ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) k)) msg.currentTarget
      msg.caller (balAt ((initDevm msg).getStor msg.currentTarget) k * rlAmt (initSevm msg) / T)) :
    ∃ (V : Nat → Devm → Prop) (U : Nat) (pushD : Nat → Devm → List B256 → Mem → Nat)
      (pushN : Nat → Devm → List B256 → Mem → Devm),
      ¬ (initSevm msg).benvStat.rules.isPrecomp c3 ∧
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
          RawCallOk U 0x520 0x44 0x5c0 (pushD i) (pushN i)) := by
  subst ht
  have htc : ∀ j : Fin 3, coinOf (initSevm msg) (initDevm msg) j ≠
      tokOf (initSevm msg) (initDevm msg) := hcoins.tok
  have hp : ∀ k : Fin 3, CoinPushExactAt (initSevm msg)
      (C3With (tokOf (initSevm msg) (initDevm msg))
        (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
        (coinsFrom (initSevm msg) (initDevm msg) k.val))
      (C3With (tokOf (initSevm msg) (initDevm msg))
        (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
        (coinsFrom (initSevm msg) (initDevm msg) (k.val + 1)))
      (((initDevm msg).getStor msg.currentTarget).get (coinSlot k))
      (balAt ((initDevm msg).getStor msg.currentTarget) k * rlAmt (initSevm msg) / T)
      80000 0x520 0x5c0 := fun k =>
    coinsFrom_pushExact hfork hstatic hdepth hcoins (htc k) (by decide) (by decide) (hfits k)
  obtain ⟨d0, n0, p0⟩ := hp 0
  obtain ⟨d1, n1, p1⟩ := hp 1
  obtain ⟨d2, n2, p2⟩ := hp 2
  refine ⟨coinsFrom (initSevm msg) (initDevm msg), 80000,
    fun i => if i = 0 then d0 else if i = 1 then d1 else d2,
    fun i => if i = 0 then n0 else if i = 1 then n1 else n2,
    hc3.prec, hcoins.prec, by decide, hc3.supply, hburn,
    fun k _ => coinsFrom_wClosed hcoins k, coinsFrom_entry hcoins 0, coinsFrom_blind htc,
    fun i hi => ?_⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · exact p0
  · exact p1
  · exact p2

/-- **The headline's premise route at the witness**: `rlExactPremises_c3crv` applied to
`removeLiquidity_exact_literal_witness`'s data gives the exact bundle at the headline's own world
chain `rlC3W c3 σ σb V` and call data `rlC3Calls … pushD pushN`, with the chain's closedness and
entry world as the headline derives them. -/
theorem removeLiquidity_exact_literal_premises {msg : Msg} {pool c3 : Adr} {T : B256}
    (target : msg.currentTarget = pool)
    (ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3)
    (hfork : CoveredFork (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false)
    (hdepth : (initSevm msg).depth ≠ 0) (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hcoins : T20Coins (initSevm msg) (initDevm msg))
    (hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
      (rlAmt (initSevm msg)))
    (hfits : ∀ k : Fin 3, T20MoveFits
      ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) k)) msg.currentTarget
      msg.caller (balAt ((initDevm msg).getStor msg.currentTarget) k * rlAmt (initSevm msg) / T)) :
    ∃ (V : Nat → Devm → Prop) (U : Nat) (pushD : Nat → Devm → List B256 → Mem → Nat)
      (pushN : Nat → Devm → List B256 → Mem → Devm),
      (∀ k, k ≤ 4 → WClosed (initSevm msg) (rlC3W c3 (Devm.getStor (initDevm msg) c3)
        (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256 (rlAmt (initSevm msg))) V
        k)) ∧
      rlC3W c3 (Devm.getStor (initDevm msg) c3)
        (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256 (rlAmt (initSevm msg))) V 0
        (initDevm msg) ∧
      RLExactPremises (initSevm msg) (initDevm msg) T (rlC3W c3 (Devm.getStor (initDevm msg) c3)
        (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256 (rlAmt (initSevm msg))) V) U
        (rlC3Calls (initSevm msg) (initDevm msg) pushD pushN) := by
  obtain ⟨V, U, pushD, pushN, htok, -, hU, hT, hburn', hVc, hVb, hVs, hpush⟩ :=
    removeLiquidity_exact_literal_witness ht hfork hstatic hdepth hc3 hcoins hburn hfits
  have hne : (initSevm msg).currentTarget ≠ c3 := fun h => hc3.pool (ht.trans h.symm)
  subst target
  refine ⟨V, U, pushD, pushN, fun k hk => ?_, ⟨⟨by rw [← ht]; exact hc3.code, rfl⟩, hVb⟩,
    rlExactPremises_c3crv ht hne hfork hstatic hdepth htok hU hT hburn' hVs hpush⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
  all_goals exact Curve3Pool3CrvHeadlines.c3With_wClosed hne (hVc _ (by decide))

/-! ## `add_liquidity` -/

/-- **`pool_3crv_addLiquidity_live_exact`'s coin and 3Crv hypotheses, witnessed as stated**: the
chain `V := alCoins` (coins `k, …, 2` as at the entry, and the fee coin's pulled ledger in `V 3`,
hence in `C3With σm (V 3)` after the mint), the fee coin's two `balanceOf(self)` answers `B1`, `B2`
(its ledger before and after its pull), `U = 80000` and `Token20`'s own debits and successors
satisfy `_htok`, `_hcoin`, `_hU`, `_hT`, `_hmint`, `_hVc`, `_hVb`, `_hVs`, `_hskip`, `_hpull`,
`_hbalB` and `_hbalA` in the headline's text. -/
theorem addLiquidity_exact_literal_witness {msg : Msg} {o : Out} {pool c3 : Adr} {T : B256}
    (ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3)
    (hfork : CoveredFork (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false)
    (hdepth : (initSevm msg).depth ≠ 0) (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hcoins : T20Coins (initSevm msg) (initDevm msg))
    (hmint : MintFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
      (Nat.toB256 (alMintAmt o)))
    (hfits : ∀ k : Fin 3, alAmt (initSevm msg) k.val ≠ 0 → T20PullFits
      ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) k)) msg.caller
      msg.currentTarget msg.currentTarget (alAmt (initSevm msg) k.val)) :
    ∃ (B1 B2 : B256) (V : Nat → Devm → Prop) (U : Nat)
      (pullD : Nat → Devm → List B256 → Mem → Nat) (pullN : Nat → Devm → List B256 → Mem → Devm)
      (balBD balAD : Devm → List B256 → Mem → Nat) (balBN balAN : Devm → List B256 → Mem → Devm),
      ¬ (initSevm msg).benvStat.rules.isPrecomp c3 ∧
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
            (balanceOfData msg.currentTarget) B2 U 0x87c 0x24 0x8e0 balAD balAN) := by
  subst ht
  have htc : ∀ j : Fin 3, coinOf (initSevm msg) (initDevm msg) j ≠
      tokOf (initSevm msg) (initDevm msg) := hcoins.tok
  have hpz : ∀ k : Fin 3, ∃ (d : Devm → List B256 → Mem → Nat)
      (n : Devm → List B256 → Mem → Devm), alAmt (initSevm msg) k.val ≠ 0 →
      MutableCallProfile (initSevm msg)
        (C3With (tokOf (initSevm msg) (initDevm msg))
          (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
          (alCoins (initSevm msg) (initDevm msg) k.val))
        (C3With (tokOf (initSevm msg) (initDevm msg))
          (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
          (alCoins (initSevm msg) (initDevm msg) (k.val + 1)))
        (((initDevm msg).getStor msg.currentTarget).get (coinSlot k))
        (transferFromSel ++ msg.caller.toB256.toBytes ++ msg.currentTarget.toB256.toBytes ++
          (alAmt (initSevm msg) k.val).toBytes) RawCallOk 80000 0x760 0x64 0x820 d n := by
    intro k
    by_cases ha : alAmt (initSevm msg) k.val = 0
    · exact ⟨fun _ _ _ => 0, fun b _ _ => b, fun h => absurd ha h⟩
    · obtain ⟨d, n, p⟩ := alCoins_pullExact hfork hstatic hdepth hcoins (htc k) (hfits k ha)
      exact ⟨d, n, fun _ => p⟩
  obtain ⟨dB, nB, pB⟩ : CoinBalExactAt (initSevm msg)
      (C3With (tokOf (initSevm msg) (initDevm msg))
        (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
        (alCoins (initSevm msg) (initDevm msg) 2))
      (C3With (tokOf (initSevm msg) (initDevm msg))
        (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
        (alCoins (initSevm msg) (initDevm msg) 2))
      (((initDevm msg).getStor msg.currentTarget).get (coinSlot 2))
      (((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 2)).get
        (VyperNonreentrantDeployed.Token20.balSlot msg.currentTarget)) 80000 0x53c 0x5a0 :=
    token20_coinBalExactAt hfork hdepth (hcoins.prec 2) rfl (by decide) (by decide) (by decide)
      (fun b hb => ⟨(hb.2.1 2 (le_refl _)).1, by rw [(hb.2.1 2 (le_refl _)).2]; rfl⟩)
      (fun b d hb hs hc => alCoins_keep hb hs hc)
  have hAz : ∃ (d : Devm → List B256 → Mem → Nat) (n : Devm → List B256 → Mem → Devm),
      alAmt (initSevm msg) 2 ≠ 0 →
      StaticWordCallProfile (initSevm msg)
        (C3With (tokOf (initSevm msg) (initDevm msg))
          (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
          (alCoins (initSevm msg) (initDevm msg) 3))
        (C3With (tokOf (initSevm msg) (initDevm msg))
          (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
          (alCoins (initSevm msg) (initDevm msg) 3))
        (((initDevm msg).getStor msg.currentTarget).get (coinSlot 2))
        (balanceOfData msg.currentTarget)
        ((alFeeStor (initSevm msg) (initDevm msg)).get
          (VyperNonreentrantDeployed.Token20.balSlot msg.currentTarget))
        80000 0x87c 0x24 0x8e0 d n := by
    by_cases ha : alAmt (initSevm msg) 2 = 0
    · exact ⟨fun _ _ _ => 0, fun b _ _ => b, fun h => absurd ha h⟩
    · obtain ⟨d, n, p⟩ := token20_coinBalExactAt (W := C3With (tokOf (initSevm msg) (initDevm msg))
          (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
          (alCoins (initSevm msg) (initDevm msg) 3)) (ii := 0x87c) (oi := 0x8e0)
        (B := (alFeeStor (initSevm msg) (initDevm msg)).get
          (VyperNonreentrantDeployed.Token20.balSlot msg.currentTarget)) (U := 80000)
        hfork hdepth (hcoins.prec 2) rfl (by decide) (by decide) (by decide)
        (fun b hb => ⟨(hb.2.2 rfl ha).1, by rw [(hb.2.2 rfl ha).2]; rfl⟩)
        (fun b d hb hs hc => alCoins_keep hb hs hc)
      exact ⟨d, n, fun _ => p⟩
  obtain ⟨d0, n0, p0⟩ := hpz 0
  obtain ⟨d1, n1, p1⟩ := hpz 1
  obtain ⟨d2, n2, p2⟩ := hpz 2
  obtain ⟨dA, nA, pA⟩ := hAz
  refine ⟨_, _, alCoins (initSevm msg) (initDevm msg), 80000,
    fun i => if i = 0 then d0 else if i = 1 then d1 else d2,
    fun i => if i = 0 then n0 else if i = 1 then n1 else n2, dB, dA, nB, nA,
    hc3.prec, hcoins.prec, by decide, hc3.supply, hmint,
    fun k _ => alCoins_wClosed hcoins k, alCoins_entry hcoins, alCoins_blind htc,
    fun k hz b hb => ⟨fun j hj => hb.1 j (by omega), fun h3 ha => ?_⟩,
    fun k hk ha => ?_, fun _ => pB, pA⟩
  · have hk : k = 2 := Fin.ext (by omega)
    subst hk
    exact absurd hz ha
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exact p0 ha
    · exact p1 ha
    · exact p2 ha

/-- **The headline's premise route at the witness**: `alExactPremises_c3crv` applied to
`addLiquidity_exact_literal_witness`'s data gives the exact bundle at the headline's own world
chain `alC3W c3 σ σm V` and call data `alC3Calls …`, with the chain's closedness, entry world and
skips as the headline derives them. The world after the mint is `C3With σm (V 3)`, which carries
the fee coin's pulled ledger. -/
theorem addLiquidity_exact_literal_premises {msg : Msg} {o : Out} {pool c3 : Adr} {T : B256}
    (target : msg.currentTarget = pool)
    (ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3)
    (hfork : CoveredFork (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false)
    (hdepth : (initSevm msg).depth ≠ 0) (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hcoins : T20Coins (initSevm msg) (initDevm msg))
    (hmint : MintFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
      (Nat.toB256 (alMintAmt o)))
    (hfits : ∀ k : Fin 3, alAmt (initSevm msg) k.val ≠ 0 → T20PullFits
      ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) k)) msg.caller
      msg.currentTarget msg.currentTarget (alAmt (initSevm msg) k.val)) :
    ∃ (B1 B2 : B256) (V : Nat → Devm → Prop) (U : Nat)
      (pullD : Nat → Devm → List B256 → Mem → Nat) (pullN : Nat → Devm → List B256 → Mem → Devm)
      (balBD balAD : Devm → List B256 → Mem → Nat) (balBN balAN : Devm → List B256 → Mem → Devm),
      (∀ k, k ≤ 4 → WClosed (initSevm msg) (alC3W c3 (Devm.getStor (initDevm msg) c3)
        (mintStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256 (Nat.toB256 (alMintAmt o)))
        V k)) ∧
      alC3W c3 (Devm.getStor (initDevm msg) c3)
        (mintStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256 (Nat.toB256 (alMintAmt o)))
        V 0 (initDevm msg) ∧
      (∀ k : Fin 3, alAmt (initSevm msg) k.val = 0 → ∀ b,
        alC3W c3 (Devm.getStor (initDevm msg) c3)
          (mintStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
            (Nat.toB256 (alMintAmt o))) V k b →
        alC3W c3 (Devm.getStor (initDevm msg) c3)
          (mintStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
            (Nat.toB256 (alMintAmt o))) V (k + 1) b) ∧
      ALExactPremises (initSevm msg) ((initDevm msg).getStor msg.currentTarget) T B1 B2
        (Nat.toB256 (alMintAmt o))
        (alC3W c3 (Devm.getStor (initDevm msg) c3)
          (mintStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
            (Nat.toB256 (alMintAmt o))) V) U
        (alC3Calls (initSevm msg) (initDevm msg) pullD pullN balBD balAD balBN balAN) := by
  obtain ⟨B1, B2, V, U, pullD, pullN, balBD, balAD, balBN, balAN, htok, -, hU, hT, hmint', hVc,
    hVb, hVs, hskip, hpull, hbalB, hbalA⟩ :=
    addLiquidity_exact_literal_witness ht hfork hstatic hdepth hc3 hcoins hmint hfits
  have hne : (initSevm msg).currentTarget ≠ c3 := fun h => hc3.pool (ht.trans h.symm)
  subst target
  refine ⟨B1, B2, V, U, pullD, pullN, balBD, balAD, balBN, balAN, fun k hk => ?_,
    ⟨⟨by rw [← ht]; exact hc3.code, rfl⟩, hVb⟩,
    fun k hz b hb => match k, hz, hb with
      | ⟨0, _⟩, hz, hb => ⟨hb.1, hskip 0 hz b hb.2⟩
      | ⟨1, _⟩, hz, hb => ⟨hb.1, hskip 1 hz b hb.2⟩
      | ⟨2, _⟩, hz, hb => ⟨hb.1, hskip 2 hz b hb.2⟩,
    alExactPremises_c3crv ht hne hfork hstatic hdepth htok hU hT hmint' hVs hpull hbalB hbalA⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
  all_goals exact Curve3Pool3CrvHeadlines.c3With_wClosed hne (hVc _ (by decide))

/-! ## `remove_liquidity_imbalance` -/

/-- **`pool_3crv_removeLiquidityImbalance_live_exact`'s coin and 3Crv hypotheses, witnessed as
stated**: the chain `V := coinsFrom`, `U = 80000` and `Token20`'s own transfer debits and
successors satisfy `_htok`, `_hcoin`, `_hU`, `_hT`, `_hburn`, `_hVc`, `_hVb`, `_hVs`, `_hskip` and
`_hpush` in the headline's text. -/
theorem removeLiquidityImbalance_exact_literal_witness {msg : Msg} {o : Out} {pool c3 : Adr}
    {T : B256} (ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3)
    (hfork : CoveredFork (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false)
    (hdepth : (initSevm msg).depth ≠ 0) (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hcoins : T20Coins (initSevm msg) (initDevm msg))
    (hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
      (Nat.toB256 (rliBurnAmt o)))
    (hfits : ∀ k : Fin 3, rliAmt (initSevm msg) k.val ≠ 0 → T20MoveFits
      ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) k)) msg.currentTarget
      msg.caller (rliAmt (initSevm msg) k.val)) :
    ∃ (V : Nat → Devm → Prop) (U : Nat) (pushD : Nat → Devm → List B256 → Mem → Nat)
      (pushN : Nat → Devm → List B256 → Mem → Devm),
      ¬ (initSevm msg).benvStat.rules.isPrecomp c3 ∧
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
            RawCallOk U 0xaa0 0x44 0xb40 (pushD k) (pushN k)) := by
  subst ht
  have htc : ∀ j : Fin 3, coinOf (initSevm msg) (initDevm msg) j ≠
      tokOf (initSevm msg) (initDevm msg) := hcoins.tok
  have hpz : ∀ k : Fin 3, ∃ (d : Devm → List B256 → Mem → Nat)
      (n : Devm → List B256 → Mem → Devm), rliAmt (initSevm msg) k.val ≠ 0 →
      MutableCallProfile (initSevm msg)
        (C3With (tokOf (initSevm msg) (initDevm msg))
          (burnStor (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
            msg.caller.toB256 (Nat.toB256 (rliBurnAmt o)))
          (coinsFrom (initSevm msg) (initDevm msg) k.val))
        (C3With (tokOf (initSevm msg) (initDevm msg))
          (burnStor (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
            msg.caller.toB256 (Nat.toB256 (rliBurnAmt o)))
          (coinsFrom (initSevm msg) (initDevm msg) (k.val + 1)))
        (((initDevm msg).getStor msg.currentTarget).get (coinSlot k))
        (transferSel ++ msg.caller.toB256.toBytes ++ (rliAmt (initSevm msg) k.val).toBytes)
        RawCallOk 80000 0xaa0 0x44 0xb40 d n := by
    intro k
    by_cases ha : rliAmt (initSevm msg) k.val = 0
    · exact ⟨fun _ _ _ => 0, fun b _ _ => b, fun h => absurd ha h⟩
    · obtain ⟨d, n, p⟩ := coinsFrom_pushExact (σ := burnStor
          (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
          msg.caller.toB256 (Nat.toB256 (rliBurnAmt o))) (ii := 0xaa0) (oi := 0xb40)
        hfork hstatic hdepth hcoins (htc k) (by decide) (by decide) (hfits k ha)
      exact ⟨d, n, fun _ => p⟩
  obtain ⟨d0, n0, p0⟩ := hpz 0
  obtain ⟨d1, n1, p1⟩ := hpz 1
  obtain ⟨d2, n2, p2⟩ := hpz 2
  refine ⟨coinsFrom (initSevm msg) (initDevm msg), 80000,
    fun i => if i = 0 then d0 else if i = 1 then d1 else d2,
    fun i => if i = 0 then n0 else if i = 1 then n1 else n2,
    hc3.prec, hcoins.prec, by decide, hc3.supply, hburn,
    fun k _ => coinsFrom_wClosed hcoins k, coinsFrom_entry hcoins 0, coinsFrom_blind htc,
    fun k _ b hb j hj => hb j (by omega), fun k hk ha => ?_⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · exact p0 ha
  · exact p1 ha
  · exact p2 ha

/-- **The headline's premise route at the witness**: `rliExactPremises_c3crv` applied to
`removeLiquidityImbalance_exact_literal_witness`'s data gives the exact bundle at the headline's
own world chain `rliC3W c3 σ σb V` and call data `rliC3Calls … pushD pushN`, with the chain's
closedness, entry world and skips as the headline derives them. -/
theorem removeLiquidityImbalance_exact_literal_premises {msg : Msg} {o : Out} {pool c3 : Adr}
    {T : B256} (target : msg.currentTarget = pool)
    (ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3)
    (hfork : CoveredFork (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false)
    (hdepth : (initSevm msg).depth ≠ 0) (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hcoins : T20Coins (initSevm msg) (initDevm msg))
    (hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
      (Nat.toB256 (rliBurnAmt o)))
    (hfits : ∀ k : Fin 3, rliAmt (initSevm msg) k.val ≠ 0 → T20MoveFits
      ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) k)) msg.currentTarget
      msg.caller (rliAmt (initSevm msg) k.val)) :
    ∃ (V : Nat → Devm → Prop) (U : Nat) (pushD : Nat → Devm → List B256 → Mem → Nat)
      (pushN : Nat → Devm → List B256 → Mem → Devm),
      (∀ j, j ≤ 4 → WClosed (initSevm msg) (rliC3W c3 (Devm.getStor (initDevm msg) c3)
        (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256 (Nat.toB256 (rliBurnAmt o)))
        V j)) ∧
      rliC3W c3 (Devm.getStor (initDevm msg) c3)
        (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256 (Nat.toB256 (rliBurnAmt o)))
        V 0 (initDevm msg) ∧
      (∀ k : Fin 3, rliAmt (initSevm msg) k.val = 0 → ∀ b,
        rliC3W c3 (Devm.getStor (initDevm msg) c3)
          (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
            (Nat.toB256 (rliBurnAmt o))) V (k + 1) b →
        rliC3W c3 (Devm.getStor (initDevm msg) c3)
          (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
            (Nat.toB256 (rliBurnAmt o))) V (k + 2) b) ∧
      RLIExactPremises (initSevm msg) ((initDevm msg).getStor msg.currentTarget) T
        (Nat.toB256 (rliBurnAmt o))
        (rliC3W c3 (Devm.getStor (initDevm msg) c3)
          (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
            (Nat.toB256 (rliBurnAmt o))) V) U
        (rliC3Calls (initSevm msg) (initDevm msg) pushD pushN) := by
  obtain ⟨V, U, pushD, pushN, htok, -, hU, hT, hburn', hVc, hVb, hVs, hskip, hpush⟩ :=
    removeLiquidityImbalance_exact_literal_witness ht hfork hstatic hdepth hc3 hcoins hburn hfits
  have hne : (initSevm msg).currentTarget ≠ c3 := fun h => hc3.pool (ht.trans h.symm)
  subst target
  refine ⟨V, U, pushD, pushN, fun k hk => ?_, ⟨⟨by rw [← ht]; exact hc3.code, rfl⟩, hVb⟩,
    fun k hz b hb => ⟨hb.1, hskip k hz b hb.2⟩,
    rliExactPremises_c3crv ht hne hfork hstatic hdepth htok hU hT hburn' hVs hpush⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
  all_goals exact Curve3Pool3CrvHeadlines.c3With_wClosed hne (hVc _ (by decide))

/-! ## `remove_liquidity_one_coin` -/

/-- **`pool_3crv_removeLiquidityOneCoin_live_exact`'s coin and 3Crv hypotheses, witnessed as
stated**: the chain `V := ocCoins i` (coin `i` as at the entry, then anything), `U = 80000` and
`Token20`'s own transfer debit and successor satisfy `_htok`, `_hcoin`, `_hU`, `_hT`, `_hburn`,
`_hVc`, `_hVb`, `_hVs` and `_hpush` in the headline's text. Only coin `i` is called, so only coin
`i` is required to run `Token20`; `_hcoin` is a fact about all three coin words. -/
theorem removeLiquidityOneCoin_exact_literal_witness {msg : Msg} {o : Out} {i : Fin 3}
    {pool c3 : Adr} {T : B256}
    (ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3)
    (hfork : CoveredFork (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false)
    (hdepth : (initSevm msg).depth ≠ 0) (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hi : i.val = (ocI (initSevm msg)).toNat)
    (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
      (coinOf (initSevm msg) (initDevm msg) k))
    (hcode : (initDevm msg).getCode (coinOf (initSevm msg) (initDevm msg) i) =
      VyperNonreentrantDeployed.Token20.code)
    (hpool : coinOf (initSevm msg) (initDevm msg) i ≠ msg.currentTarget)
    (htc : coinOf (initSevm msg) (initDevm msg) i ≠ c3)
    (hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
      (ocAmt (initSevm msg)))
    (hfits : T20MoveFits ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) i))
      msg.currentTarget msg.caller (Nat.toB256 (ocPushAmt o))) :
    ∃ (V : Nat → Devm → Prop) (U : Nat) (pushD : Devm → List B256 → Mem → Nat)
      (pushN : Devm → List B256 → Mem → Devm),
      ¬ (initSevm msg).benvStat.rules.isPrecomp c3 ∧
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
          RawCallOk U 0x540 0x44 0x5e0 pushD pushN := by
  subst ht
  have hci : coinSlot i = coinsBase + ocI (initSevm msg) := by
    simp only [coinSlot, hi, toB256_toNat]
  obtain ⟨dP, nP, pP⟩ : CoinPushExactAt (initSevm msg)
      (C3With (tokOf (initSevm msg) (initDevm msg))
        (burnStor (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
          msg.caller.toB256 (ocAmt (initSevm msg))) (ocCoins (initSevm msg) (initDevm msg) i 0))
      (C3With (tokOf (initSevm msg) (initDevm msg))
        (burnStor (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
          msg.caller.toB256 (ocAmt (initSevm msg))) (ocCoins (initSevm msg) (initDevm msg) i 1))
      (((initDevm msg).getStor msg.currentTarget).get (coinSlot i)) (Nat.toB256 (ocPushAmt o))
      80000 0x540 0x5e0 :=
    token20_coinPushExactAt hfork hstatic hdepth (hcoin i) rfl hpool (le_refl _) (by decide)
      (by decide) (fun b hb => ⟨hb.2.1, by rw [hb.2.2]; exact hfits⟩)
      (fun b d hb hl => ⟨c3At_keep' hb.1 (hl.other _ (Ne.symm htc)) hl.code, trivial⟩)
  rw [hci] at pP
  exact ⟨ocCoins (initSevm msg) (initDevm msg) i, 80000, dP, nP, hc3.prec, hcoin, by decide,
    hc3.supply, hburn, fun k _ => ocCoins_wClosed hpool k, ⟨hcode, rfl⟩,
    ocCoins_blind htc, pP⟩

/-- **The headline's premise route at the witness**: `ocExactPremises_c3crv` applied to
`removeLiquidityOneCoin_exact_literal_witness`'s data gives the exact bundle along the headline's
own chain `C3With c3 σ (V 0) → C3With c3 σb (V 0) → C3With c3 σb (V 1)` and call data
`ocC3Calls … pushD pushN`, with the chain's closedness and entry world. -/
theorem removeLiquidityOneCoin_exact_literal_premises {msg : Msg} {o : Out} {i : Fin 3}
    {pool c3 : Adr} {T : B256} (target : msg.currentTarget = pool)
    (ht : (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr = c3)
    (hfork : CoveredFork (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false)
    (hdepth : (initSevm msg).depth ≠ 0) (hc3 : C3Entry (initSevm msg) (initDevm msg) T)
    (hi : i.val = (ocI (initSevm msg)).toNat)
    (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
      (coinOf (initSevm msg) (initDevm msg) k))
    (hcode : (initDevm msg).getCode (coinOf (initSevm msg) (initDevm msg) i) =
      VyperNonreentrantDeployed.Token20.code)
    (hpool : coinOf (initSevm msg) (initDevm msg) i ≠ msg.currentTarget)
    (htc : coinOf (initSevm msg) (initDevm msg) i ≠ c3)
    (hburn : BurnFits (Devm.getStor (initDevm msg) c3) pool msg.caller.toB256
      (ocAmt (initSevm msg)))
    (hfits : T20MoveFits ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) i))
      msg.currentTarget msg.caller (Nat.toB256 (ocPushAmt o))) :
    ∃ (V : Nat → Devm → Prop) (U : Nat) (pushD : Devm → List B256 → Mem → Nat)
      (pushN : Devm → List B256 → Mem → Devm),
      WClosed (initSevm msg) (C3With c3 (Devm.getStor (initDevm msg) c3) (V 0)) ∧
      WClosed (initSevm msg) (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3)
        msg.caller.toB256 (ocAmt (initSevm msg))) (V 0)) ∧
      C3With c3 (Devm.getStor (initDevm msg) c3) (V 0) (initDevm msg) ∧
      WClosed (initSevm msg) (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3)
        msg.caller.toB256 (ocAmt (initSevm msg))) (V 1)) ∧
      OCExactPremises (initSevm msg) (initDevm msg) T (Nat.toB256 (ocPushAmt o))
        (C3With c3 (Devm.getStor (initDevm msg) c3) (V 0))
        (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
          (ocAmt (initSevm msg))) (V 0))
        (C3With c3 (burnStor (Devm.getStor (initDevm msg) c3) msg.caller.toB256
          (ocAmt (initSevm msg))) (V 1)) U
        (ocC3Calls (initSevm msg) (initDevm msg) pushD pushN) := by
  obtain ⟨V, U, pushD, pushN, htok, -, hU, hT, hburn', hVc, hVb, hVs, hpush⟩ :=
    removeLiquidityOneCoin_exact_literal_witness ht hfork hstatic hdepth hc3 hi hcoin hcode hpool
      htc hburn hfits
  have hne : (initSevm msg).currentTarget ≠ c3 := fun h => hc3.pool (ht.trans h.symm)
  subst target
  exact ⟨V, U, pushD, pushN, Curve3Pool3CrvHeadlines.c3With_wClosed hne (hVc 0 (by decide)),
    Curve3Pool3CrvHeadlines.c3With_wClosed hne (hVc 0 (by decide)),
    ⟨⟨by rw [← ht]; exact hc3.code, rfl⟩, hVb⟩,
    Curve3Pool3CrvHeadlines.c3With_wClosed hne (hVc 1 (by decide)),
    ocExactPremises_c3crv ht hne hfork hstatic hdepth htok hU hT hburn' hVs hpush⟩

/-! ## The sufficient-gas composed rows

The bounded composed entries (`Curve3Pool3CrvHeadlines.pool_3crv_*_live_entry`) take the same coin
chain with bounded coin premises (`CoinPushOkAt`, `CoinPullOkAt`, `CoinBalOkAt`); the same chains
and `Token20` profiles, forgotten to bounded success (`MutCallExactAt.bounded`,
`StaticWordExactAt.bounded`), meet them as stated. -/

section Bounded

variable {sevm : Sevm} {pre : Devm} {pool c3 : Adr} {T : B256}

/-- **`pool_3crv_removeLiquidity_live_entry`'s coin and 3Crv hypotheses, witnessed as stated.** -/
theorem removeLiquidity_entry_literal_witness
    (ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcoins : T20Coins sevm pre)
    (hburn : BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (rlAmt sevm))
    (hfits : ∀ k : Fin 3, T20MoveFits (pre.getStor (coinOf sevm pre k)) sevm.currentTarget
      sevm.caller (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T)) :
    ∃ (V : Nat → Devm → Prop) (U : Nat),
      ¬ sevm.benvStat.rules.isPrecomp c3 ∧
      (∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
          ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr) ∧
      70000 ≤ U ∧
      (Devm.getStor pre c3).get Curve3Crv.vySupplySlot = T ∧
      BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (rlAmt sevm) ∧
      (∀ k, k ≤ 3 → WClosed sevm (V k)) ∧ V 0 pre ∧ (∀ k, C3Blind c3 (V k)) ∧
      (∀ k : Fin 3, CoinPushOkAt sevm (C3With c3 (Devm.getStor pre c3) (V k))
          (C3With c3 (Devm.getStor pre c3) (V (k + 1)))
          ((pre.getStor sevm.currentTarget).get (coinSlot k))
          (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T) U 0x520 0x5c0) := by
  subst ht
  exact ⟨coinsFrom sevm pre, 80000, hc3.prec, hcoins.prec, by decide, hc3.supply, hburn,
    fun k _ => coinsFrom_wClosed hcoins k, coinsFrom_entry hcoins 0, coinsFrom_blind hcoins.tok,
    fun k => MutCallExactAt.bounded
      (coinsFrom_pushExact hfork hstatic hdepth hcoins (hcoins.tok k) (by decide) (by decide)
        (hfits k))⟩

/-- **`pool_3crv_addLiquidity_live_entry`'s coin and 3Crv hypotheses, witnessed as stated**,
the fee coin's pulled ledger carried in `V 3`. -/
theorem addLiquidity_entry_literal_witness {o : Out}
    (ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcoins : T20Coins sevm pre)
    (hmint : MintFits (Devm.getStor pre c3) pool sevm.caller.toB256 (Nat.toB256 (alMintAmt o)))
    (hfits : ∀ k : Fin 3, alAmt sevm k.val ≠ 0 → T20PullFits (pre.getStor (coinOf sevm pre k))
      sevm.caller sevm.currentTarget sevm.currentTarget (alAmt sevm k.val)) :
    ∃ (B1 B2 : B256) (V : Nat → Devm → Prop) (U : Nat),
      ¬ sevm.benvStat.rules.isPrecomp c3 ∧
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
            ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B2 U 0x87c 0x8e0) := by
  subst ht
  refine ⟨_, _, alCoins sevm pre, 80000, hc3.prec, hcoins.prec, by decide, hc3.supply, hmint,
    fun k _ => alCoins_wClosed hcoins k, alCoins_entry hcoins, alCoins_blind hcoins.tok,
    fun k _ ha => MutCallExactAt.bounded
      (alCoins_pullExact hfork hstatic hdepth hcoins (hcoins.tok k) (hfits k ha)),
    fun k hz b hb => ⟨fun j hj => hb.1 j (by omega), fun h3 ha => ?_⟩,
    fun ha => ⟨StaticWordExactAt.bounded (token20_coinBalExactAt (U := 80000) hfork hdepth
        (hcoins.prec 2) rfl (by decide) (by decide) (by decide)
        (fun b hb => ⟨(hb.2.1 2 (le_refl _)).1, by rw [(hb.2.1 2 (le_refl _)).2]⟩)
        (fun b d hb hs hc => alCoins_keep hb hs hc)),
      MutCallExactAt.bounded
        (alCoins_pullExact (k := 2) hfork hstatic hdepth hcoins (hcoins.tok 2) (hfits 2 ha)),
      StaticWordExactAt.bounded (token20_coinBalExactAt (U := 80000)
        (B := (alFeeStor sevm pre).get (VyperNonreentrantDeployed.Token20.balSlot
          sevm.currentTarget)) hfork hdepth (hcoins.prec 2) rfl (by decide) (by decide) (by decide)
        (fun b hb => ⟨(hb.2.2 rfl ha).1, by rw [(hb.2.2 rfl ha).2]⟩)
        (fun b d hb hs hc => alCoins_keep hb hs hc))⟩⟩
  have hk : k = 2 := Fin.ext (by omega)
  subst hk
  exact absurd hz ha

/-- **`pool_3crv_removeLiquidityImbalance_live_entry`'s coin and 3Crv hypotheses, witnessed as
stated.** -/
theorem removeLiquidityImbalance_entry_literal_witness {o : Out}
    (ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T) (hcoins : T20Coins sevm pre)
    (hburn : BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (Nat.toB256 (rliBurnAmt o)))
    (hfits : ∀ k : Fin 3, rliAmt sevm k.val ≠ 0 → T20MoveFits (pre.getStor (coinOf sevm pre k))
      sevm.currentTarget sevm.caller (rliAmt sevm k.val)) :
    ∃ (V : Nat → Devm → Prop) (U : Nat),
      ¬ sevm.benvStat.rules.isPrecomp c3 ∧
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
      (∀ k : Fin 3, rliAmt sevm k.val = 0 → ∀ b, V k b → V (k + 1) b) := by
  subst ht
  exact ⟨coinsFrom sevm pre, 80000, hc3.prec, hcoins.prec, by decide, hc3.supply, hburn,
    fun k _ => coinsFrom_wClosed hcoins k, coinsFrom_entry hcoins 0, coinsFrom_blind hcoins.tok,
    fun k ha => MutCallExactAt.bounded
      (coinsFrom_pushExact hfork hstatic hdepth hcoins (hcoins.tok k) (by decide) (by decide)
        (hfits k ha)),
    fun k _ b hb j hj => hb j (by omega)⟩

/-- **`pool_3crv_removeLiquidityOneCoin_live_entry`'s coin and 3Crv hypotheses, witnessed as
stated**, only coin `i` running `Token20`. -/
theorem removeLiquidityOneCoin_entry_literal_witness {o : Out} {i : Fin 3}
    (ht : ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr = c3)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hc3 : C3Entry sevm pre T)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp (coinOf sevm pre k))
    (hcode : pre.getCode (coinOf sevm pre i) = VyperNonreentrantDeployed.Token20.code)
    (hpool : coinOf sevm pre i ≠ sevm.currentTarget) (htc : coinOf sevm pre i ≠ c3)
    (hburn : BurnFits (Devm.getStor pre c3) pool sevm.caller.toB256 (ocAmt sevm))
    (hfits : T20MoveFits (pre.getStor (coinOf sevm pre i)) sevm.currentTarget sevm.caller
      (Nat.toB256 (ocPushAmt o))) :
    ∃ (V : Nat → Devm → Prop) (U : Nat),
      ¬ sevm.benvStat.rules.isPrecomp c3 ∧
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
          0x540 0x5e0 := by
  subst ht
  exact ⟨ocCoins sevm pre i, 80000, hc3.prec, hcoin, by decide, hc3.supply, hburn,
    fun k _ => ocCoins_wClosed hpool k, ⟨hcode, rfl⟩, ocCoins_blind htc,
    MutCallExactAt.bounded (token20_coinPushExactAt hfork hstatic hdepth (hcoin i) rfl hpool
      (le_refl _) (by decide) (by decide) (fun b hb => ⟨hb.2.1, by rw [hb.2.2]; exact hfits⟩)
      (fun b d hb hl => ⟨c3At_keep' hb.1 (hl.other _ (Ne.symm htc)) hl.code, trivial⟩))⟩

end Bounded

end Blanc.Composition.Curve3Pool3CrvLiteralWitness
