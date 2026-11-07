import Blanc.Composition.Curve3PoolAddRequest

/-!
# `add_liquidity`'s exact premises with the real coins

`addV`: the coin chain, each coin's ledger as the pulls so far leave it. `addCalls`: the calls' data, with 3Crv's profiles and each
coin's own debit and successor at `add_liquidity`'s windows. `add_premises`: `ALExactPremises` along that chain, at `U = 129555`.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift
open Blanc.Lift.Curve3Pool (ALExactCalls ALExactPremises WClosed alAmt coinSlot transferFromSel balanceOfData)
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (RealCoins Pin pulledK PullFitsK proxyAt_pinned)
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3At C3With C3Blind c3With_keep)
open Blanc.Composition.Curve3Pool3CrvExactAssembly (alC3Calls alC3W alExactPremises_c3crv tokW)
open Blanc.Composition.Curve3Pool3CrvInstance (coinOf tokOf CoinLeaves c3At_keep')

section Chain

variable (sevm : Sevm) (pre : Devm)

/-- The word naming coin `k` at the entry. -/
noncomputable abbrev coinW (k : Nat) : B256 := Curve3Pool.coinAt (pre.getStor sevm.currentTarget) k

/-- Coin `k`'s pull debit at `add_liquidity`'s window. -/
noncomputable def addPullD : Nat → Devm → List B256 → Mem → Nat
  | 0 => coinDebit Dai.pullG sevm (coinW sevm pre 0) 0x760 0x64 0x820
  | 1 => coinDebit UsdcLive.pullG sevm (coinW sevm pre 1) 0x760 0x64 0x820
  | _ => coinDebit Usdt.pullG sevm (coinW sevm pre 2) 0x760 0x64 0x820

/-- Coin `k`'s pull successor at `add_liquidity`'s window. -/
noncomputable def addPullN : Nat → Devm → List B256 → Mem → Devm
  | 0 => coinNext (fun s p => Dai.pullPost s p 0) sevm (coinW sevm pre 0) 0x760 0x64 0x820
  | 1 => coinNext (UsdcLive.proxyCanon 1 (fun s p => UsdcLive.implPullPost s p 0)) sevm (coinW sevm pre 1) 0x760 0x64 0x820
  | _ => coinNext (fun s p => Usdt.pullP s p 0) sevm (coinW sevm pre 2) 0x760 0x64 0x820

/-- `add_liquidity`'s exact calls with the real coins. -/
noncomputable def addCalls : ALExactCalls :=
  alC3Calls sevm pre (addPullD sevm pre) (addPullN sevm pre)
    (coinStaticDebit Usdt.balG sevm (coinW sevm pre 2) 0x53c 0x24 0x5a0)
    (coinStaticDebit Usdt.balG sevm (coinW sevm pre 2) 0x87c 0x24 0x8e0)
    (coinStaticNext (fun s p => Usdt.balP s p 0) sevm (coinW sevm pre 2) 0x53c 0x24 0x5a0)
    (coinStaticNext (fun s p => Usdt.balP s p 0) sevm (coinW sevm pre 2) 0x87c 0x24 0x8e0)

/-- Coin `j`'s ledger once the pulls before coin `k` are done. -/
noncomputable def addLedger (k : Nat) (j : Fin 3) : Stor :=
  if j.val < k ∧ alAmt sevm j.val ≠ 0 then
    pulledK j (pre.getStor (coinOf sevm pre j)) sevm.caller sevm.currentTarget (alAmt sevm j.val)
  else pre.getStor (coinOf sevm pre j)

/-- **`add_liquidity`'s coin chain**: every code as at the entry, each coin's ledger as the pulls before `k` leave it. -/
def addV (k : Nat) (b : Devm) : Prop :=
  (∀ a, b.getCode a = pre.getCode a) ∧ ∀ j : Fin 3, b.getStor (coinOf sevm pre j) = addLedger sevm pre k j

/-- The pool's USDT word before the pull. -/
noncomputable abbrev addB1 : B256 := (pre.getStor (coinOf sevm pre 2)).get (Usdt.balSlot sevm.currentTarget)

/-- The pool's USDT word after the pull. -/
noncomputable abbrev addB2 : B256 :=
  (pulledK 2 (pre.getStor (coinOf sevm pre 2)) sevm.caller sevm.currentTarget (alAmt sevm 2)).get
    (Usdt.balSlot sevm.currentTarget)

end Chain

variable {sevm : Sevm} {pre : Devm} {c3a : Adr} {σ : Stor}

theorem addLedger_self (k : Fin 3) : addLedger sevm pre k.val k = pre.getStor (coinOf sevm pre k) :=
  if_neg fun h => Nat.lt_irrefl _ h.1

theorem addLedger_next_self {k : Fin 3} (ha : alAmt sevm k.val ≠ 0) :
    addLedger sevm pre (k.val + 1) k =
      pulledK k (pre.getStor (coinOf sevm pre k)) sevm.caller sevm.currentTarget (alAmt sevm k.val) :=
  if_pos ⟨Nat.lt_succ_self _, ha⟩

theorem addLedger_next_other {k j : Fin 3} (hjk : j ≠ k) : addLedger sevm pre (k.val + 1) j = addLedger sevm pre k.val j := by
  have hne : j.val ≠ k.val := fun e => hjk (Fin.ext e)
  have hiff : (j.val < k.val + 1 ∧ alAmt sevm j.val ≠ 0) ↔ (j.val < k.val ∧ alAmt sevm j.val ≠ 0) :=
    ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨by omega, h.2⟩⟩
  simp only [addLedger, hiff]

theorem addLedger_skip {k : Fin 3} (hz : alAmt sevm k.val = 0) (j : Fin 3) :
    addLedger sevm pre (k.val + 1) j = addLedger sevm pre k.val j := by
  by_cases hjk : j = k
  · subst hjk
    have h1 : ¬ (j.val < j.val + 1 ∧ alAmt sevm j.val ≠ 0) := fun h => h.2 hz
    have h2 : ¬ (j.val < j.val ∧ alAmt sevm j.val ≠ 0) := fun h => Nat.lt_irrefl _ h.1
    simp only [addLedger, h1, h2, if_false]
  · exact addLedger_next_other hjk

theorem addV_keep {k : Nat} {b d : Devm} (hb : addV sevm pre k b) (hs : ∀ j : Fin 3, d.getStor (coinOf sevm pre j) = b.getStor (coinOf sevm pre j))
    (hc : ∀ a, d.getCode a = b.getCode a) : addV sevm pre k d :=
  ⟨fun a => (hc a).trans (hb.1 a), fun j => (hs j).trans (hb.2 j)⟩

theorem addV_wClosed (hC : RealCoins sevm pre) (k : Nat) : WClosed sevm (addV sevm pre k) :=
  Curve3Pool.WClosed.of_foreign fun _ _ hb hs hc => addV_keep hb (fun j => hs _ (hC.pool j)) hc

theorem addV_blind {c : Adr} (htc : ∀ j : Fin 3, coinOf sevm pre j ≠ c) (k : Nat) : C3Blind c (addV sevm pre k) :=
  fun _ _ hb hs hc => addV_keep hb (fun j => hs _ (htc j)) hc

theorem addV_entry : addV sevm pre 0 pre := ⟨fun _ => rfl, fun j => (if_neg fun h => Nat.not_lt_zero _ h.1).symm⟩

theorem addV_skip {k : Fin 3} (hz : alAmt sevm k.val = 0) {b : Devm} (h : addV sevm pre k.val b) : addV sevm pre (k.val + 1) b :=
  ⟨h.1, fun j => (h.2 j).trans (addLedger_skip hz j).symm⟩

/-- What a pull's coin leaves is the next world of the chain. -/
theorem addV_leave (hC : RealCoins sevm pre) {k : Fin 3} {b d : Devm} {R : Prop} (ha : alAmt sevm k.val ≠ 0) {c : Adr} (htc : c ≠ coinOf sevm pre k)
    (hb : C3With c σ (addV sevm pre k.val) b)
    (hl : CoinLeaves (coinOf sevm pre k) (pulledK k (b.getStor (coinOf sevm pre k)) sevm.caller sevm.currentTarget (alAmt sevm k.val)) R b d) :
    C3With c σ (addV sevm pre (k.val + 1)) d := by
  refine ⟨c3At_keep' hb.1 (hl.other _ htc) hl.code, fun a => (hl.code a).trans (hb.2.1 a), fun j => ?_⟩
  by_cases hjk : j = k
  · subst hjk
    rw [hl.stor, hb.2.2 j, addLedger_self, addLedger_next_self ha]
  · rw [hl.other _ (hC.apart j k hjk), hb.2.2 j, addLedger_next_other hjk]

/-- The pull's ledger, in the world before it. -/
theorem addV_at {k : Fin 3} {b : Devm} {c : Adr} (hb : C3With c σ (addV sevm pre k.val) b) :
    b.getStor (coinOf sevm pre k) = pre.getStor (coinOf sevm pre k) := by
  rw [hb.2.2 k, addLedger_self]

theorem add_chain_keep {c : Adr} (htc : ∀ j : Fin 3, coinOf sevm pre j ≠ c) {k : Nat} {b d : Devm} (hb : C3With c σ (addV sevm pre k) b)
    (hs : ∀ a, Devm.getStor d a = Devm.getStor b a) (hc : ∀ a, d.getCode a = b.getCode a) : C3With c σ (addV sevm pre k) d :=
  c3With_keep (addV_blind htc k) hb hs hc

/-- **Coin `k`'s pull, exact, by its index.** -/
theorem add_pull (hfork : ShanghaiOnwards sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : 2 ≤ sevm.depth) (hC : RealCoins sevm pre)
    {c : Adr} (htc : ∀ j : Fin 3, coinOf sevm pre j ≠ c) (k : Fin 3) (ha : alAmt sevm k.val ≠ 0)
    (hpf : PullFitsK k (pre.getStor (coinOf sevm pre k)) sevm.caller sevm.currentTarget (alAmt sevm k.val)) :
    MutableCallProfile sevm (C3With c σ (addV sevm pre k.val)) (C3With c σ (addV sevm pre (k.val + 1))) (coinW sevm pre k.val)
      (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++ (alAmt sevm k.val).toBytes)
      RawCallOk 129555 0x760 0x64 0x820 (addPullD sevm pre k.val) (addPullN sevm pre k.val) := by
  have hdep0 : sevm.depth ≠ 0 := by omega
  match k with
  | 0 =>
    exact Curve3PoolDai.dai_coinPullExact hfork hstatic hdep0 (hC.prec 0) (hC.pool 0) (by decide) (by decide) (by decide)
      (fun b hb => ⟨(hb.2.1 _).trans hC.dai, by
        have e := addV_at (k := 0) hb
        show Dai.PullFits (b.getStor (coinOf sevm pre 0)) _ _ _ _
        rw [e]; exact hpf⟩)
      (fun b d hb hl => addV_leave hC ha (Ne.symm (htc 0)) hb hl)
  | 1 =>
    exact UsdcLive.usdc22_coinPullExact hfork hstatic hdepth (hC.prec 1) (hC.pool 1) (by decide) (by decide) (by decide)
      (fun b hb => by
        have e := addV_at (k := 1) hb
        refine ⟨(hb.2.1 _).trans hC.usdc, proxyAt_pinned hC ⟨hb.2.1, e⟩, ?_⟩
        show UsdcLive.PullFits (b.getStor (coinOf sevm pre 1)) _ _ _ _
        rw [e]; exact hpf)
      (fun b d hb hl => addV_leave hC ha (Ne.symm (htc 1)) hb hl)
  | 2 =>
    exact Curve3PoolUsdt.usdt_coinPullExact hfork hstatic hdep0 (hC.prec 2) (hC.pool 2) (by decide) (by decide) (by decide)
      (fun b hb => by
        have e := addV_at (k := 2) hb
        refine ⟨(hb.2.1 _).trans hC.usdt, ?_, ?_⟩
        · show Usdt.NotDeprecated (b.getStor (coinOf sevm pre 2))
          rw [e]; exact hC.live
        · show Usdt.PullFits (b.getStor (coinOf sevm pre 2)) _ _ _ _
          rw [e]; exact hpf)
      (fun b d hb hl => addV_leave hC ha (Ne.symm (htc 2)) hb hl)

/-- **`ALExactPremises` with the real coins and 3Crv.** -/
theorem add_premises {T mint : B256} (hfork : ShanghaiOnwards sevm.benvStat.fork) (hstatic : sevm.isStatic = false) (hdepth : 2 ≤ sevm.depth)
    (hC : RealCoins sevm pre) (hne : sevm.currentTarget ≠ tokOf sevm pre) (htp : ¬ sevm.benvStat.rules.isPrecomp (tokOf sevm pre))
    (hT : (Devm.getStor pre (tokOf sevm pre)).get Curve3Crv.vySupplySlot = T)
    (hmint : MintFits (Devm.getStor pre (tokOf sevm pre)) sevm.currentTarget sevm.caller.toB256 mint)
    (hpf : ∀ k : Fin 3, alAmt sevm k.val ≠ 0 → PullFitsK k (pre.getStor (coinOf sevm pre k)) sevm.caller sevm.currentTarget (alAmt sevm k.val))
    (hlive : alAmt sevm 2 ≠ 0 → Usdt.NotDeprecated (pulledK 2 (pre.getStor (coinOf sevm pre 2)) sevm.caller sevm.currentTarget (alAmt sevm 2))) :
    ALExactPremises sevm (pre.getStor sevm.currentTarget) T (addB1 sevm pre) (addB2 sevm pre) mint
      (alC3W (tokOf sevm pre) (Devm.getStor pre (tokOf sevm pre)) (mintStor (Devm.getStor pre (tokOf sevm pre)) sevm.caller.toB256 mint) (addV sevm pre))
      129555 (addCalls sevm pre) := by
  have hdep0 : sevm.depth ≠ 0 := by omega
  have htc : ∀ j : Fin 3, coinOf sevm pre j ≠ tokOf sevm pre := hC.tok
  refine alExactPremises_c3crv rfl hne hfork hstatic hdep0 htp (by decide) hT hmint (addV_blind htc) ?_ ?_ ?_
  · intro k hk hz
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exact add_pull hfork hstatic hdepth hC htc 0 hz (hpf 0 hz)
    · exact add_pull hfork hstatic hdepth hC htc 1 hz (hpf 1 hz)
    · exact add_pull hfork hstatic hdepth hC htc 2 hz (hpf 2 hz)
  · intro hz
    refine Curve3PoolUsdt.usdt_coinBalExact hfork hdep0 (hC.prec 2) (by decide) (by decide) (by decide) (fun b hb => ?_)
      (fun b d hb hs hc => add_chain_keep htc hb hs hc)
    have e := addV_at (k := 2) hb
    refine ⟨(hb.2.1 _).trans hC.usdt, ?_, ?_⟩
    · show Usdt.NotDeprecated (b.getStor (coinOf sevm pre 2))
      rw [e]; exact hC.live
    · show (b.getStor (coinOf sevm pre 2)).get _ = _
      rw [e]
  · intro hz
    refine Curve3PoolUsdt.usdt_coinBalExact hfork hdep0 (hC.prec 2) (by decide) (by decide) (by decide) (fun b hb => ?_)
      (fun b d hb hs hc => add_chain_keep htc hb hs hc)
    have e : b.getStor (coinOf sevm pre 2) =
        pulledK 2 (pre.getStor (coinOf sevm pre 2)) sevm.caller sevm.currentTarget (alAmt sevm 2) := by
      rw [hb.2.2 2]; exact addLedger_next_self (k := 2) hz
    refine ⟨(hb.2.1 _).trans hC.usdt, ?_, ?_⟩
    · show Usdt.NotDeprecated (b.getStor (coinOf sevm pre 2))
      rw [e]; exact hlive hz
    · show (b.getStor (coinOf sevm pre 2)).get _ = _
      rw [e]

end Blanc.Composition.Curve3PoolPublic
