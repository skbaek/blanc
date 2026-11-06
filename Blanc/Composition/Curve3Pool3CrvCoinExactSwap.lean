import Blanc.Composition.Curve3Pool3CrvCoinExactExit

/-!
# `exchange`'s exact premises with the real coins

`exchange_coins_exact`: the profiles `pool_history_exchange_live_exact` takes, for coin `i` pulled and `j` pushed, each
being DAI, USDC's proxy over V2_2 or USDT by its index, along a world chain, at `U = 129555`, with the coins' debits in
`P := swapCalls`. When USDT is pulled the pool reads its balance twice around the pull; those two reads are its exact
`balanceOf`.
-/

namespace Blanc.Composition.Curve3Pool3CrvLiteralWitness

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.ExecutionTrace Blanc.StableSwapNewton
open Blanc.Composition.Curve3PoolCalleeLive Blanc.Composition.Curve3PoolCoinExactKit
open Blanc.Composition.Curve3Pool3CrvHeadlines (C3Ready C3With C3Blind C3At)
open Blanc.Composition.Curve3Pool3CrvExactAssembly
open Blanc.Composition.Curve3Pool3CrvInstance
open Blanc.Lift.Usdc

/-! ## The coins by index -/

/-- Coin `k`'s ledger after the pool pulls `v`. -/
noncomputable def pulledK (k : Fin 3) (σ : Stor) (src dst : Adr) (v : B256) : Stor :=
  match k with
  | 0 => Blanc.Lift.Dai.moveStor (Blanc.Lift.Dai.spendStor σ src dst v) src dst v
  | 1 => UsdcLive.pullStor σ src dst dst v
  | 2 => Blanc.Lift.Usdt.moveStor (Blanc.Lift.Usdt.spendStor σ src dst v) src dst v (Blanc.Lift.Usdt.feeOf σ v)

/-- The pull fits coin `k`'s ledger. -/
def PullFitsK (k : Fin 3) (σ : Stor) (src dst : Adr) (v : B256) : Prop :=
  match k with
  | 0 => Blanc.Lift.Dai.PullFits σ src dst dst v
  | 1 => UsdcLive.PullFits σ src dst dst v
  | 2 => Blanc.Lift.Usdt.PullFits σ src dst dst v

/-- The push fits coin `k`'s ledger. -/
def PushFitsK (k : Fin 3) (σ : Stor) (src dst : Adr) (v : B256) : Prop :=
  match k with
  | 0 => Blanc.Lift.Dai.MoveFits σ src dst v
  | 1 => UsdcLive.MoveFits σ src dst v
  | 2 => Blanc.Lift.Usdt.XferFits σ src dst v

section Calls

variable (sevm : Sevm) (t : B256)

/-- Coin `k`'s pull debit at `exchange`'s window. -/
noncomputable def swapPullD : Fin 3 → Devm → List B256 → Mem → Nat
  | 0 => coinDebit Blanc.Lift.Dai.pullG sevm t 0x600 0x64 0x6c0
  | 1 => coinDebit UsdcLive.pullG sevm t 0x600 0x64 0x6c0
  | 2 => coinDebit Blanc.Lift.Usdt.pullG sevm t 0x600 0x64 0x6c0

/-- Coin `k`'s pull successor at `exchange`'s window. -/
noncomputable def swapPullN : Fin 3 → Devm → List B256 → Mem → Devm
  | 0 => coinNext (fun s p => Blanc.Lift.Dai.pullPost s p 0) sevm t 0x600 0x64 0x6c0
  | 1 => coinNext (UsdcLive.proxyCanon 1 (fun s p => UsdcLive.implPullPost s p 0)) sevm t 0x600 0x64 0x6c0
  | 2 => coinNext (fun s p => Blanc.Lift.Usdt.pullP s p 0) sevm t 0x600 0x64 0x6c0

/-- Coin `k`'s push debit at `exchange`'s window. -/
noncomputable def swapPushD : Fin 3 → Devm → List B256 → Mem → Nat
  | 0 => coinDebit Blanc.Lift.Dai.xferG sevm t 0xb60 0x44 0xc00
  | 1 => coinDebit UsdcLive.xferG sevm t 0xb60 0x44 0xc00
  | 2 => coinDebit Blanc.Lift.Usdt.xferG sevm t 0xb60 0x44 0xc00

/-- Coin `k`'s push successor at `exchange`'s window. -/
noncomputable def swapPushN : Fin 3 → Devm → List B256 → Mem → Devm
  | 0 => coinNext (fun s p => Blanc.Lift.Dai.xferPost s p 0) sevm t 0xb60 0x44 0xc00
  | 1 => coinNext (UsdcLive.proxyCanon 1 (fun s p => UsdcLive.implXferPost s p 0)) sevm t 0xb60 0x44 0xc00
  | 2 => coinNext (fun s p => Blanc.Lift.Usdt.xferPost s p 0) sevm t 0xb60 0x44 0xc00

end Calls

section World

variable (sevm : Sevm) (pre : Devm) (i j : Fin 3)

/-- `exchange`'s world before the pull: coins `i` and `j` as at the entry. -/
def swapW0 (b : Devm) : Prop := Pin sevm pre i b ∧ Pin sevm pre j b

/-- `exchange`'s world after the pull: coin `i`'s ledger as its pull leaves it, coin `j`'s as at the entry. -/
def swapW1 (b : Devm) : Prop :=
  (∀ a, b.getCode a = pre.getCode a) ∧
    b.getStor (coinOf sevm pre i) = pulledK i (pre.getStor (coinOf sevm pre i)) sevm.caller sevm.currentTarget (exDx sevm) ∧
    Pin sevm pre j b

/-- The pool's USDT word before the pull. -/
noncomputable abbrev swapB1 : B256 :=
  (pre.getStor (coinOf sevm pre i)).get (Blanc.Lift.Usdt.balSlot sevm.currentTarget)

/-- The pool's USDT word after the pull. -/
noncomputable abbrev swapB2 : B256 :=
  (pulledK i (pre.getStor (coinOf sevm pre i)) sevm.caller sevm.currentTarget (exDx sevm)).get
    (Blanc.Lift.Usdt.balSlot sevm.currentTarget)

/-- `exchange`'s exact calls with the real coins. -/
noncomputable def swapCalls : ExchangeExactCalls where
  balD1 := coinStaticDebit Blanc.Lift.Usdt.balG sevm ((pre.getStor sevm.currentTarget).get (coinSlot i)) 0x3dc 0x24 0x440
  balN1 := coinStaticNext (fun s p => Blanc.Lift.Usdt.balP s p 0) sevm ((pre.getStor sevm.currentTarget).get (coinSlot i)) 0x3dc 0x24 0x440
  balD2 := coinStaticDebit Blanc.Lift.Usdt.balG sevm ((pre.getStor sevm.currentTarget).get (coinSlot i)) 0x71c 0x24 0x780
  balN2 := coinStaticNext (fun s p => Blanc.Lift.Usdt.balP s p 0) sevm ((pre.getStor sevm.currentTarget).get (coinSlot i)) 0x71c 0x24 0x780
  pullD := swapPullD sevm ((pre.getStor sevm.currentTarget).get (coinSlot i)) i
  pullN := swapPullN sevm ((pre.getStor sevm.currentTarget).get (coinSlot i)) i
  pushD := swapPushD sevm ((pre.getStor sevm.currentTarget).get (coinSlot j)) j
  pushN := swapPushN sevm ((pre.getStor sevm.currentTarget).get (coinSlot j)) j

end World

variable {sevm : Sevm} {pre : Devm} {i j : Fin 3} {v : B256}

/-- **`exchange_live_exact`'s premises with the real coins.** For `i ≠ j`, ledgers covering the pull of `exDx` and the
push of `v`, and a pulled USDT still undeprecated: the world chain's closure, the two balance reads when USDT is pulled,
the pull and the push, each an exact profile with `swapCalls`' debit and successor, at `U = 129555`. -/
theorem exchange_coins_exact (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : 2 ≤ sevm.depth) (hC : RealCoins sevm pre) (hij : i ≠ j)
    (hpf : PullFitsK i (pre.getStor (coinOf sevm pre i)) sevm.caller sevm.currentTarget (exDx sevm))
    (hqf : PushFitsK j (pre.getStor (coinOf sevm pre j)) sevm.currentTarget sevm.caller v)
    (hlive : i = 2 → Blanc.Lift.Usdt.NotDeprecated
      (pulledK i (pre.getStor (coinOf sevm pre i)) sevm.caller sevm.currentTarget (exDx sevm))) :
    WClosed sevm (swapW0 sevm pre i j) ∧ WClosed sevm (swapW1 sevm pre i j) ∧ swapW0 sevm pre i j pre ∧
      WClosed sevm (fun _ => True) ∧
      (i = feeIndex →
        StaticWordCallProfile sevm (swapW0 sevm pre i j) (swapW0 sevm pre i j)
          ((pre.getStor sevm.currentTarget).get (coinSlot i)) (balanceOfData sevm.currentTarget)
          (swapB1 sevm pre i) 129555 0x3dc 0x24 0x440 (swapCalls sevm pre i j).balD1 (swapCalls sevm pre i j).balN1 ∧
        StaticWordCallProfile sevm (swapW1 sevm pre i j) (swapW1 sevm pre i j)
          ((pre.getStor sevm.currentTarget).get (coinSlot i)) (balanceOfData sevm.currentTarget)
          (swapB2 sevm pre i) 129555 0x71c 0x24 0x780 (swapCalls sevm pre i j).balD2 (swapCalls sevm pre i j).balN2) ∧
      MutableCallProfile sevm (swapW0 sevm pre i j) (swapW1 sevm pre i j)
        ((pre.getStor sevm.currentTarget).get (coinSlot i))
        (transferFromSel ++ sevm.caller.toB256.toBytes ++ sevm.currentTarget.toB256.toBytes ++ (exDx sevm).toBytes)
        RawCallOk 129555 0x600 0x64 0x6c0 (swapCalls sevm pre i j).pullD (swapCalls sevm pre i j).pullN ∧
      MutableCallProfile sevm (swapW1 sevm pre i j) (fun _ => True)
        ((pre.getStor sevm.currentTarget).get (coinSlot j))
        (transferSel ++ sevm.caller.toB256.toBytes ++ v.toBytes) RawCallOk 129555 0xb60 0x44 0xc00
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
    refine ⟨Blanc.Composition.Curve3PoolUsdt.usdt_coinBalExact hfork hdep0 (hC.prec 2) (by decide) (by decide) (by decide)
        (fun b hb => ?_) (fun b d hb hs hc => keep0 b d hb hs hc),
      Blanc.Composition.Curve3PoolUsdt.usdt_coinBalExact hfork hdep0 (hC.prec 2) (by decide) (by decide) (by decide)
        (fun b hb => ?_) (fun b d hb hs hc => keep1 b d hb hs hc)⟩
    · have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 2)).toAdr = pre.getStor (coinOf sevm pre 2) := hb.1.2
      exact ⟨(hb.1.1 _).trans hC.usdt, by rw [e]; exact hC.live, by rw [e]⟩
    · have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 2)).toAdr =
          pulledK 2 (pre.getStor (coinOf sevm pre 2)) sevm.caller sevm.currentTarget (exDx sevm) := hb.2.1
      exact ⟨(hb.1 _).trans hC.usdt, by rw [e]; exact hlive rfl, by rw [e]⟩
  · show MutableCallProfile _ _ _ _ _ _ _ _ _ _ (swapPullD sevm _ i) (swapPullN sevm _ i)
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) i with rfl | rfl | rfl
    · exact Blanc.Composition.Curve3PoolDai.dai_coinPullExact hfork hstatic hdep0 (hC.prec 0) (hC.pool 0)
        (by decide) (by decide) (by decide)
        (fun b hb => ⟨(hb.1.1 _).trans hC.dai, by
          have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 0)).toAdr = pre.getStor (coinOf sevm pre 0) := hb.1.2
          rw [e]; exact hpf⟩)
        (fun b d hb hl => leave hb hl)
    · exact UsdcLive.usdc22_coinPullExact hfork hstatic hdepth (hC.prec 1) (hC.pool 1)
        (by decide) (by decide) (by decide)
        (fun b hb => ⟨(hb.1.1 _).trans hC.usdc, proxyAt_pinned hC hb.1, by
          have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 1)).toAdr = pre.getStor (coinOf sevm pre 1) := hb.1.2
          rw [e]; exact hpf⟩)
        (fun b d hb hl => leave hb hl)
    · exact Blanc.Composition.Curve3PoolUsdt.usdt_coinPullExact hfork hstatic hdep0 (hC.prec 2) (hC.pool 2)
        (by decide) (by decide) (by decide)
        (fun b hb => by
          have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 2)).toAdr = pre.getStor (coinOf sevm pre 2) := hb.1.2
          exact ⟨(hb.1.1 _).trans hC.usdt, by rw [e]; exact hC.live, by rw [e]; exact hpf⟩)
        (fun b d hb hl => leave hb hl)
  · show MutableCallProfile _ _ _ _ _ _ _ _ _ _ (swapPushD sevm _ j) (swapPushN sevm _ j)
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) j with rfl | rfl | rfl
    · exact Blanc.Composition.Curve3PoolDai.dai_coinPushExact hfork hstatic hdep0 (hC.prec 0) (hC.pool 0)
        (by decide) (by decide) (by decide)
        (fun b hb => ⟨(hb.2.2.1 _).trans hC.dai, by
          have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 0)).toAdr = pre.getStor (coinOf sevm pre 0) := hb.2.2.2
          rw [e]; exact hqf⟩)
        (fun _ _ _ _ => trivial)
    · exact UsdcLive.usdc22_coinPushExact hfork hstatic hdepth (hC.prec 1) (hC.pool 1)
        (by decide) (by decide) (by decide)
        (fun b hb => ⟨(hb.2.2.1 _).trans hC.usdc, proxyAt_pinned hC hb.2.2, by
          have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 1)).toAdr = pre.getStor (coinOf sevm pre 1) := hb.2.2.2
          rw [e]; exact hqf⟩)
        (fun _ _ _ _ => trivial)
    · exact Blanc.Composition.Curve3PoolUsdt.usdt_coinPushExact hfork hstatic hdep0 (hC.prec 2) (hC.pool 2)
        (by decide) (by decide) (by decide)
        (fun b hb => by
          have e : b.getStor ((pre.getStor sevm.currentTarget).get (coinSlot 2)).toAdr = pre.getStor (coinOf sevm pre 2) := hb.2.2.2
          exact ⟨(hb.2.2.1 _).trans hC.usdt, by rw [e]; exact hC.live, by rw [e]; exact hqf⟩)
        (fun _ _ _ _ => trivial)

end Blanc.Composition.Curve3Pool3CrvLiteralWitness
