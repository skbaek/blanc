import Blanc.Lift.Curve3Pool.Walk.RliLiveTail

/-!
# `remove_liquidity_imbalance`, forward: the fee loop composed, and the whole frame

`rx_rli_feeLoop` runs the fee loop from `t_336e_c1039` over its three `RliFeeIter`s, whichever
contexts the differences select (`rx_rli_fee12a`, `rx_rli_fee12b`). `rx_rli_frame` composes the
dispatcher, the guards, `D0`, `D1`, the fee loop, `D2`, the burn, the transfers and the event,
under the machine-word checks of the entry storage and the callees' window premises.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- Fee iterations 1–2 from `t_336e_c1048`, forward. -/
theorem rx_rli_fee12a {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop}
    {T F AF Aw D0 D1 B1 B2 N1 N2 x0 f0 f1 f2 s1 s2 x1 x2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x660)
    (hc : WordAt img 0x600 (Nat.toB256 1)) (hT : WordAt img 0x140 T) (hF : WordAt img 0x1e0 F)
    (hAF : WordAt img 0x200 AF) (hAw : WordAt img 0x220 Aw) (hB1 : WordAt img 0x2a0 B1)
    (hB2 : WordAt img 0x2c0 B2) (hx0 : WordAt img 0x2e0 x0) (hN1 : WordAt img 0x300 N1)
    (hN2 : WordAt img 0x320 N2) (hD0w : WordAt img 0x340 D0) (hD1 : WordAt img 0x480 D1)
    (hf0 : WordAt img 0x5a0 f0)
    (h1 : RliFeeIter F AF D0 D1 B1 N1 f1 s1 x1) (h2 : RliFeeIter F AF D0 D1 B2 N2 f2 s2 x2)
    (hG : 52000 + R ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' ((σ.set (balancesBase + Nat.toB256 1) s1).set (balancesBase + Nat.toB256 2) s2) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 → WordAt img' 0x140 T → WordAt img' 0x1e0 F → WordAt img' 0x200 AF →
      WordAt img' 0x220 Aw → WordAt img' 0x2e0 x0 → WordAt img' 0x300 x1 →
      WordAt img' 0x320 x2 → WordAt img' 0x340 D0 → WordAt img' 0x480 D1 →
      WordAt img' 0x5a0 f0 → WordAt img' 0x5c0 f1 → WordAt img' 0x5e0 f2 → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) rliExit Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) t_336e_c1048 Q := by
  refine rx_rli_fee1a (R := 26000 + R) hfork hstatic hL hR hW hsz hc hD1 hD0w hB1 hN1 hF hAF h1 (by omega)
    hroom ?_ ?_
  all_goals
    intro b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hk1 hn1 hf1' hc1 hg1 hg1'
    refine rx_rli_fee2 (R := R) hfork hstatic hL1 hR1 hW1 hsz1 hc1 (hk1 _ _ hD1 (by omega))
      (hk1 _ _ hD0w (by omega)) (hk1 _ _ hB2 (by omega)) (hk1 _ _ hN2 (by omega))
      (hk1 _ _ hF (by omega)) (hk1 _ _ hAF (by omega)) h2 (by omega) hroom ?_ ?_
    all_goals
      intro b2 M2 img2 g2 hL2 hR2 hW2 hsz2 hk2 hn2 hf2' hc2 hg2 hg2'
      exact k b2 M2 img2 g2 hL2 hR2 hW2 hsz2 (hk2 _ _ (hk1 _ _ hT (by omega)) (by omega))
        (hk2 _ _ (hk1 _ _ hF (by omega)) (by omega)) (hk2 _ _ (hk1 _ _ hAF (by omega)) (by omega))
        (hk2 _ _ (hk1 _ _ hAw (by omega)) (by omega)) (hk2 _ _ (hk1 _ _ hx0 (by omega)) (by omega))
        (hk2 _ _ hn1 (by omega)) hn2 (hk2 _ _ (hk1 _ _ hD0w (by omega)) (by omega))
        (hk2 _ _ (hk1 _ _ hD1 (by omega)) (by omega)) (hk2 _ _ (hk1 _ _ hf0 (by omega)) (by omega))
        (hk2 _ _ hf1' (by omega)) hf2' hg2 (by omega)

/-- Fee iterations 1–2 from `t_336e_c1055`, forward. -/
theorem rx_rli_fee12b {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256} {M : Mem}
    {img : Bytes} {G R : Nat} {Q : Outcome → Prop}
    {T F AF Aw D0 D1 B1 B2 N1 N2 x0 f0 f1 f2 s1 s2 x1 x2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x660)
    (hc : WordAt img 0x600 (Nat.toB256 1)) (hT : WordAt img 0x140 T) (hF : WordAt img 0x1e0 F)
    (hAF : WordAt img 0x200 AF) (hAw : WordAt img 0x220 Aw) (hB1 : WordAt img 0x2a0 B1)
    (hB2 : WordAt img 0x2c0 B2) (hx0 : WordAt img 0x2e0 x0) (hN1 : WordAt img 0x300 N1)
    (hN2 : WordAt img 0x320 N2) (hD0w : WordAt img 0x340 D0) (hD1 : WordAt img 0x480 D1)
    (hf0 : WordAt img 0x5a0 f0)
    (h1 : RliFeeIter F AF D0 D1 B1 N1 f1 s1 x1) (h2 : RliFeeIter F AF D0 D1 B2 N2 f2 s2 x2)
    (hG : 52000 + R ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' ((σ.set (balancesBase + Nat.toB256 1) s1).set (balancesBase + Nat.toB256 2) s2) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 → WordAt img' 0x140 T → WordAt img' 0x1e0 F → WordAt img' 0x200 AF →
      WordAt img' 0x220 Aw → WordAt img' 0x2e0 x0 → WordAt img' 0x300 x1 →
      WordAt img' 0x320 x2 → WordAt img' 0x340 D0 → WordAt img' 0x480 D1 →
      WordAt img' 0x5a0 f0 → WordAt img' 0x5c0 f1 → WordAt img' 0x5e0 f2 → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) rliExit Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) t_336e_c1055 Q := by
  refine rx_rli_fee1b (R := 26000 + R) hfork hstatic hL hR hW hsz hc hD1 hD0w hB1 hN1 hF hAF h1 (by omega)
    hroom ?_ ?_
  all_goals
    intro b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hk1 hn1 hf1' hc1 hg1 hg1'
    refine rx_rli_fee2 (R := R) hfork hstatic hL1 hR1 hW1 hsz1 hc1 (hk1 _ _ hD1 (by omega))
      (hk1 _ _ hD0w (by omega)) (hk1 _ _ hB2 (by omega)) (hk1 _ _ hN2 (by omega))
      (hk1 _ _ hF (by omega)) (hk1 _ _ hAF (by omega)) h2 (by omega) hroom ?_ ?_
    all_goals
      intro b2 M2 img2 g2 hL2 hR2 hW2 hsz2 hk2 hn2 hf2' hc2 hg2 hg2'
      exact k b2 M2 img2 g2 hL2 hR2 hW2 hsz2 (hk2 _ _ (hk1 _ _ hT (by omega)) (by omega))
        (hk2 _ _ (hk1 _ _ hF (by omega)) (by omega)) (hk2 _ _ (hk1 _ _ hAF (by omega)) (by omega))
        (hk2 _ _ (hk1 _ _ hAw (by omega)) (by omega)) (hk2 _ _ (hk1 _ _ hx0 (by omega)) (by omega))
        (hk2 _ _ hn1 (by omega)) hn2 (hk2 _ _ (hk1 _ _ hD0w (by omega)) (by omega))
        (hk2 _ _ (hk1 _ _ hD1 (by omega)) (by omega)) (hk2 _ _ (hk1 _ _ hf0 (by omega)) (by omega))
        (hk2 _ _ hf1' (by omega)) hf2' hg2 (by omega)

/-- **The fee loop, forward.** -/
theorem rx_rli_feeLoop {sevm : Sevm} {b : Devm} {σ : Stor} {W : Devm → Prop} {S : List B256}
    {M : Mem} {img : Bytes} {G R : Nat} {Q : Outcome → Prop}
    {T F AF Aw D0 D1 B0 B1 B2 N0 N1 N2 f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x620)
    (hc : WordAt img 0x600 (Nat.toB256 0)) (hT : WordAt img 0x140 T) (hF : WordAt img 0x1e0 F)
    (hAF : WordAt img 0x200 AF) (hAw : WordAt img 0x220 Aw) (hB0 : WordAt img 0x280 B0)
    (hB1 : WordAt img 0x2a0 B1) (hB2 : WordAt img 0x2c0 B2) (hN0 : WordAt img 0x2e0 N0)
    (hN1 : WordAt img 0x300 N1) (hN2 : WordAt img 0x320 N2) (hD0w : WordAt img 0x340 D0)
    (hD1 : WordAt img 0x480 D1)
    (h0 : RliFeeIter F AF D0 D1 B0 N0 f0 s0 x0) (h1 : RliFeeIter F AF D0 D1 B1 N1 f1 s1 x1)
    (h2 : RliFeeIter F AF D0 D1 B2 N2 f2 s2 x2)
    (hG : 78000 + R ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat),
      ExLive sevm W b' (((σ.set (balancesBase + Nat.toB256 0) s0).set (balancesBase + Nat.toB256 1)
        s1).set (balancesBase + Nat.toB256 2) s2) →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x660 → WordAt img' 0x140 T → WordAt img' 0x1e0 F → WordAt img' 0x200 AF →
      WordAt img' 0x220 Aw → WordAt img' 0x2e0 x0 → WordAt img' 0x300 x1 →
      WordAt img' 0x320 x2 → WordAt img' 0x340 D0 → WordAt img' 0x480 D1 →
      WordAt img' 0x5a0 f0 → WordAt img' 0x5c0 f1 → WordAt img' 0x5e0 f2 → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
        Bytes.toB256 [6, 0] :: S) M' g) rliExit Q) :
    SFunc.RunEx cert.prog sevm (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) ::
      Bytes.toB256 [6, 0] :: S) M G) t_336e_c1039 Q := by
  refine rx_rli_fee0 (R := 52000 + R) hfork hstatic hL hR hW hsz hc hD1 hD0w hB0 hN0 hF hAF h0
    (by omega) hroom ?_ ?_
  · intro b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hk1 hn1 hf1' hc1 hg1 hg1'
    exact rx_rli_fee12a hfork hstatic hL1 hR1 hW1 hsz1 hc1 (hk1 _ _ hT (by omega))
      (hk1 _ _ hF (by omega)) (hk1 _ _ hAF (by omega)) (hk1 _ _ hAw (by omega))
      (hk1 _ _ hB1 (by omega)) (hk1 _ _ hB2 (by omega)) hn1 (hk1 _ _ hN1 (by omega))
      (hk1 _ _ hN2 (by omega)) (hk1 _ _ hD0w (by omega)) (hk1 _ _ hD1 (by omega)) hf1' h1 h2
      hg1 hroom (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 hr hgg =>
        k b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 hr (le_trans hgg hg1'))
  · intro b1 M1 img1 g1 hL1 hR1 hW1 hsz1 hk1 hn1 hf1' hc1 hg1 hg1'
    exact rx_rli_fee12b hfork hstatic hL1 hR1 hW1 hsz1 hc1 (hk1 _ _ hT (by omega))
      (hk1 _ _ hF (by omega)) (hk1 _ _ hAF (by omega)) (hk1 _ _ hAw (by omega))
      (hk1 _ _ hB1 (by omega)) (hk1 _ _ hB2 (by omega)) hn1 (hk1 _ _ hN1 (by omega))
      (hk1 _ _ hN2 (by omega)) (hk1 _ _ hD0w (by omega)) (hk1 _ _ hD1 (by omega)) hf1' h1 h2
      hg1 hroom (fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 hr hgg =>
        k b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 hr (le_trans hgg hg1'))

section Frame

variable {sevm : Sevm} {pre : Devm} {s : State} {W : Nat → Devm → Prop} {U G amp v0 v1 v2 : Nat}
  {Q : Outcome → Prop} {T f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256} {xa xb xc : V3}

/-- The storage the fee loop leaves: the lock set and the three stored balances. -/
abbrev rliStor (σ : Stor) (s0 s1 s2 : B256) : Stor :=
  (((σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [1])).set (balancesBase + Nat.toB256 0)
    s0).set (balancesBase + Nat.toB256 1) s1).set (balancesBase + Nat.toB256 2) s2

theorem rliStor_get {σ : Stor} {s0 s1 s2 x : B256} (hx : x ≠ lockSlot)
    (h0 : x ≠ balancesBase + Nat.toB256 0) (h1 : x ≠ balancesBase + Nat.toB256 1)
    (h2 : x ≠ balancesBase + Nat.toB256 2) : (rliStor σ s0 s1 s2).get x = σ.get x := by
  unfold rliStor
  rw [Stor.get_set_ne _ (Ne.symm h2), Stor.get_set_ne _ (Ne.symm h1), Stor.get_set_ne _ (Ne.symm h0),
    Stor.get_set_ne _ (by rw [lockSlot_lit]; exact Ne.symm hx)]

/-- **The `remove_liquidity_imbalance` frame, forward**, along a world chain: the supply read in
`W 0`, the burn from `W 0` to `W 1`, coin `j`'s transfer (when its amount is nonzero) from
`W (j + 1)` to `W (j + 2)`, a skipped transfer staying inside `W (j + 2)`. -/
theorem rx_rli_frame (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance) (hid : IdReady sevm pre)
    (hWc : ∀ j, j ≤ 4 → WClosed sevm (W j)) (hWb : W 0 pre)
    (ha : Abstracts (pre.getStor sevm.currentTarget) s)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hsup : SupplyOkAt sevm (W 0) (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T U
      0x17c 0x1c0)
    (hT0 : T ≠ 0)
    (hmf : (pre.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [0x03] /
        (pre.getStor sevm.currentTarget).get feeSlot = Bytes.toB256 [0x03] ∨
      (pre.getStor sevm.currentTarget).get feeSlot = 0)
    (hX0 : xpChk ⟨(balAt (pre.getStor sevm.currentTarget) 0).toNat,
      (balAt (pre.getStor sevm.currentTarget) 1).toNat,
      (balAt (pre.getStor sevm.currentTarget) 2).toNat⟩ = some xa)
    (hD0 : getDChk xa.get amp 1 = some v0)
    (hu0 : ¬ balAt (pre.getStor sevm.currentTarget) 0 < rliAmt sevm 0)
    (hu1 : ¬ balAt (pre.getStor sevm.currentTarget) 1 < rliAmt sevm 1)
    (hu2 : ¬ balAt (pre.getStor sevm.currentTarget) 2 < rliAmt sevm 2)
    (hX1 : xpChk ⟨(balAt (pre.getStor sevm.currentTarget) 0 - rliAmt sevm 0).toNat,
      (balAt (pre.getStor sevm.currentTarget) 1 - rliAmt sevm 1).toNat,
      (balAt (pre.getStor sevm.currentTarget) 2 - rliAmt sevm 2).toNat⟩ = some xb)
    (hD1 : getDChk xb.get amp 1 = some v1)
    (h0 : RliFeeIter (cwFee ((pre.getStor sevm.currentTarget).get feeSlot))
      ((pre.getStor sevm.currentTarget).get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
      (balAt (pre.getStor sevm.currentTarget) 0)
      (balAt (pre.getStor sevm.currentTarget) 0 - rliAmt sevm 0) f0 s0 x0)
    (h1 : RliFeeIter (cwFee ((pre.getStor sevm.currentTarget).get feeSlot))
      ((pre.getStor sevm.currentTarget).get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
      (balAt (pre.getStor sevm.currentTarget) 1)
      (balAt (pre.getStor sevm.currentTarget) 1 - rliAmt sevm 1) f1 s1 x1)
    (h2 : RliFeeIter (cwFee ((pre.getStor sevm.currentTarget).get feeSlot))
      ((pre.getStor sevm.currentTarget).get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
      (balAt (pre.getStor sevm.currentTarget) 2)
      (balAt (pre.getStor sevm.currentTarget) 2 - rliAmt sevm 2) f2 s2 x2)
    (hX2 : xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc)
    (hD2 : getDChk xc.get amp 1 = some v2)
    (hD02 : ¬ Nat.toB256 v0 < Nat.toB256 v2) (hmT : (Nat.toB256 v0 - Nat.toB256 v2).Nofm T)
    (hbn : (Nat.toB256 v0 - Nat.toB256 v2) * T / Nat.toB256 v0 ≠ 0)
    (hb1 : ¬ rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T <
      (Nat.toB256 v0 - Nat.toB256 v2) * T / Nat.toB256 v0)
    (hslip : ¬ Sevm.dataWord sevm (Bytes.toB256 [0x64]) < rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T)
    (hTX : ¬ T < rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T)
    (hburn : BurnOkAt sevm (W 0) (W 1) ((pre.getStor sevm.currentTarget).get tokenSlot)
      (rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T) U 0x85c 0x8e0)
    (hp0 : rliAmt sevm 0 ≠ 0 → CoinPushOkAt sevm (W 1) (W 2)
      ((pre.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 0)) (rliAmt sevm 0) U 0xaa0 0xb40)
    (hp1 : rliAmt sevm 1 ≠ 0 → CoinPushOkAt sevm (W 2) (W 3)
      ((pre.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 1)) (rliAmt sevm 1) U 0xaa0 0xb40)
    (hp2 : rliAmt sevm 2 ≠ 0 → CoinPushOkAt sevm (W 3) (W 4)
      ((pre.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 2)) (rliAmt sevm 2) U 0xaa0 0xb40)
    (hskip : ∀ j, j < 3 → rliAmt sevm j = 0 → ∀ b, W (j + 1) b → W (j + 2) b)
    (hG : costGetDMem xa amp + costGetDMem xb amp + costGetDMem xc amp + 240000 + 5 * U ≤ G)
    (hGb : G + 3000 < 2 ^ 256)
    (k : ∀ D : Devm, ExLive sevm (W 4) D ((rliStor (pre.getStor sevm.currentTarget) s0 s1 s2).set
        (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      (∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
        Bytes.toB256 (data.sliceD 0x60 32 0) = f0 ∧ Bytes.toB256 (data.sliceD 0x80 32 0) = f1 ∧
        Bytes.toB256 (data.sliceD 0xa0 32 0) = f2 ∧
        Bytes.toB256 (data.sliceD 0xc0 32 0) = Nat.toB256 v1 ∧
        Bytes.toB256 (data.sliceD 0xe0 32 0) = T - rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T) →
      Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty G) t_0000_c0 Q := by
  set σ := pre.getStor sevm.currentTarget with hσ
  obtain ⟨g0, rfl⟩ : ∃ g, G = g + 480 := ⟨G - 480, by omega⟩
  refine rx_dispatch_rli hlen hcd hsel ?_
  refine rx_rli_pre (R := g0 - 60000 - U) hfork hstatic ⟨fun _ => rfl, hid, hWc 0 (by decide), hWb⟩
    ha hlock hval
    hkill hA (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyMem_wf Mem.wf_empty _)
    (vyMem_empty_size _) hsup hT0 hmf (by omega) (by omega) ?_
  intro b1 M1 img1 g1 Aw hAw hL1 hR1 hW1 hsz1 wT wF wAF wAw wb0 wb1 wb2 wc0 wc1 wc2 wctr hg1 hg1'
  subst hAw
  -- `D0`, `new_balances`
  refine rx_rli_d0 (R := g1 - costGetDMem xa Aw.toNat - 5000) (S := []) hX0 hD0 hu0 hu1 hu2 hR1 hW1
    hsz1 wctr wT wF wAF wAw wb0 wb1 wb2 wc0 wc1 wc2 (by omega) (by simp only [List.length_nil]; omega) ?_
  intro M2 img2 g2 hR2 hW2 hsz2 vT vF vAF vAw vb0 vb1 vb2 vn0 vn1 vn2 vD0 vctr hg2 hg2'
  -- `D1`
  refine rx_rli_d1 (R := g2 - costGetDMem xb Aw.toNat - 7000) (S := []) hX1 hD1 hR2 hW2 hsz2 vctr vT
    vF vAF vAw vb0 vb1 vb2 vn0 vn1 vn2 vD0 (by omega) (by simp only [List.length_nil]; omega) ?_
  intro M3 img3 g3 hR3 hW3 hsz3 uT uF uAF uAw ub0 ub1 ub2 un0 un1 un2 uD0 uD1 uctr hg3 hg3'
  -- the fee loop
  refine rx_rli_feeLoop (R := g3 - 78000) hfork hstatic hL1 hR3 hW3 hsz3
    (by rw [show Nat.toB256 0 = Bytes.toB256 [0] by decide]; exact uctr) uT uF uAF uAw ub0 ub1 ub2
    un0 un1 un2 uD0 uD1 h0 h1 h2 (by omega) (by simp only [List.length_nil, List.length_cons]; omega) ?_
  intro b4 M4 img4 g4 hL4 hR4 hW4 hsz4 tT tF tAF tAw tx0 tx1 tx2 tD0 tD1 tf0 tf1 tf2 hg4 hg4'
  -- `D2`, the burn
  have e_tok : (rliStor σ s0 s1 s2).get tokenSlot = σ.get tokenSlot :=
    rliStor_get (by decide) (by decide) (by decide) (by decide)
  refine rx_rli_d2 (R := g4 - costGetDMem xc Aw.toNat - 13000 - U) hfork hstatic hL4 (hWc 1 (by decide)) hX2 hD2
    hD02 hmT h0.2.1 hbn hb1 hslip (by rw [e_tok]; exact hburn) hR4 hW4 hsz4 tT tF tAF tAw tx0 tx1 tx2
    tD0 tD1 tf0 tf1 tf2 (by omega) (by omega) (by simp only [List.length_nil, List.length_cons]; omega) ?_
  intro b5 M5 img5 g5 hL5 hR5 hW5 hsz5 pT pD1 pf0 pf1 pf2 pB pctr hg5 hg5'
  -- the transfers, the event
  have e_coin : ∀ j, j < 3 → (rliStor σ s0 s1 s2).get (coinsBase + Nat.toB256 j) =
      σ.get (coinsBase + Nat.toB256 j) := by
    intro j hj
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    all_goals exact rliStor_get (by decide) (by decide) (by decide) (by decide)
  exact rx_rli_tail0 (V := fun j => W (j + 1)) hfork hstatic hdepth hL5 hR5 hW5 hsz5
    (by rw [show Nat.toB256 0 = Bytes.toB256 [0] by decide]; exact pctr) pT pD1 pf0 pf1 pf2 pB hTX
    (fun j hj => hWc (j + 1) (by omega)) hskip
    (by rw [e_coin 0 (by decide)]; exact hp0) (by rw [e_coin 1 (by decide)]; exact hp1)
    (by rw [e_coin 2 (by decide)]; exact hp2) (by omega) (by omega)
    (by simp only [List.length_nil, List.length_cons]; omega) k

end Frame

end Blanc.Lift.Curve3Pool
