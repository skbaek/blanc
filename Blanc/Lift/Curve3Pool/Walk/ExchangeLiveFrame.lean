import Blanc.Lift.Curve3Pool.Walk.ExchangeLivePush
import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveBal

/-!
# `exchange`, forward: the whole frame

`rx_ex_back` composes the segments after the pull (`x`, the frame save, `get_y`, the restore,
`dy`, the stores, the push, the event, `STOP`); `rx_ex_frame` composes the dispatcher, the guards,
`_xp_mem`, the pull with its optional `balanceOf` pair, and `rx_ex_back`: from the frame's entry
with the `exchange` selector, enough gas and the callees answering as premised, the frame runs to
`STOP` with the pool's storage the entry storage with both balances stored and the lock clear.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- `_A`'s gas is at most `458` plus four cold loads. -/
theorem aGas_le (sevm : Sevm) (b : Devm) : aGas sevm b ≤ 8858 := by
  unfold aGas
  have h1 := sloadCost_le sevm b futureATimeSlot
  have h2 := sloadCost_le sevm (afterSload sevm b futureATimeSlot) futureASlot
  have h3 := sloadCost_le sevm (afterSload sevm (afterSload sevm b futureATimeSlot) futureASlot)
    initialASlot
  have h4 := sloadCost_le sevm (afterSload sevm (afterSload sevm (afterSload sevm b
    futureATimeSlot) futureASlot) initialASlot) initialATimeSlot
  have e : gasColdSload = 2100 := rfl
  split_ifs <;> omega

/-- `get_y`'s gas over one base is at most its gas over any other plus `_A`'s worst case. -/
theorem costGetY_le (sevm : Sevm) (b b' : Devm) (amp i j x x0 x1 x2 : Nat) :
    costGetY sevm b amp i j x x0 x1 x2 ≤ costGetY sevm b' amp i j x x0 x1 x2 + 8858 := by
  unfold costGetY
  have := aGas_le sevm b
  omega

/-- The pool's storage at the end of `exchange`: both balances stored, the lock clear. -/
abbrev exFinal (σ : Stor) (sevm : Sevm) (bi bj : B256) : Stor :=
  ((σ.set (balancesBase + exI sevm) bi).set (balancesBase + exJ sevm) bj).set
    (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])

section Back

variable {sevm : Sevm} {b : Devm} {σ : Stor} {s0 : State} {G U amp v : Nat} {Q : Outcome → Prop}
  {M : Mem} {img : Bytes} {W : Devm → Prop} {B X : Nat → B256} {D C : B256} {s c0 : Nat}

/-- **`exchange` after the pull, forward** (`t_26c9_c13` → `STOP`). -/
theorem rx_ex_back (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hL : ExLive sevm W b σ) (ha : Abstracts σ s0)
    (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = s)
    (hs : (s = 0x6e0 ∧ c0 = 26) ∨ (s = 0x7a0 ∧ c0 = 6)) (hF : ExFrame img B X D C)
    (hmx : D * exRate (exI sevm).toNat / D = exRate (exI sevm).toNat ∨ D = 0)
    (hax : ¬ X (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0 < X (exI sevm).toNat)
    (hA : aChk s0 sevm.benvStat.time.toNat = some amp)
    (hres : getYChk amp ⟨(exI sevm).toNat, hi⟩ ⟨(exJ sevm).toNat, hj⟩
      (X (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0).toNat
      (V3.mk (X 0).toNat (X 1).toNat (X 2).toNat).get = some v)
    (hy1 : ¬ X (exJ sevm).toNat < Nat.toB256 v)
    (hy2 : ¬ X (exJ sevm).toNat - Nat.toB256 v < Bytes.toB256 [1])
    (hmf : exDy0 (X (exJ sevm).toNat) (Nat.toB256 v) * σ.get feeSlot /
      exDy0 (X (exJ sevm).toNat) (Nat.toB256 v) = σ.get feeSlot ∨
      exDy0 (X (exJ sevm).toNat) (Nat.toB256 v) = 0)
    (hsf : ¬ exDy0 (X (exJ sevm).toNat) (Nat.toB256 v) <
      exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
    (hmo : (exDy0 (X (exJ sevm).toNat) (Nat.toB256 v) -
        exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)) * exR0 /
        (exDy0 (X (exJ sevm).toNat) (Nat.toB256 v) -
          exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)) = exR0 ∨
      exDy0 (X (exJ sevm).toNat) (Nat.toB256 v) -
        exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) = 0)
    (hmin : ¬ exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)
      (exRate (exJ sevm).toNat) < exMinDy sevm)
    (hma : exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) * σ.get adminFeeSlot /
        exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) = σ.get adminFeeSlot ∨
      exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) = 0)
    (hmap : exAdm0 (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
        (σ.get adminFeeSlot) * exR0 /
        exAdm0 (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
          (σ.get adminFeeSlot) = exR0 ∨
      exAdm0 (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
        (σ.get adminFeeSlot) = 0)
    (hbi : ¬ B (exI sevm).toNat + D < B (exI sevm).toNat)
    (hbj1 : ¬ B (exJ sevm).toNat < exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)
      (exRate (exJ sevm).toNat))
    (hbj2 : ¬ B (exJ sevm).toNat - exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)
        (exRate (exJ sevm).toNat) <
      exAdm (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)) (σ.get adminFeeSlot)
        (exRate (exJ sevm).toNat))
    (hpush : CoinPushOkAt sevm W W (σ.get (coinsBase + exJ sevm))
      (exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) (exRate (exJ sevm).toNat))
      U 0xb60 0xc00)
    (hG : costGetY sevm b amp (exI sevm).toNat (exJ sevm).toNat
      (X (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0).toNat (X 0).toNat (X 1).toNat
      (X 2).toNat + 101000 + U ≤ G) (hGb : G + 2000 < 2 ^ 256)
    (k : ∀ D' : Devm, ExLive sevm W D' (exFinal σ sevm (B (exI sevm).toNat + D)
      (B (exJ sevm).toNat - exDyOut (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)
        (exRate (exJ sevm).toNat) -
        exAdm (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)) (σ.get adminFeeSlot)
          (exRate (exJ sevm).toNat))) → Q (.halted D')) :
    SFunc.RunEx cert.prog sevm (St b [] M G) t_26c9_c13 Q := by
  refine rx_ex_x (R := G - 400) hi hR hW hsz hs hF hmx hax (by omega) ?_
  intro M1 img1 g1 hR1 hW1 hsz1 hF1 hx1 hc1 hg1 hg1'
  rw [show Bytes.toB256 [1, 0x40] = Nat.toB256 (0x140 + 32 * 0) by decide] at hc1
  obtain ⟨g2, rfl⟩ : ∃ g, g1 = g + 67 * 52 + 56 := ⟨g1 - 3540, by omega⟩
  rw [ex_save_first, show ([] : List B256) = [] from rfl]
  refine rx_ex_saveFrom (fun o => Bytes.toB256 (img1.sliceD o 32 0)) 52 (n := 0) (S := [])
    rfl hR1 hW1 hsz1 hc1 (fun m _ _ => WordAt.self _ _) (by simp only [List.length_nil]; omega) ?_
  intro M2 img2 hR2 hW2 hsz2 hk2
  rw [List.append_nil]
  refine rx_ex_y (R := g2 - costGetY sevm b amp (exI sevm).toNat (exJ sevm).toNat
      (X (exI sevm).toNat + D * exRate (exI sevm).toNat / exR0).toNat (X 0).toNat (X 1).toNat
      (X 2).toNat - 3906) hfork hL ha hA hi hj hres hR2 hW2 hsz2
    (hF1.mono fun o v hv ho => hk2 o v hv (by omega)) (hk2 _ _ hx1 (by omega)) (by omega) ?_
  intro b3 M3 img3 g3 hL3 hR3 hW3 hsz3 hm3 hy3 hg3 hg3'
  have hF3 : ExFrame img3 B X D C :=
    ExFrame.of_restore hF1 fun m hm => hm3 m (by omega)
  refine rx_ex_dy (R := g3 - 3000) hfork hL3 hj hR3 hW3 hsz3 hF3 hy3 hy1 hy2 hmf hsf hmo hmin
    (by omega) ?_
  intro b4 M4 img4 g4 hL4 hR4 hW4 hsz4 hF4 hout4 hfee4 hg4 hg4'
  refine rx_ex_store (R := g4 - 60000) hfork hstatic hdepth hL4 hi hj hR4 hW4 hsz4 hF4 hout4
    hfee4 hma hmap hbi hbj1 hbj2 (by omega) (by omega) ?_
  intro b5 M5 img5 g5 hL5 hR5 hW5 hsz5 hdata5 hout5 hg5 hg5'
  have hcj : ((σ.set (balancesBase + exI sevm) (B (exI sevm).toNat + D)).set
      (balancesBase + exJ sevm) (B (exJ sevm).toNat - exDyOut (X (exJ sevm).toNat) (Nat.toB256 v)
        (σ.get feeSlot) (exRate (exJ sevm).toNat) -
        exAdm (exDyFee (X (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)) (σ.get adminFeeSlot)
          (exRate (exJ sevm).toNat))).get (coinsBase + exJ sevm) = σ.get (coinsBase + exJ sevm) := by
    have hiN : balancesBase + exI sevm = balancesBase + Nat.toB256 (exI sevm).toNat := by
      rw [toB256_toNat]
    have hjN : balancesBase + exJ sevm = balancesBase + Nat.toB256 (exJ sevm).toNat := by
      rw [toB256_toNat]
    have hcN : coinsBase + exJ sevm = coinsBase + Nat.toB256 (exJ sevm).toNat := by
      rw [toB256_toNat]
    rw [Stor.get_set_ne _ (by rw [hjN, hcN]; exact bal_ne_coin hj hj),
      Stor.get_set_ne _ (by rw [hiN, hcN]; exact bal_ne_coin hi hj)]
  refine rx_ex_push hfork hstatic hdepth hL5 hL5.wc hj hR5 hW5 hsz5 hdata5 hout5 (by rw [hcj]; exact hpush)
    (by omega) (by omega) k

end Back

/-- The fee-index test (`i == FEE_INDEX`) as the runtime computes it. -/
abbrev exFeeTest (sevm : Sevm) : B256 := B256.eqCheck (B256.eqCheck (exI sevm) (Bytes.toB256 [2])) 0

theorem exFeeTest_ne {sevm : Sevm} (h : exI sevm ≠ 2) : exFeeTest sevm ≠ 0 := by
  have h1 : B256.eqCheck (exI sevm) (Bytes.toB256 [2]) = 0 :=
    if_neg (by rw [show Bytes.toB256 [2] = (2 : B256) by decide]; exact h)
  unfold exFeeTest
  rw [h1]
  decide

theorem exFeeTest_eq {sevm : Sevm} (h : exI sevm = 2) : exFeeTest sevm = 0 := by
  have h1 : B256.eqCheck (exI sevm) (Bytes.toB256 [2]) = 1 := if_pos (by rw [h]; decide)
  unfold exFeeTest
  rw [h1]
  decide

/-- The second fee test, forward: for `i ≠ FEE_INDEX` on to `x`. -/
theorem rx_ex_test2_ne {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {Q : Outcome → Prop}
    (h : exI sevm ≠ 2)
    (k : SFunc.RunEx cert.prog sevm (St b [] M G) t_26c9_c13 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M (G + 29)) t_2666_c12 Q := by
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branchTo_succ (exFeeTest_ne h) (g := t_26c9_c13) rfl ·)
  exact k

/-- The second fee test, forward: for `i == FEE_INDEX` on to the second `balanceOf`. -/
theorem rx_ex_test2_eq {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {Q : Outcome → Prop}
    (h : exI sevm = 2)
    (k : SFunc.RunEx cert.prog sevm (St b [] M G) t_2672_c12 Q) :
    SFunc.RunEx cert.prog sevm (St b [] M (G + 29)) t_2666_c12 Q := by
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branchTo_zero' (exFeeTest_eq h) ·)
  exact k

/-- The amount `exchange` credits: the fee coin's balance difference, else `dx`. -/
abbrev exCred (sevm : Sevm) (B1 B2 : B256) : B256 := if exI sevm = 2 then B2 - B1 else exDx sevm

section Frame

variable {sevm : Sevm} {pre : Devm} {s0 : State} {G U amp v : Nat} {Q : Outcome → Prop}
  {W W' : Devm → Prop} {x0 x1 x2 B1 B2 : B256}

/-- **The `exchange` frame, forward** (see the module note): `σ` is the entry storage, `X` the
`_xp_mem` words, `D = exCred` the credited amount. -/
theorem rx_ex_frame (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange) (hid : IdReady sevm pre)
    (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre)
    (ha : Abstracts (pre.getStor sevm.currentTarget) s0)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0)
    (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3)
    (hX : xpChk ⟨(balAt (pre.getStor sevm.currentTarget) 0).toNat,
      (balAt (pre.getStor sevm.currentTarget) 1).toNat,
      (balAt (pre.getStor sevm.currentTarget) 2).toNat⟩ = some ⟨x0.toNat, x1.toNat, x2.toNat⟩)
    (hbal : exI sevm = 2 →
      CoinBalOkAt sevm W W ((pre.getStor sevm.currentTarget).get (coinsBase + exI sevm)) B1 U
        0x3dc 0x440 ∧
      CoinBalOkAt sevm W' W' ((pre.getStor sevm.currentTarget).get (coinsBase + exI sevm)) B2 U
        0x71c 0x780 ∧ ¬ B2 < B1)
    (hpull : CoinPullOkAt sevm W W' ((pre.getStor sevm.currentTarget).get (coinsBase + exI sevm))
      (exDx sevm) U 0x600 0x6c0)
    (hmx : exCred sevm B1 B2 * exRate (exI sevm).toNat / exCred sevm B1 B2 =
      exRate (exI sevm).toNat ∨ exCred sevm B1 B2 = 0)
    (hax : ¬ exW3 x0 x1 x2 (exI sevm).toNat + exCred sevm B1 B2 * exRate (exI sevm).toNat / exR0 <
      exW3 x0 x1 x2 (exI sevm).toNat)
    (hA : aChk s0 sevm.benvStat.time.toNat = some amp)
    (hres : getYChk amp ⟨(exI sevm).toNat, hi⟩ ⟨(exJ sevm).toNat, hj⟩
      (exW3 x0 x1 x2 (exI sevm).toNat + exCred sevm B1 B2 * exRate (exI sevm).toNat / exR0).toNat
      (V3.mk x0.toNat x1.toNat x2.toNat).get = some v)
    (hy1 : ¬ exW3 x0 x1 x2 (exJ sevm).toNat < Nat.toB256 v)
    (hy2 : ¬ exW3 x0 x1 x2 (exJ sevm).toNat - Nat.toB256 v < Bytes.toB256 [1])
    (hmf : exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) *
        (pre.getStor sevm.currentTarget).get feeSlot /
        exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) =
        (pre.getStor sevm.currentTarget).get feeSlot ∨
      exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) = 0)
    (hsf : ¬ exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) <
      exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
        ((pre.getStor sevm.currentTarget).get feeSlot))
    (hmo : (exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) -
        exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot)) * exR0 /
        (exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) -
          exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
            ((pre.getStor sevm.currentTarget).get feeSlot)) = exR0 ∨
      exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) -
        exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot) = 0)
    (hmin : ¬ exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
      ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat) < exMinDy sevm)
    (hma : exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
        ((pre.getStor sevm.currentTarget).get feeSlot) *
        (pre.getStor sevm.currentTarget).get adminFeeSlot /
        exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot) =
        (pre.getStor sevm.currentTarget).get adminFeeSlot ∨
      exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
        ((pre.getStor sevm.currentTarget).get feeSlot) = 0)
    (hmap : exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
        ((pre.getStor sevm.currentTarget).get feeSlot))
        ((pre.getStor sevm.currentTarget).get adminFeeSlot) * exR0 /
        exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot))
          ((pre.getStor sevm.currentTarget).get adminFeeSlot) = exR0 ∨
      exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
        ((pre.getStor sevm.currentTarget).get feeSlot))
        ((pre.getStor sevm.currentTarget).get adminFeeSlot) = 0)
    (hbi : ¬ exBal (pre.getStor sevm.currentTarget) ⟨(exI sevm).toNat, hi⟩ + exCred sevm B1 B2 <
      exBal (pre.getStor sevm.currentTarget) ⟨(exI sevm).toNat, hi⟩)
    (hbj1 : ¬ exBal (pre.getStor sevm.currentTarget) ⟨(exJ sevm).toNat, hj⟩ <
      exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
        ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat))
    (hbj2 : ¬ exBal (pre.getStor sevm.currentTarget) ⟨(exJ sevm).toNat, hj⟩ -
        exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat) <
      exAdm (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
        ((pre.getStor sevm.currentTarget).get feeSlot))
        ((pre.getStor sevm.currentTarget).get adminFeeSlot) (exRate (exJ sevm).toNat))
    (hpush : CoinPushOkAt sevm W' W' ((pre.getStor sevm.currentTarget).get (coinsBase + exJ sevm))
      (exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
        ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat)) U 0xb60 0xc00)
    (hG : costGetY sevm pre amp (exI sevm).toNat (exJ sevm).toNat
      (exW3 x0 x1 x2 (exI sevm).toNat + exCred sevm B1 B2 * exRate (exI sevm).toNat / exR0).toNat
      x0.toNat x1.toNat x2.toNat + 154000 + 4 * U ≤ G) (hGb : G < 2 ^ 256)
    (k : ∀ D' : Devm, ExLive sevm W' D' (exFinal ((pre.getStor sevm.currentTarget).set lockSlot 1)
      sevm (exBal (pre.getStor sevm.currentTarget) ⟨(exI sevm).toNat, hi⟩ + exCred sevm B1 B2)
      (exBal (pre.getStor sevm.currentTarget) ⟨(exJ sevm).toNat, hj⟩ -
        exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot) (exRate (exJ sevm).toNat) -
        exAdm (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v)
          ((pre.getStor sevm.currentTarget).get feeSlot))
          ((pre.getStor sevm.currentTarget).get adminFeeSlot) (exRate (exJ sevm).toNat))) →
      Q (.halted D')) :
    SFunc.RunEx cert.prog sevm (St pre [] Mem.empty G) t_0000_c0 Q := by
  -- the entry storage with the lock set reads as the entry storage off the lock
  have ef : ((pre.getStor sevm.currentTarget).set lockSlot 1).get feeSlot =
      (pre.getStor sevm.currentTarget).get feeSlot := Stor.get_set_ne _ (by decide) _
  have eaf : ((pre.getStor sevm.currentTarget).set lockSlot 1).get adminFeeSlot =
      (pre.getStor sevm.currentTarget).get adminFeeSlot := Stor.get_set_ne _ (by decide) _
  have eci : ((pre.getStor sevm.currentTarget).set lockSlot 1).get (coinsBase + exI sevm) =
      (pre.getStor sevm.currentTarget).get (coinsBase + exI sevm) := Stor.get_set_ne _ (by
    rw [show coinsBase + exI sevm = coinsBase + Nat.toB256 (exI sevm).toNat by rw [toB256_toNat]]
    exact coin_ne_lock hi) _
  have ecj : ((pre.getStor sevm.currentTarget).set lockSlot 1).get (coinsBase + exJ sevm) =
      (pre.getStor sevm.currentTarget).get (coinsBase + exJ sevm) := Stor.get_set_ne _ (by
    rw [show coinsBase + exJ sevm = coinsBase + Nat.toB256 (exJ sevm).toNat by rw [toB256_toNat]]
    exact coin_ne_lock hj) _
  have ha1 : Abstracts ((pre.getStor sevm.currentTarget).set lockSlot 1) s0 :=
    ha.of_lock fun x hx => Stor.get_set_ne _ (Ne.symm hx) _
  obtain ⟨g0, rfl⟩ : ∃ g, G = g + 422 := ⟨G - 422, by omega⟩
  refine rx_dispatch_ex hlen hcd hsel ?_
  refine rx_ex_pre (b0 := pre) (σ := pre.getStor sevm.currentTarget) (R := g0 - 33261) hfork
    hstatic ⟨fun _ => rfl, rfl, rfl, hid⟩ hWc hWb hlock hval hkill hi hj
    (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyMem_wf Mem.wf_empty _)
    (vyMem_empty_size _) (vyImg_clamps _ _) (by omega) ?_
  intro b1 M1 img1 g1 z0 z1 z2 hB1 hW1 hR1 hWf1 hsz1 hg1 hg1'
  refine rx_ex_mid (R := g1 - 3689) hfork hB1 hWc hW1 hi hX hR1 hWf1 hsz1 (by omega) ?_
  intro b2 M2 img2 g2 x0' x1' x2' hxp hB2 hW2 hR2 hWf2 hsz2 hF2 hg2 hg2'
  obtain ⟨e0, e1, e2⟩ := V3.mk.inj hxp
  obtain rfl := B256.toNat_inj _ _ e0
  obtain rfl := B256.toNat_inj _ _ e1
  obtain rfl := B256.toNat_inj _ _ e2
  rw [eci] at hF2
  have hL2 : ExLive sevm W b2 ((pre.getStor sevm.currentTarget).set lockSlot 1) :=
    ⟨hB2.stor, hB2.id, hWc, hW2⟩
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 10 := ⟨g2 - 10, by omega⟩
  by_cases hfee : exI sevm = 2
  · -- the fee coin: `balanceOf`, the pull, `balanceOf`
    obtain ⟨hb1, hb2, hsub⟩ := hbal hfee
    have hD : exCred sevm B1 B2 = B2 - B1 := if_pos hfee
    rw [hD] at hmx hax hres hbi hG k
    xr (rx_branchTo_zero' (exFeeTest_eq hfee) ·)
    refine rx_ex_bal1 (R := g3 - 1000 - U) hL2 hR2 hWf2 hsz2 hF2 hb1 (by omega) (by omega) ?_
    intro b4 M4 img4 g4 hL4 hR4 hWf4 hsz4 hF4 hg4 hg4'
    refine rx_ex_pull (R := g4 - 4000 - U) hfork hdepth hL4 hW'c hR4 hWf4 hsz4
      (.inr ⟨rfl, rfl⟩) hF4 hpull (by omega) (by omega) ?_
    intro b5 M5 img5 g5 hL5 hR5 hWf5 hsz5 hF5 hg5 hg5'
    obtain ⟨g6, rfl⟩ : ∃ g, g5 = g + 29 := ⟨g5 - 29, by omega⟩
    refine rx_ex_test2_eq hfee ?_
    refine rx_ex_bal2 (R := g6 - 1000 - U) hL5 hR5 hWf5 hsz5 hF5 hb2 hsub (by omega) (by omega) ?_
    intro b7 M7 img7 g7 hL7 hR7 hWf7 hsz7 hF7 hg7 hg7'
    have hcy : costGetY sevm b7 amp (exI sevm).toNat (exJ sevm).toNat
        (exW3 x0 x1 x2 (exI sevm).toNat + (B2 - B1) * exRate (exI sevm).toNat / exR0).toNat
        (exW3 x0 x1 x2 0).toNat (exW3 x0 x1 x2 1).toNat (exW3 x0 x1 x2 2).toNat ≤
        costGetY sevm pre amp (exI sevm).toNat (exJ sevm).toNat
        (exW3 x0 x1 x2 (exI sevm).toNat + (B2 - B1) * exRate (exI sevm).toNat / exR0).toNat
        x0.toNat x1.toNat x2.toNat + 8858 := costGetY_le _ _ _ _ _ _ _ _ _ _
    exact rx_ex_back hfork hstatic hdepth hL7 ha1 hi hj hR7 hWf7 hsz7 (.inr ⟨rfl, rfl⟩) hF7 hmx hax
      hA hres hy1 hy2 (by rw [ef]; exact hmf) (by rw [ef]; exact hsf) (by rw [ef]; exact hmo)
      (by rw [ef]; exact hmin) (by rw [ef, eaf]; exact hma) (by rw [ef, eaf]; exact hmap) hbi
      (by rw [ef]; exact hbj1) (by rw [ef, eaf]; exact hbj2) (by rw [ef, ecj]; exact hpush)
      (by omega) (by omega) (by rw [ef, eaf]; exact k)
  · -- another coin: the pull alone
    have hD : exCred sevm B1 B2 = exDx sevm := if_neg hfee
    rw [hD] at hmx hax hres hbi hG k
    xr (rx_branchTo_succ (exFeeTest_ne hfee) (g := t_2517_c11) rfl ·)
    refine rx_ex_pull (R := g3 - 4000 - U) hfork hdepth hL2 hW'c hR2 hWf2 hsz2
      (.inl ⟨rfl, rfl⟩) hF2 hpull (by omega) (by omega) ?_
    intro b5 M5 img5 g5 hL5 hR5 hWf5 hsz5 hF5 hg5 hg5'
    obtain ⟨g6, rfl⟩ : ∃ g, g5 = g + 29 := ⟨g5 - 29, by omega⟩
    refine rx_ex_test2_ne hfee ?_
    have hcy : costGetY sevm b5 amp (exI sevm).toNat (exJ sevm).toNat
        (exW3 x0 x1 x2 (exI sevm).toNat + exDx sevm * exRate (exI sevm).toNat / exR0).toNat
        (exW3 x0 x1 x2 0).toNat (exW3 x0 x1 x2 1).toNat (exW3 x0 x1 x2 2).toNat ≤
        costGetY sevm pre amp (exI sevm).toNat (exJ sevm).toNat
        (exW3 x0 x1 x2 (exI sevm).toNat + exDx sevm * exRate (exI sevm).toNat / exR0).toNat
        x0.toNat x1.toNat x2.toNat + 8858 := costGetY_le _ _ _ _ _ _ _ _ _ _
    exact rx_ex_back hfork hstatic hdepth hL5 ha1 hi hj hR5 hWf5 hsz5 (.inl ⟨rfl, rfl⟩) hF5 hmx hax
      hA hres hy1 hy2 (by rw [ef]; exact hmf) (by rw [ef]; exact hsf) (by rw [ef]; exact hmo)
      (by rw [ef]; exact hmin) (by rw [ef, eaf]; exact hma) (by rw [ef, eaf]; exact hmap) hbi
      (by rw [ef]; exact hbj1) (by rw [ef, eaf]; exact hbj2) (by rw [ef, ecj]; exact hpush)
      (by omega) (by omega) (by rw [ef, eaf]; exact k)

end Frame

end Blanc.Lift.Curve3Pool
