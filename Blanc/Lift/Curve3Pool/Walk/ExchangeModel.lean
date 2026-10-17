import Blanc.Lift.Curve3Pool.Walk.Exchange

/-! # The checked exchange arithmetic as model operations -/
namespace Blanc.Lift.Curve3Pool
open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- Each successful checked operation in `exchange`, in source order. -/
theorem ex_model_eq {s : State} {e : Env} {i j : Fin 3}
    {dx minDy D X Y dy fee out adm0 adm bi bj amp : Nat} {xp : V3}
    (hk : s.isKilled = false) (hxp : xpChk s.balances = some xp)
    (hpull : pullIn e i dx = some D)
    (hmx : chkMul D (rates.get i) = some X)
    (hdx : chkDiv X precision = some Y)
    {x y dy1 dfp dop afp aop : Nat}
    (hax : chkAdd (xp.get i) Y = some x)
    (ha : aChk s e.time = some amp) (hy : getYChk amp i j x xp.get = some y)
    (hsub1 : chkSub (xp.get j) y = some dy1) (hsub2 : chkSub dy1 1 = some dy)
    (hmf : chkMul dy s.fee = some dfp) (hdf : chkDiv dfp feeDen = some fee)
    (hsf : chkSub dy fee = some dop)
    {outp : Nat} (hmo : chkMul dop precision = some outp)
    (hdo : chkDiv outp (rates.get j) = some out) (hmin : minDy ≤ out)
    (hma : chkMul fee s.adminFee = some afp) (hda : chkDiv afp feeDen = some adm0)
    (hmap : chkMul adm0 precision = some aop)
    (hdap : chkDiv aop (rates.get j) = some adm)
    (hbi : chkAdd (s.balances.get i) D = some bi)
    {bj1 : Nat} (hbj1 : chkSub (s.balances.get j) out = some bj1)
    (hbj2 : chkSub bj1 adm = some bj) (hpush : (e.coin j).pushOk = true) :
    exchange s e i j dx minDy = some
      ⟨{s with balances := (s.balances.set i bi).set j bj}, none,
        [.tokenExchange e.caller i.val dx j.val out],
        [.pull i e.caller dx, .push j e.caller out]⟩ := by
  have rk : req (s.isKilled = false) = some () := by unfold req; rw [ite_eq_left hk]
  have rmin : req (out ≥ minDy) = some () := by unfold req; rw [ite_eq_left hmin]
  have rpush : req ((e.coin j).pushOk = true) = some () := by
    unfold req; rw [ite_eq_left hpush]
  unfold exchange
  rw [rk, Option.bind_eq_bind, Option.bind_some]
  change (xpChk s.balances).bind _ = _
  rw [hxp, Option.bind_some]
  change (pullIn e i dx).bind _ = _
  rw [hpull, Option.bind_some]
  change (chkMul D (rates.get i)).bind _ = _
  rw [hmx, Option.bind_some]
  change (chkDiv X precision).bind _ = _
  rw [hdx, Option.bind_some]
  change (chkAdd (xp.get i) Y).bind _ = _
  rw [hax, Option.bind_some]
  change (aChk s e.time).bind _ = _
  rw [ha, Option.bind_some]
  change (getYChk amp i j x xp.get).bind _ = _
  rw [hy, Option.bind_some]
  change (chkSub (xp.get j) y).bind _ = _
  rw [hsub1, Option.bind_some]
  change (chkSub dy1 1).bind _ = _
  rw [hsub2, Option.bind_some]
  change (chkMul dy s.fee).bind _ = _
  rw [hmf, Option.bind_some]
  change (chkDiv dfp feeDen).bind _ = _
  rw [hdf, Option.bind_some]
  change (chkSub dy fee).bind _ = _
  rw [hsf, Option.bind_some]
  change (chkMul dop precision).bind _ = _
  rw [hmo, Option.bind_some]
  change (chkDiv outp (rates.get j)).bind _ = _
  rw [hdo, Option.bind_some]
  rw [rmin, Option.bind_some]
  change (chkMul fee s.adminFee).bind _ = _
  rw [hma, Option.bind_some]
  change (chkDiv afp feeDen).bind _ = _
  rw [hda, Option.bind_some]
  change (chkMul adm0 precision).bind _ = _
  rw [hmap, Option.bind_some]
  change (chkDiv aop (rates.get j)).bind _ = _
  rw [hdap, Option.bind_some]
  change (chkAdd (s.balances.get i) D).bind _ = _
  rw [hbi, Option.bind_some]
  change (chkSub (s.balances.get j) out).bind _ = _
  rw [hbj1, Option.bind_some]
  change (chkSub bj1 adm).bind _ = _
  rw [hbj2, Option.bind_some]
  rw [rpush, Option.bind_some]

/-- The selected machine rate is the model's rate. -/
theorem ex_rate_nat (k : Fin 3) : (exRate k.val).toNat = rates.get k := by
  match k with
  | 0 => decide
  | 1 => decide
  | 2 => decide

/-- The saved three-word image agrees with the model vector. -/
theorem ex_w3_nat (a b c : B256) (k : Fin 3) :
    (exW3 a b c k.val).toNat = (V3.mk a.toNat b.toNat c.toNat).get k := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

/-- The saved balance image agrees with the abstract state. -/
theorem ex_bal_nat {σ : Stor} {s : State} (h : Abstracts σ s) (k : Fin 3) :
    (exW3 (balAt σ 0) (balAt σ 1) (balAt σ 2) k.val).toNat = s.balances.get k := by
  match k with
  | 0 => exact h.balances 0
  | 1 => exact h.balances 1
  | 2 => exact h.balances 2

/-- The machine's saved balance word. -/
abbrev exBal (σ : Stor) (k : Fin 3) : B256 :=
  exW3 (balAt σ 0) (balAt σ 1) (balAt σ 2) k.val

/-- The exchange checks imply the model result, with the very same stored words. -/
theorem ex_model_words {s : State} {e : Env} {i j : Fin 3} {σ : Stor}
    {x0 x1 x2 D y : B256} {amp dx minDy : Nat}
    (ha : Abstracts σ s) (hk : s.isKilled = false)
    (hxp : xpChk s.balances = some ⟨x0.toNat,x1.toNat,x2.toNat⟩)
    (hpull : pullIn e i dx = some D.toNat)
    (hmx : D * exRate i.val / D = exRate i.val ∨ D = 0)
    (hax : ¬ exW3 x0 x1 x2 i.val + D * exRate i.val / exR0 < exW3 x0 x1 x2 i.val)
    (hamp : aChk s e.time = some amp)
    (hy : getYChk amp i j (exW3 x0 x1 x2 i.val + D * exRate i.val / exR0).toNat
      (V3.mk x0.toNat x1.toNat x2.toNat).get = some y.toNat)
    (hy1 : ¬ exW3 x0 x1 x2 j.val < y)
    (hy2 : ¬ exW3 x0 x1 x2 j.val - y < Bytes.toB256 [1])
    (hmf : exDy0 (exW3 x0 x1 x2 j.val) y * σ.get feeSlot /
      exDy0 (exW3 x0 x1 x2 j.val) y = σ.get feeSlot ∨ exDy0 (exW3 x0 x1 x2 j.val) y = 0)
    (hsf : ¬ exDy0 (exW3 x0 x1 x2 j.val) y < exDyFee (exW3 x0 x1 x2 j.val) y (σ.get feeSlot))
    (hmo : (exDy0 (exW3 x0 x1 x2 j.val) y - exDyFee (exW3 x0 x1 x2 j.val) y (σ.get feeSlot)) *
      exR0 / (exDy0 (exW3 x0 x1 x2 j.val) y - exDyFee (exW3 x0 x1 x2 j.val) y (σ.get feeSlot)) =
        exR0 ∨ exDy0 (exW3 x0 x1 x2 j.val) y - exDyFee (exW3 x0 x1 x2 j.val) y (σ.get feeSlot) = 0)
    (hmin : minDy ≤ (exDyOut (exW3 x0 x1 x2 j.val) y (σ.get feeSlot) (exRate j.val)).toNat)
    (hma : exDyFee (exW3 x0 x1 x2 j.val) y (σ.get feeSlot) * σ.get adminFeeSlot /
      exDyFee (exW3 x0 x1 x2 j.val) y (σ.get feeSlot) = σ.get adminFeeSlot ∨
      exDyFee (exW3 x0 x1 x2 j.val) y (σ.get feeSlot) = 0)
    (hmap : exAdm0 (exDyFee (exW3 x0 x1 x2 j.val) y (σ.get feeSlot)) (σ.get adminFeeSlot) * exR0 /
      exAdm0 (exDyFee (exW3 x0 x1 x2 j.val) y (σ.get feeSlot)) (σ.get adminFeeSlot) = exR0 ∨
      exAdm0 (exDyFee (exW3 x0 x1 x2 j.val) y (σ.get feeSlot)) (σ.get adminFeeSlot) = 0)
    (hbi : ¬ exBal σ i + D < exBal σ i)
    (hbj1 : ¬ exBal σ j < exDyOut (exW3 x0 x1 x2 j.val) y (σ.get feeSlot) (exRate j.val))
    (hbj2 : ¬ exBal σ j - exDyOut (exW3 x0 x1 x2 j.val) y (σ.get feeSlot) (exRate j.val) <
      exAdm (exDyFee (exW3 x0 x1 x2 j.val) y (σ.get feeSlot)) (σ.get adminFeeSlot) (exRate j.val))
    (hpush : (e.coin j).pushOk = true) :
    exchange s e i j dx minDy = some
      ⟨{s with balances := ((s.balances.set i (exBal σ i + D).toNat).set j
        (exBal σ j - exDyOut (exW3 x0 x1 x2 j.val) y (σ.get feeSlot) (exRate j.val) -
          exAdm (exDyFee (exW3 x0 x1 x2 j.val) y (σ.get feeSlot)) (σ.get adminFeeSlot)
            (exRate j.val)).toNat)}, none,
        [.tokenExchange e.caller i.val dx j.val
          (exDyOut (exW3 x0 x1 x2 j.val) y (σ.get feeSlot) (exRate j.val)).toNat],
        [.pull i e.caller dx, .push j e.caller
          (exDyOut (exW3 x0 x1 x2 j.val) y (σ.get feeSlot) (exRate j.val)).toNat]⟩ := by
  have hp : exR0.toNat = precision := by decide
  have hd : exFeeDen.toNat = feeDen := by decide
  have h1 : (Bytes.toB256 [1]).toNat = 1 := by decide
  apply ex_model_eq hk hxp hpull
  · simpa only [← ex_rate_nat i] using chkMul_toNat_of_nofm (B256.nofm_of_mulGuard hmx)
  · simpa only [← hp] using chkDiv_toNat_of_ne (x := D * exRate i.val)
      (y := exR0) (by decide)
  · simpa only [← ex_w3_nat x0 x1 x2 i] using
      chkAdd_toNat_of_lt ((B256.nof_iff_not_add_lt _ _).mpr hax)
  · exact hamp
  · exact hy
  · simpa only [← ex_w3_nat x0 x1 x2 j] using chkSub_toNat_of_le (toNat_le_of_not_lt hy1)
  · simpa only [← h1] using chkSub_toNat_of_le (toNat_le_of_not_lt hy2)
  · simpa only [← ha.fee] using chkMul_toNat_of_nofm (B256.nofm_of_mulGuard hmf)
  · simpa only [← hd] using chkDiv_toNat_of_ne
      (x := exDy0 (exW3 x0 x1 x2 j.val) y * σ.get feeSlot) (y := exFeeDen) (by decide)
  · exact chkSub_toNat_of_le (toNat_le_of_not_lt hsf)
  · simpa only [← hp] using chkMul_toNat_of_nofm (B256.nofm_of_mulGuard hmo)
  · simpa only [← ex_rate_nat j] using chkDiv_toNat_of_ne
      (x := (exDy0 (exW3 x0 x1 x2 j.val) y - exDyFee (exW3 x0 x1 x2 j.val) y (σ.get feeSlot)) * exR0)
      (exRate_ne (k := j.val))
  · exact hmin
  · simpa only [← ha.adminFee] using chkMul_toNat_of_nofm (B256.nofm_of_mulGuard hma)
  · simpa only [← hd] using chkDiv_toNat_of_ne
      (x := exDyFee (exW3 x0 x1 x2 j.val) y (σ.get feeSlot) * σ.get adminFeeSlot)
      (y := exFeeDen) (by decide)
  · simpa only [← hp] using chkMul_toNat_of_nofm (B256.nofm_of_mulGuard hmap)
  · simpa only [← ex_rate_nat j] using chkDiv_toNat_of_ne
      (x := exAdm0 (exDyFee (exW3 x0 x1 x2 j.val) y (σ.get feeSlot)) (σ.get adminFeeSlot) * exR0)
      (exRate_ne (k := j.val))
  · simpa only [← ex_bal_nat ha i] using
      chkAdd_toNat_of_lt ((B256.nof_iff_not_add_lt _ _).mpr hbi)
  · simpa only [← ex_bal_nat ha j] using chkSub_toNat_of_le (toNat_le_of_not_lt hbj1)
  · exact chkSub_toNat_of_le (toNat_le_of_not_lt hbj2)
  · exact hpush

end Blanc.Lift.Curve3Pool
