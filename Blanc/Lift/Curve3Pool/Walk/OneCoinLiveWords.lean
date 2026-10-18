import Blanc.Lift.Curve3Pool.Walk.OneCoinLiveModel

/-!
# `remove_liquidity_one_coin`, forward: the machine-word checks from the model's step

`oc_words` turns a successful model `remove_liquidity_one_coin` (inverted by
`removeLiquidityOneCoin_inv` and `calcWithdrawOne_inv`) into the word facts `rx_oc_frame` takes,
with the model's numbers as their values. `costOneCoin` is the closed sufficient-gas bound of
the frame: `get_D`'s and the two `get_y_D`s' gas at the model's arguments plus a constant.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **`remove_liquidity_one_coin`'s sufficient gas** (without the callee allowances `3 U`):
`get_D(xp, amp)`, `get_y_D(amp, i, xp, D1)` and `get_y_D(amp, i, xp_reduced, D1)` at the model's
arguments, and the frame's own instructions, storage accesses and `_A`'s worst case. `0` past a
model revert. -/
def costOneCoin (s : State) (e : Env) (amount : Nat) (i : Fin 3) : Nat :=
  (do
    let amp ← aChk s e.time
    let F ← feeAdj s
    let T ← e.supply
    let xp ← xpChk s.balances
    let D0 ← getDChk xp.get amp 1
    let D1 := D0 - amount * D0 / T
    let newY ← getYDChk amp i xp.get D1
    let red ← V3.ofFnM fun k => do
      let scaled ← chkDiv (← chkMul (xp.get k) D1) D0
      let dxExp ← if k = i then chkSub scaled newY else chkSub (xp.get k) scaled
      chkSub (xp.get k) (← chkDiv (← chkMul F dxExp) feeDen)
    some (costGetD xp.v0 xp.v1 xp.v2 amp + costGetYD amp i.val xp.v0 xp.v1 xp.v2 D1 +
      costGetYD amp i.val red.v0 red.v1 red.v2 D1 + 131000)).getD 0

theorem chkSub_eq' {a b z : Nat} (h : chkSub a b = some z) : z = a - b := by
  unfold chkSub at h
  split at h
  · cases h; rfl
  · cases h

theorem mulEq_of_nofm {x y : B256} (h : B256.Nofm x y) : x * y / x = y ∨ x = 0 := by
  by_cases hx : x = 0
  · exact .inr hx
  · refine .inl (B256.toNat_inj _ _ ?_)
    rw [B256.toNat_div hx, B256.toNat_mul_eq_of_nofm h,
      Nat.mul_div_cancel_left _ (B256.toNat_pos hx)]

theorem cw_ofFnM_parts {f : Fin 3 → Option Nat} {v : V3} (h : V3.ofFnM f = some v) :
    f 0 = some v.v0 ∧ f 1 = some v.v1 ∧ f 2 = some v.v2 := by
  unfold V3.ofFnM at h
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨ha, hb, hc⟩

section Words

variable {sevm : Sevm} {σ : Stor} {s : State} {i : Fin 3} {T : B256} {o : Out}

/-- **The model's `remove_liquidity_one_coin`, as the frame's words**: `x_k` are `_xp`'s words,
`D0`, `y`, `r_k` (`xp_reduced`), `y2` the checked results, with the frame's word checks and the
model's output in those words. -/
theorem oc_words (ha : Abstracts σ s) (hi : i.val = (ocI sevm).toNat)
    (hrl : removeLiquidityOneCoin s (ocEnv sevm i T.toNat) (ocAmt sevm).toNat i
      (ocMin sevm).toNat = some o) :
    ∃ (amp : Nat) (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) (hi3 : (ocI sevm).toNat < 3),
      s.isKilled = false ∧ aChk s sevm.benvStat.time.toNat = some amp ∧
      (σ.get feeSlot * Bytes.toB256 [0x03] / σ.get feeSlot = Bytes.toB256 [0x03] ∨
        σ.get feeSlot = 0) ∧
      xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1 = some D0.toNat ∧
      (ocAmt sevm * D0 / ocAmt sevm = D0 ∨ ocAmt sevm = 0) ∧ T ≠ 0 ∧
      ¬ D0 < ocAmt sevm * D0 / T ∧
      getYDChk amp ⟨(ocI sevm).toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
        (D0 - ocAmt sevm * D0 / T).toNat = some y.toNat ∧
      ¬ pickWord3 (ocI sevm).toNat x0 x1 x2 < y ∧
      CwStep (Bytes.toB256 [0] = ocI sevm) x0 (D0 - ocAmt sevm * D0 / T) D0 y
        (cwFee (σ.get feeSlot)) x0 r0 ∧
      CwStep (Bytes.toB256 [1] = ocI sevm) x1 (D0 - ocAmt sevm * D0 / T) D0 y
        (cwFee (σ.get feeSlot)) x1 r1 ∧
      CwStep (Bytes.toB256 [2] = ocI sevm) x2 (D0 - ocAmt sevm * D0 / T) D0 y
        (cwFee (σ.get feeSlot)) x2 r2 ∧
      getYDChk amp ⟨(ocI sevm).toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
        (D0 - ocAmt sevm * D0 / T).toNat = some y2.toNat ∧
      ¬ pickWord3 (ocI sevm).toNat r0 r1 r2 < y2 ∧
      ¬ pickWord3 (ocI sevm).toNat r0 r1 r2 - y2 < Bytes.toB256 [1] ∧
      ¬ (pickWord3 (ocI sevm).toNat x0 x1 x2 - y) /
        pickWord3 (ocI sevm).toNat cwP1 cwPm cwPm < cwDy (ocI sevm) r0 r1 r2 y2 ∧
      ¬ cwDy (ocI sevm) r0 r1 r2 y2 < ocMin sevm ∧
      B256.Nofm ((pickWord3 (ocI sevm).toNat x0 x1 x2 - y) /
        pickWord3 (ocI sevm).toNat cwP1 cwPm cwPm - cwDy (ocI sevm) r0 r1 r2 y2)
        (σ.get adminFeeSlot) ∧
      ¬ cwDy (ocI sevm) r0 r1 r2 y2 + ((pickWord3 (ocI sevm).toNat x0 x1 x2 - y) /
        pickWord3 (ocI sevm).toNat cwP1 cwPm cwPm - cwDy (ocI sevm) r0 r1 r2 y2) *
        σ.get adminFeeSlot / ocDen < cwDy (ocI sevm) r0 r1 r2 y2 ∧
      ¬ σ.get (balancesBase + ocI sevm) <
        cwDy (ocI sevm) r0 r1 r2 y2 + ((pickWord3 (ocI sevm).toNat x0 x1 x2 - y) /
          pickWord3 (ocI sevm).toNat cwP1 cwPm cwPm - cwDy (ocI sevm) r0 r1 r2 y2) *
          σ.get adminFeeSlot / ocDen ∧
      o = ⟨{ s with balances := (s.balances.set ⟨(ocI sevm).toNat, hi3⟩
          (ocBal σ (ocI sevm) (cwDy (ocI sevm) r0 r1 r2 y2)
            ((pickWord3 (ocI sevm).toNat x0 x1 x2 - y) /
              pickWord3 (ocI sevm).toNat cwP1 cwPm cwPm - cwDy (ocI sevm) r0 r1 r2 y2)).toNat) },
        none, [.removeLiquidityOne sevm.caller.toB256.toNat (ocAmt sevm).toNat
          (cwDy (ocI sevm) r0 r1 r2 y2).toNat],
        [.burn sevm.caller.toB256.toNat (ocAmt sevm).toNat,
          .push ⟨(ocI sevm).toNat, hi3⟩ sevm.caller.toB256.toNat (cwDy (ocI sevm) r0 r1 r2 y2).toNat]⟩ ∧
      costOneCoin s (ocEnv sevm i T.toNat) (ocAmt sevm).toNat i =
        costGetD x0.toNat x1.toNat x2.toNat amp +
        costGetYD amp (ocI sevm).toNat x0.toNat x1.toNat x2.toNat
          (D0 - ocAmt sevm * D0 / T).toNat +
        costGetYD amp (ocI sevm).toNat r0.toNat r1.toNat r2.toNat
          (D0 - ocAmt sevm * D0 / T).toNat + 131000 := by
  obtain ⟨hk, dy, fee, p, q, take, bi, hcw, hmin, hp, hq, htake, hbi, -, -, ho⟩ :=
    removeLiquidityOneCoin_inv hrl
  obtain ⟨amp, F, Tn, xp, D0n, m, qd, D1n, newY, d, dy0, red, y2n, e1, e2, hamp, hF, hT, hxp,
    hD0, hm, hqd, hD1, hnewY, hd, hdy0, hred, hy2, he1, he2, hdy, hfee⟩ := calcWithdrawOne_inv hcw
  have hi3 : (ocI sevm).toNat < 3 := hi ▸ i.isLt
  obtain rfl : i = ⟨(ocI sevm).toNat, hi3⟩ := Fin.ext hi
  -- the supply
  have hTn : Tn = T.toNat := (Option.some.inj hT).symm
  subst hTn
  have hD1e : D1n = D0n - (ocAmt sevm).toNat * D0n / T.toNat := by
    rw [chkSub_eq' hD1, ex_chkDiv_eq hqd, ex_chkMul_eq hm]
  have hred0 := hred
  -- the adjusted fee
  have hF0 := hF
  unfold feeAdj at hF
  obtain ⟨pf, hpf, hF⟩ := Option.bind_eq_some_iff.mp hF
  rw [← ha.fee, show (3 : Nat) = (Bytes.toB256 [0x03]).toNat by decide] at hpf
  obtain ⟨hmfn, rfl⟩ := chkMul_inv hpf
  rw [show (8 : Nat) = (Bytes.toB256 [0x08]).toNat by decide] at hF
  obtain ⟨-, rfl⟩ := chkDiv_word hF
  -- `xp` as words
  obtain ⟨⟨p0, hm0, hd0⟩, ⟨p1, hm1, hd1⟩, ⟨p2, hm2, hd2⟩⟩ := xpChk_some_parts hxp
  have hx0 := ex_chkMulDiv_lt hm0 hd0
  have hx1 := ex_chkMulDiv_lt hm1 hd1
  have hx2 := ex_chkMulDiv_lt hm2 hd2
  clear hm0 hd0 hm1 hd1 hm2 hd2
  obtain ⟨v0, v1, v2⟩ := xp
  obtain ⟨x0, rfl⟩ : ∃ w : B256, w.toNat = v0 := ⟨_, B256.toNat_toB256_of_lt hx0⟩
  obtain ⟨x1, rfl⟩ : ∃ w : B256, w.toNat = v1 := ⟨_, B256.toNat_toB256_of_lt hx1⟩
  obtain ⟨x2, rfl⟩ : ∃ w : B256, w.toNat = v2 := ⟨_, B256.toNat_toB256_of_lt hx2⟩
  -- `D0`, `D1`
  obtain ⟨D0, rfl⟩ : ∃ w : B256, w.toNat = D0n := ⟨_, B256.toNat_toB256_of_lt (getDChk_lt hD0)⟩
  obtain ⟨hmo, rfl⟩ := chkMul_inv hm
  obtain ⟨hT0, rfl⟩ := chkDiv_word hqd
  obtain ⟨hle, rfl⟩ := chkSub_word hD1
  -- `new_y`, `dy_0`
  obtain ⟨y, rfl⟩ : ∃ w : B256, w.toNat = newY :=
    ⟨_, B256.toNat_toB256_of_lt (getYDChk_lt (B256.toNat_lt _) hnewY)⟩
  rw [← dy_pickWord3_toNat hi3] at hd
  obtain ⟨hyl, rfl⟩ := chkSub_word hd
  rw [← cw_precMul_toNat hi3] at hdy0
  obtain ⟨-, rfl⟩ := chkDiv_word hdy0
  -- the fee loop
  obtain ⟨hr0, hr1, hr2⟩ := cw_ofFnM_parts hred
  obtain ⟨h0, hb0⟩ := cwStep_of_chk (xk := x0) (D1 := D0 - ocAmt sevm * D0 / T) (D0 := D0) (y := y)
    (F := cwFee (σ.get feeSlot)) (cw_eq_iff (w := Bytes.toB256 [0]) (k := 0) hi3 (by decide)) hr0
  obtain ⟨h1, hb1⟩ := cwStep_of_chk (xk := x1) (D1 := D0 - ocAmt sevm * D0 / T) (D0 := D0) (y := y)
    (F := cwFee (σ.get feeSlot)) (cw_eq_iff (w := Bytes.toB256 [1]) (k := 1) hi3 (by decide)) hr1
  obtain ⟨h2, hb2⟩ := cwStep_of_chk (xk := x2) (D1 := D0 - ocAmt sevm * D0 / T) (D0 := D0) (y := y)
    (F := cwFee (σ.get feeSlot)) (cw_eq_iff (w := Bytes.toB256 [2]) (k := 2) hi3 (by decide)) hr2
  obtain ⟨u0, u1, u2⟩ := red
  obtain ⟨r0, rfl⟩ : ∃ w : B256, w.toNat = u0 := ⟨_, B256.toNat_toB256_of_lt hb0⟩
  obtain ⟨r1, rfl⟩ : ∃ w : B256, w.toNat = u1 := ⟨_, B256.toNat_toB256_of_lt hb1⟩
  obtain ⟨r2, rfl⟩ : ∃ w : B256, w.toNat = u2 := ⟨_, B256.toNat_toB256_of_lt hb2⟩
  simp only [toB256_toNat] at h0 h1 h2
  -- the second `get_y_D`, `dy`, the fee
  obtain ⟨y2, rfl⟩ : ∃ w : B256, w.toNat = y2n :=
    ⟨_, B256.toNat_toB256_of_lt (getYDChk_lt (B256.toNat_lt _) hy2)⟩
  rw [← dy_pickWord3_toNat hi3] at he1
  obtain ⟨hs0, rfl⟩ := chkSub_word he1
  rw [show (1 : Nat) = (Bytes.toB256 [1]).toNat by decide] at he2
  obtain ⟨hs1, rfl⟩ := chkSub_word he2
  rw [← cw_precMul_toNat hi3] at hdy
  obtain ⟨-, rfl⟩ := chkDiv_word hdy
  obtain ⟨hs2, rfl⟩ := chkSub_word hfee
  -- the balance store
  rw [← ha.adminFee] at hp
  obtain ⟨hma, rfl⟩ := chkMul_inv hp
  rw [show feeDen = ocDen.toNat by decide] at hq
  obtain ⟨-, rfl⟩ := chkDiv_word hq
  obtain ⟨hadd, rfl⟩ := chkAdd_inv htake
  rw [← ha.balances, show balanceSlot ⟨(ocI sevm).toNat, hi3⟩ = balancesBase + ocI sevm by
    rw [balanceSlot]; exact congrArg _ (toB256_toNat _)] at hbi
  obtain ⟨hsub, rfl⟩ := chkSub_word hbi
  refine ⟨amp, x0, x1, x2, D0, y, r0, r1, r2, y2, hi3, hk, hamp, mulEq_of_nofm hmfn, hxp, hD0,
    mulEq_of_nofm hmo, hT0, fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hle),
    hnewY, fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hyl), h0, h1, h2, hy2,
    fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hs0),
    fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hs1),
    fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hs2),
    fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hmin), hma,
    (B256.nof_iff_not_add_lt _ _).mp hadd,
    fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hsub), ho, ?_⟩
  -- the cost
  unfold costOneCoin
  rw [hamp, hF0]
  simp only [cw_some_bind, show (ocEnv sevm ⟨(ocI sevm).toNat, hi3⟩ T.toNat).supply = some T.toNat
    from rfl, hxp, hD0]
  rw [← hD1e]
  simp only [hnewY, cw_some_bind, hred, Option.getD_some]

end Words

end Blanc.Lift.Curve3Pool
