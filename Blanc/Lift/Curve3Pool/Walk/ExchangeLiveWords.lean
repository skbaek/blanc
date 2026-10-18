import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveFrame
import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveModel
import Blanc.Lift.Curve3Pool.U3Bounds

/-!
# `exchange`, forward: the machine-word checks from the model's step

`ex_words` turns a successful model `exchange` (inverted by `exchange_inv`) into the machine-word
facts `rx_ex_frame` takes: each checked operation's guard passes, on the words the frame computes,
with the model's numbers as their values. `costExchange` is `exchange`'s closed sufficient-gas
bound.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem ex_sub_of {x y : B256} {z : Nat} (h : chkSub x.toNat y.toNat = some z) :
    ¬ x < y ∧ (x - y).toNat = z :=
  let ⟨g, v⟩ := fwdChkSub h
  ⟨ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq g), v⟩

theorem ex_add_of {x y : B256} {z : Nat} (h : chkAdd x.toNat y.toNat = some z) :
    ¬ x + y < x ∧ (x + y).toNat = z :=
  let ⟨g, v⟩ := fwdChkAdd h
  ⟨ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq g), v⟩

theorem ex_mul_of {x y : B256} {z : Nat} (h : chkMul x.toNat y.toNat = some z) :
    (x * y / x = y ∨ x = 0) ∧ (x * y).toNat = z :=
  let ⟨g, v⟩ := fwdChkMul h
  ⟨(or_ne_zero g).imp eqCheck_ne_zero_eq eqCheck_ne_zero_eq, v⟩

theorem ex_div_of {x y : B256} {z : Nat} (h : chkDiv x.toNat y.toNat = some z) :
    (x / y).toNat = z :=
  (fwdChkDiv h).2

theorem ex_chkMulDiv_lt {a b p c z : Nat} (hm : chkMul a b = some p) (hd : chkDiv p c = some z) :
    z < 2 ^ 256 := by
  unfold chkMul wordSize at hm
  unfold chkDiv at hd
  split at hm
  · cases hm
    split at hd
    · cases hd
    · cases hd
      exact lt_of_le_of_lt (Nat.div_le_self _ _) (by assumption)
  · cases hm

theorem ex_chkSub_le {a b z : Nat} (h : chkSub a b = some z) : b ≤ a := by
  unfold chkSub at h
  split at h
  · assumption
  · cases h

theorem ex_chkAdd_eq {a b z : Nat} (h : chkAdd a b = some z) : z = a + b := by
  unfold chkAdd at h
  split at h
  · cases h; rfl
  · cases h

theorem ex_chkMul_eq {a b z : Nat} (h : chkMul a b = some z) : z = a * b := by
  unfold chkMul at h
  split at h
  · cases h; rfl
  · cases h

theorem ex_chkDiv_eq {a b z : Nat} (h : chkDiv a b = some z) : z = a / b := by
  unfold chkDiv at h
  split at h
  · cases h
  · cases h; rfl

/-- The fee coin's answer as the model's optional reading (none for another coin). -/
def exBalOpt (i : Fin 3) (B : B256) : Option Nat := if i = feeIndex then some B.toNat else none

/-- The amount `exchange` pushes, read off the model's call list. -/
def exPushAmt (o : Out) : Nat :=
  match o.calls with
  | [_, .push _ _ a] => a
  | _ => 0

/-- **`exchange`'s sufficient gas** at the entry base `pre`: `get_y`'s `costGetY` at the model's
`amp`, `x` and `xp`, `_A`'s worst-case slack, and the frame's own instructions and storage
accesses (each `SLOAD`/`SSTORE` at its cold price). `0` past a model revert. -/
def costExchange (sevm : Sevm) (pre : Devm) (s : State) (e : Env) (i j : Fin 3) (dx : Nat) : Nat :=
  match xpChk s.balances, pullIn e i dx, aChk s e.time with
  | some xp, some D, some amp =>
    costGetY sevm pre amp i.val j.val (xp.get i + D * rates.get i / precision) xp.v0 xp.v1 xp.v2 +
      8858 + 154000
  | _, _, _ => 0

section Words

variable {sevm : Sevm} {σ : Stor} {s : State} {i j : Fin 3} {B1 B2 : B256} {o : Out}

/-- **The model's `exchange`, as the frame's words** (see the module note): `x_k` are `_xp_mem`'s
words, `v` is `get_y`'s answer, `D = exCred` the credited amount. -/
theorem ex_words (ha : Abstracts σ s) (hi : i.val = (exI sevm).toNat)
    (hj : j.val = (exJ sevm).toNat)
    (hex : exchange s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i j (exDx sevm).toNat
      (exMinDy sevm).toNat = some o) :
    ∃ (x0 x1 x2 : B256) (amp v : Nat) (hi3 : (exI sevm).toNat < 3) (hj3 : (exJ sevm).toNat < 3),
      s.isKilled = false ∧
      xpChk ⟨(balAt σ 0).toNat, (balAt σ 1).toNat, (balAt σ 2).toNat⟩ =
        some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      (exI sevm = 2 → ¬ B2 < B1) ∧
      (exCred sevm B1 B2 * exRate (exI sevm).toNat / exCred sevm B1 B2 =
        exRate (exI sevm).toNat ∨ exCred sevm B1 B2 = 0) ∧
      ¬ exW3 x0 x1 x2 (exI sevm).toNat + exCred sevm B1 B2 * exRate (exI sevm).toNat / exR0 <
        exW3 x0 x1 x2 (exI sevm).toNat ∧
      aChk s sevm.benvStat.time.toNat = some amp ∧
      getYChk amp ⟨(exI sevm).toNat, hi3⟩ ⟨(exJ sevm).toNat, hj3⟩
        (exW3 x0 x1 x2 (exI sevm).toNat + exCred sevm B1 B2 * exRate (exI sevm).toNat /
          exR0).toNat (V3.mk x0.toNat x1.toNat x2.toNat).get = some v ∧
      ¬ exW3 x0 x1 x2 (exJ sevm).toNat < Nat.toB256 v ∧
      ¬ exW3 x0 x1 x2 (exJ sevm).toNat - Nat.toB256 v < Bytes.toB256 [1] ∧
      (exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) * σ.get feeSlot /
          exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) = σ.get feeSlot ∨
        exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) = 0) ∧
      ¬ exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) <
        exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) ∧
      ((exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) -
          exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)) * exR0 /
          (exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) -
            exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)) = exR0 ∨
        exDy0 (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) -
          exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) = 0) ∧
      ¬ exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)
        (exRate (exJ sevm).toNat) < exMinDy sevm ∧
      (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) *
          σ.get adminFeeSlot /
          exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) =
          σ.get adminFeeSlot ∨
        exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot) = 0) ∧
      (exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
          (σ.get adminFeeSlot) * exR0 /
          exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
            (σ.get adminFeeSlot) = exR0 ∨
        exAdm0 (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
          (σ.get adminFeeSlot) = 0) ∧
      ¬ exBal σ ⟨(exI sevm).toNat, hi3⟩ + exCred sevm B1 B2 < exBal σ ⟨(exI sevm).toNat, hi3⟩ ∧
      ¬ exBal σ ⟨(exJ sevm).toNat, hj3⟩ <
        exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)
          (exRate (exJ sevm).toNat) ∧
      ¬ exBal σ ⟨(exJ sevm).toNat, hj3⟩ -
          exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)
            (exRate (exJ sevm).toNat) <
        exAdm (exDyFee (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot))
          (σ.get adminFeeSlot) (exRate (exJ sevm).toNat) ∧
      exPushAmt o = (exDyOut (exW3 x0 x1 x2 (exJ sevm).toNat) (Nat.toB256 v) (σ.get feeSlot)
        (exRate (exJ sevm).toNat)).toNat ∧
      i ≠ j ∧
      o.state.balances.get i = (exBal σ ⟨(exI sevm).toNat, hi3⟩ + exCred sevm B1 B2).toNat ∧
      pullIn (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i (exDx sevm).toNat =
        some (exCred sevm B1 B2).toNat ∧
      ∀ pre : Devm, costExchange sevm pre s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i j
        (exDx sevm).toNat = costGetY sevm pre amp (exI sevm).toNat (exJ sevm).toNat
          (exW3 x0 x1 x2 (exI sevm).toNat + exCred sevm B1 B2 * exRate (exI sevm).toNat /
            exR0).toNat x0.toNat x1.toNat x2.toNat + 8858 + 154000 := by
  obtain ⟨hk, xp, D, X, Y, x, amp, y, dy1, dy, dfp, fee, dop, outp, out, afp, adm0, aop, adm, bi,
    bj1, bj, hxp, hD, hX, hY, hx, hamp, hy, hdy1, hdy, hdfp, hfee, hdop, houtp, hout, hmin, hafp,
    hadm0, haop, hadm, hbi, hbj1, hbj, -, ho⟩ := exchange_inv hex
  have hi3 : (exI sevm).toNat < 3 := hi ▸ i.isLt
  have hj3 : (exJ sevm).toNat < 3 := hj ▸ j.isLt
  have hiF : i = ⟨(exI sevm).toNat, hi3⟩ := Fin.ext hi
  have hjF : j = ⟨(exJ sevm).toNat, hj3⟩ := Fin.ext hj
  subst hiF hjF
  have hD0 := hD
  have hamp0 := hamp
  have hxn : x = xp.get ⟨(exI sevm).toNat, hi3⟩ +
      D * rates.get ⟨(exI sevm).toNat, hi3⟩ / precision :=
    by rw [ex_chkAdd_eq hx, ex_chkDiv_eq hY, ex_chkMul_eq hX]
  have hne : (exI sevm).toNat ≠ (exJ sevm).toNat := by
    intro h
    have := getYChk_gyRes (amp := amp) (x := x) (x0 := xp.v0) (x1 := xp.v1) (x2 := xp.v2) hi3 hj3
      (by
        have hv : xp = V3.mk xp.v0 xp.v1 xp.v2 := rfl
        rw [← hv]; exact hy)
    exact this.1 h
  -- the stored balances and `xp` as words
  have hbal : s.balances = ⟨(balAt σ 0).toNat, (balAt σ 1).toNat, (balAt σ 2).toNat⟩ :=
    V3.ext_get fun k => by rw [← ex_w3_nat]; exact (ex_bal_nat ha k).symm
  have hxp0 := hxp
  rw [hbal] at hxp0
  obtain ⟨⟨p0, hm0, hd0⟩, ⟨p1, hm1, hd1⟩, ⟨p2, hm2, hd2⟩⟩ := xpChk_some_parts hxp
  have hx0 := ex_chkMulDiv_lt hm0 hd0
  have hx1 := ex_chkMulDiv_lt hm1 hd1
  have hx2 := ex_chkMulDiv_lt hm2 hd2
  clear hm0 hd0 hm1 hd1 hm2 hd2
  obtain ⟨v0, v1, v2⟩ := xp
  obtain ⟨x0, rfl⟩ : ∃ w : B256, w.toNat = v0 := ⟨_, B256.toNat_toB256_of_lt hx0⟩
  obtain ⟨x1, rfl⟩ : ∃ w : B256, w.toNat = v1 := ⟨_, B256.toNat_toB256_of_lt hx1⟩
  obtain ⟨x2, rfl⟩ : ∃ w : B256, w.toNat = v2 := ⟨_, B256.toNat_toB256_of_lt hx2⟩
  have hr : ∀ k : Fin 3, rates.get k = (exRate k.val).toNat := fun k => (ex_rate_nat k).symm
  have hp : precision = exR0.toNat := by decide
  have hd : feeDen = exFeeDen.toNat := by decide
  have e1 : (Bytes.toB256 [1]).toNat = 1 := by decide
  -- the credited amount
  have hDc : D = (exCred sevm B1 B2).toNat ∧ (exI sevm = 2 → ¬ B2 < B1) := by
    have hI : Nat.toB256 (exI sevm).toNat = exI sevm := toB256_toNat _
    unfold pullIn at hD
    by_cases hf : (⟨(exI sevm).toNat, hi3⟩ : Fin 3) = feeIndex
    · have h2 : exI sevm = 2 := by
        rw [← hI, show (exI sevm).toNat = 2 from congrArg Fin.val hf]; rfl
      rw [ite_eq_left_of_eq_true _ _ (eq_true hf)] at hD
      simp only [exEnv, exBalOpt, ite_eq_left_of_eq_true _ _ (eq_true hf), ite_true, decide_true,
        req,
        Option.bind_eq_bind,
        Option.bind_some] at hD
      obtain ⟨hlt, hv⟩ := ex_sub_of hD
      refine ⟨?_, fun _ => hlt⟩
      rw [← hv]; unfold exCred; rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
    · have h2 : exI sevm ≠ 2 := by
        intro h2; apply hf; apply Fin.ext; show (exI sevm).toNat = 2; rw [h2]; decide
      rw [ite_eq_right_of_eq_false _ _ (eq_false hf)] at hD
      simp only [exEnv, ite_true, decide_true, req, Option.bind_eq_bind, Option.bind_some] at hD
      refine ⟨?_, fun h => absurd h h2⟩
      rw [← Option.some.inj hD]; unfold exCred; rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
  obtain ⟨rfl, hsub⟩ := hDc
  -- the arithmetic, word by word
  rw [hr] at hX
  obtain ⟨hmx, rfl⟩ := ex_mul_of hX
  rw [hp] at hY
  obtain rfl := ex_div_of hY
  rw [← ex_w3_nat x0 x1 x2 ⟨(exI sevm).toNat, hi3⟩] at hx
  obtain ⟨hax, rfl⟩ := ex_add_of hx
  have hyl : y < 2 ^ 256 := lt_of_le_of_lt (ex_chkSub_le hdy1)
    (by rw [← ex_w3_nat]; exact B256.toNat_lt _)
  obtain ⟨yw, rfl⟩ : ∃ w : B256, w.toNat = y := ⟨_, B256.toNat_toB256_of_lt hyl⟩
  rw [← ex_w3_nat x0 x1 x2 ⟨(exJ sevm).toNat, hj3⟩] at hdy1
  obtain ⟨hy1, rfl⟩ := ex_sub_of hdy1
  have hdy' : chkSub (exW3 x0 x1 x2 (exJ sevm).toNat - yw).toNat (Bytes.toB256 [1]).toNat =
      some dy := by rw [e1]; exact hdy
  obtain ⟨hy2, rfl⟩ := ex_sub_of hdy'
  rw [← ha.fee] at hdfp
  obtain ⟨hmf, rfl⟩ := ex_mul_of hdfp
  rw [hd] at hfee
  obtain rfl := ex_div_of hfee
  obtain ⟨hsf, rfl⟩ := ex_sub_of hdop
  rw [hp] at houtp
  obtain ⟨hmo, rfl⟩ := ex_mul_of houtp
  rw [hr] at hout
  obtain rfl := ex_div_of hout
  rw [← ha.adminFee] at hafp
  obtain ⟨hma, rfl⟩ := ex_mul_of hafp
  rw [hd] at hadm0
  obtain rfl := ex_div_of hadm0
  rw [hp] at haop
  obtain ⟨hmap, rfl⟩ := ex_mul_of haop
  rw [hr] at hadm
  obtain rfl := ex_div_of hadm
  rw [← ex_bal_nat ha] at hbi hbj1
  obtain ⟨hbi', rfl⟩ := ex_add_of hbi
  obtain ⟨hbj1', rfl⟩ := ex_sub_of hbj1
  obtain ⟨hbj2', rfl⟩ := ex_sub_of hbj
  clear hX hY hx hdy1 hdy hdy' hdfp hfee hdop houtp hout hafp hadm0 haop hadm hbi hbj1 hbj hex hD
    hbal hx0 hx1 hx2
  subst ho
  refine ⟨x0, x1, x2, amp, yw.toNat, hi3, hj3, hk, hxp0, hsub, hmx, hax, hamp, hy, ?_⟩
  simp only [toB256_toNat]
  refine ⟨hy1, hy2, hmf, hsf, hmo, fun h => ?_, hma, hmap, hbi', hbj1', hbj2', rfl,
    fun h => hne (congrArg Fin.val h), ?_, hD0, fun pre => ?_⟩
  · exact absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hmin)
  · exact (V3.get_set_ne _ (k := ⟨(exJ sevm).toNat, hj3⟩) (k' := ⟨(exI sevm).toNat, hi3⟩)
      (fun h => hne (congrArg Fin.val h)) _).trans (V3.get_set_self _ _ _)
  · unfold costExchange
    rw [hxp, hD0, hamp0]
    dsimp only
    rw [← hxn]

end Words

end Blanc.Lift.Curve3Pool
