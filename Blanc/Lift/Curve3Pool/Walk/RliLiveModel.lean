import Blanc.Lift.Curve3Pool.Walk.RliLiveFrame
import Blanc.Lift.Curve3Pool.Walk.OneCoinLiveWords
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceRaw

/-!
# `remove_liquidity_imbalance`: the model read back

`removeLiquidityImbalance_inv` peels the model's success into its checked steps;
`rli_feeIter_of` reads one fee iteration (`feeAt`) back into the backward walk's
`RliFeeIter` over words.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **The model's `remove_liquidity_imbalance`, inverted.** -/
theorem removeLiquidityImbalance_inv {s : State} {e : Env} {amounts : V3} {mx : Nat} {o : Out}
    (h : removeLiquidityImbalance s e amounts mx = some o) :
    s.isKilled = false ∧ ∃ T fee amp D0 new D1 fees stored after D2 d m b0 b T',
      e.supply = some T ∧ T ≠ 0 ∧ feeAdj s = some fee ∧ aChk s e.time = some amp ∧
      getDMem s.balances amp = some D0 ∧
      V3.ofFnM (fun k => chkSub (s.balances.get k) (amounts.get k)) = some new ∧
      getDMem new amp = some D1 ∧
      feeLoop fee s.adminFee D0 D1 s.balances new = some (fees, stored, after) ∧
      getDMem after amp = some D2 ∧ chkSub D0 D2 = some d ∧ chkMul d T = some m ∧
      chkDiv m D0 = some b0 ∧ b0 ≠ 0 ∧ chkAdd b0 1 = some b ∧ b ≤ mx ∧ e.burnOk = true ∧
      ((amounts.v0 ≠ 0 → (e.coin 0).pushOk = true) ∧ (amounts.v1 ≠ 0 → (e.coin 1).pushOk = true) ∧
        (amounts.v2 ≠ 0 → (e.coin 2).pushOk = true)) ∧ chkSub T b = some T' ∧
      o = ⟨{ s with balances := stored }, none,
        [.removeLiquidityImbalance e.caller amounts fees D1 T'],
        .burn e.caller b :: pushCalls e.caller amounts⟩ := by
  unfold removeLiquidityImbalance req at h
  dsimp only at h
  obtain ⟨u0, hk, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨T, hT, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u1, hT0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨fee, hfee, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨amp, hamp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨D0, hD0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨new, hnew, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨D1, hD1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨fees, stored, after⟩, hfl, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨D2, hD2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨m, hm, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b0, hb0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u2, hbn, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u3, hmx, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u4, hburn, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u5, hpush, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨T', hT', h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := (Option.some.inj h).symm
  split_ifs at hk hT0 hbn hmx hburn hpush with c1 c2 c3 c4 c5 c6
  exact ⟨c1, T, fee, amp, D0, new, D1, fees, stored, after, D2, d, m, b0, b, T', hT, c2, hfee, hamp,
    hD0, hnew, hD1, hfl, hD2, hd, hm, hb0, c3, hb, c4, c5, c6, hT', rfl⟩

/-- **One fee iteration, read back from the model** into `RliFeeIter`. -/
theorem rli_feeIter_of {F AF D0 D1 B N : B256} {old new : V3} {i : Fin 3} {f st af : Nat}
    (h : feeAt F.toNat AF.toNat D0.toNat D1.toNat old new i = some (f, st, af))
    (hB : old.get i = B.toNat) (hN : new.get i = N.toNat) :
    RliFeeIter F AF D0 D1 B N (Nat.toB256 f) (Nat.toB256 st) (Nat.toB256 af) ∧
      f < 2 ^ 256 ∧ st < 2 ^ 256 ∧ af < 2 ^ 256 := by
  unfold feeAt at h
  rw [hB, hN] at h
  obtain ⟨m1, hm1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ideal, hid, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hn1, rfl⟩ := chkMul_inv hm1
  obtain ⟨hD0, rfl⟩ := chkDiv_word hid
  have hfd : feeDen = rliDen.toNat := by decide
  have fin : ∀ dif : B256, RliDif (D1 * B / D0) N dif →
      ((chkMul F.toNat dif.toNat).bind fun p => (chkDiv p feeDen).bind fun f =>
        (chkMul f AF.toNat).bind fun p => (chkDiv p feeDen).bind fun q =>
          (chkSub N.toNat q).bind fun stored => (chkSub N.toNat f).bind fun after =>
            some (f, stored, after)) = some (f, st, af) →
      RliFeeIter F AF D0 D1 B N (Nat.toB256 f) (Nat.toB256 st) (Nat.toB256 af) ∧
        f < 2 ^ 256 ∧ st < 2 ^ 256 ∧ af < 2 ^ 256 := by
    intro dif hdif h
    obtain ⟨m2, hm2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨fw, hfw, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hn2, rfl⟩ := chkMul_inv hm2
    rw [hfd] at hfw
    obtain ⟨-, rfl⟩ := chkDiv_word hfw
    obtain ⟨m3, hm3, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hn3, rfl⟩ := chkMul_inv hm3
    rw [hfd] at hq
    obtain ⟨-, rfl⟩ := chkDiv_word hq
    obtain ⟨sw, hsw, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hs3, rfl⟩ := chkSub_word hsw
    obtain ⟨aw, haw, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hs4, rfl⟩ := chkSub_word haw
    cases h
    refine ⟨⟨hn1, hD0, dif, hdif, hn2, by rw [toB256_toNat], by rw [toB256_toNat]; exact hn3,
      fun c => absurd (B256.lt_iff_toNat_lt_toNat.mp (by rw [toB256_toNat] at c; exact c))
        (Nat.not_lt.mpr hs3),
      by rw [toB256_toNat, toB256_toNat], fun c => absurd (B256.lt_iff_toNat_lt_toNat.mp
        (by rw [toB256_toNat] at c; exact c)) (Nat.not_lt.mpr hs4), by rw [toB256_toNat, toB256_toNat]⟩,
      B256.toNat_lt _, B256.toNat_lt _, B256.toNat_lt _⟩
  split at h
  · rename_i hgt
    obtain ⟨dw, hdw, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hle, rfl⟩ := chkSub_word hdw
    dsimp only at h
    exact fin _ (.inl ⟨B256.lt_iff_toNat_lt_toNat.mpr hgt, rfl⟩) h
  · rename_i hgt
    obtain ⟨dw, hdw, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hle, rfl⟩ := chkSub_word hdw
    dsimp only at h
    exact fin _ (.inr ⟨fun c => hgt (B256.lt_iff_toNat_lt_toNat.mp c), rfl⟩) h

/-- **`remove_liquidity_imbalance`'s sufficient-gas bound**: the three `get_D_mem` runs at the
model's arguments (`costGetDMem`) plus a closed constant for the frame's own instructions, storage
accesses, `_A`'s worst case and the frame saves and restores. `0` past a model revert. -/
def costImbalance (s : State) (e : Env) (amounts : V3) : Nat :=
  (do
    let amp ← aChk s e.time
    let fee ← feeAdj s
    let xa ← xpChk s.balances
    let D0 ← getDChk xa.get amp 1
    let new ← V3.ofFnM fun k => chkSub (s.balances.get k) (amounts.get k)
    let xb ← xpChk new
    let D1 ← getDChk xb.get amp 1
    let r ← feeLoop fee s.adminFee D0 D1 s.balances new
    let xc ← xpChk r.2.2
    some (costGetDMem xa amp + costGetDMem xb amp + costGetDMem xc amp + 240000)).getD 0

theorem rli_argV3 (sevm : Sevm) : argV3 sevm 0 =
    ⟨(rliAmt sevm 0).toNat, (rliAmt sevm 1).toNat, (rliAmt sevm 2).toNat⟩ := by
  unfold argV3 arg Sevm.argWord
  rw [rli_amt0, rli_amt1, rli_amt2,
    show (32 * 0 + 4 : B256) = Bytes.toB256 [4] by decide,
    show (32 * (0 + 1) + 4 : B256) = Bytes.toB256 [0x24] by decide,
    show (32 * (0 + 2) + 4 : B256) = Bytes.toB256 [0x44] by decide]

theorem rli_arg3 (sevm : Sevm) : arg sevm 3 = (Sevm.dataWord sevm (Bytes.toB256 [0x64])).toNat := by
  unfold arg Sevm.argWord
  rw [show (32 * 3 + 4 : B256) = Bytes.toB256 [0x64] by decide]

theorem rli_getDMem {b : V3} {amp D : Nat} (h : getDMem b amp = some D) :
    ∃ x, xpChk b = some x ∧ getDChk x.get amp 1 = some D := by
  unfold getDMem at h
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨x, hx, h⟩

end Blanc.Lift.Curve3Pool
