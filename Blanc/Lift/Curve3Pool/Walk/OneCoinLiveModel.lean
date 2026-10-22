import Blanc.Lift.Curve3Pool.Walk.OneCoinLiveFrame
import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveWords

/-!
# `remove_liquidity_one_coin`, inverted: the model's checked steps

`calcWithdrawOne_inv` and `removeLiquidityOneCoin_inv` read a successful model step back into
each checked operation it passed; `getDChk_lt` and `getYDChk_lt` bound the Newton results by a
word (every value they return comes from a checked operation), so the forward walk can carry
them as words.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem chkDiv_lt_of {a b z : Nat} (h : chkDiv a b = some z) (ha : a < 2 ^ 256) : z < 2 ^ 256 := by
  rw [ex_chkDiv_eq h]; exact lt_of_le_of_lt (Nat.div_le_self _ _) ha

theorem chkMul_lt_of {a b z : Nat} (h : chkMul a b = some z) : z < 2 ^ 256 := by
  rw [ex_chkMul_eq h]; exact chkMul_some_lt h

theorem chkAdd_lt_of {a b z : Nat} (h : chkAdd a b = some z) : z < 2 ^ 256 := by
  unfold chkAdd wordSize at h
  split at h
  · cases h; assumption
  · cases h

theorem chkSub_lt_of {a b z : Nat} (h : chkSub a b = some z) (ha : a < 2 ^ 256) : z < 2 ^ 256 := by
  unfold chkSub at h
  split at h
  · cases h; omega
  · cases h

theorem bodyDChk_lt {x : Fin 3 → Nat} {ann S D r : Nat} (h : bodyDChk x ann S D = some r) :
    r < 2 ^ 256 := by
  unfold bodyDChk at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, _, _, num, hnum, _, _, _, _, _, _, den, _, hdiv⟩ := h
  exact chkDiv_lt_of hdiv (chkMul_lt_of hnum)

theorem loopDChk_lt {x : Fin 3 → Nat} {ann S tol : Nat} :
    ∀ (fuel D r : Nat), D < 2 ^ 256 → loopDChk x ann S tol fuel D = some r → r < 2 ^ 256
  | 0, D, r, hD, h => by
    unfold loopDChk at h; cases h; exact hD
  | fuel + 1, D, r, hD, h => by
    unfold loopDChk at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨D', hD', h⟩ := h
    split at h
    · cases h; exact bodyDChk_lt hD'
    · exact loopDChk_lt fuel D' r (bodyDChk_lt hD') h

theorem getDChk_lt {x : Fin 3 → Nat} {amp tol r : Nat} (h : getDChk x amp tol = some r) :
    r < 2 ^ 256 := by
  unfold getDChk at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, S, hS, h⟩ := h
  split at h
  · cases h; norm_num only
  · obtain ⟨ann, _, h⟩ := Option.bind_eq_some_iff.mp h
    exact loopDChk_lt 255 S r (chkAdd_lt_of hS) h

theorem bodyYChk_lt {c b D y r : Nat} (h : bodyYChk c b D y = some r) : r < 2 ^ 256 := by
  unfold bodyYChk at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, num, hnum, _, _, _, _, den, _, hdiv⟩ := h
  exact chkDiv_lt_of hdiv (chkAdd_lt_of hnum)

theorem loopYChk_lt {c b D tol : Nat} :
    ∀ (fuel y r : Nat), y < 2 ^ 256 → loopYChk c b D tol fuel y = some r → r < 2 ^ 256
  | 0, y, r, hy, h => by
    unfold loopYChk at h; cases h; exact hy
  | fuel + 1, y, r, hy, h => by
    unfold loopYChk at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨y', hy', h⟩ := h
    split at h
    · cases h; exact bodyYChk_lt hy'
    · exact loopYChk_lt fuel y' r (bodyYChk_lt hy') h

theorem getYDChk_lt {amp : Nat} {i : Fin 3} {xp : Fin 3 → Nat} {D r : Nat} (hD : D < 2 ^ 256)
    (h : getYDChk amp i xp D = some r) : r < 2 ^ 256 := by
  unfold getYDChk at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, h⟩ := h
  exact loopYChk_lt 255 D r hD h

/-- **A successful model `_calc_withdraw_one_coin`, inverted.** -/
theorem calcWithdrawOne_inv {s : State} {e : Env} {amount : Nat} {i : Fin 3} {dy fee : Nat}
    (h : calcWithdrawOne s e amount i = some (dy, fee)) :
    ∃ amp F T xp D0 m q D1 newY d dy0 red y2 e1 e2,
      aChk s e.time = some amp ∧ feeAdj s = some F ∧ e.supply = some T ∧
      xpChk s.balances = some xp ∧ getDChk xp.get amp 1 = some D0 ∧ chkMul amount D0 = some m ∧
      chkDiv m T = some q ∧ chkSub D0 q = some D1 ∧ getYDChk amp i xp.get D1 = some newY ∧
      chkSub (xp.get i) newY = some d ∧ chkDiv d (precMul.get i) = some dy0 ∧
      V3.ofFnM (fun k => do
        let scaled ← chkDiv (← chkMul (xp.get k) D1) D0
        let dxExp ← if k = i then chkSub scaled newY else chkSub (xp.get k) scaled
        chkSub (xp.get k) (← chkDiv (← chkMul F dxExp) feeDen)) = some red ∧
      getYDChk amp i red.get D1 = some y2 ∧ chkSub (red.get i) y2 = some e1 ∧
      chkSub e1 1 = some e2 ∧ chkDiv e2 (precMul.get i) = some dy ∧ chkSub dy0 dy = some fee := by
  unfold calcWithdrawOne at h
  obtain ⟨amp, hamp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨F, hF, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨T, hT, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨xp, hxp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨D0, hD0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨m, hm, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨D1, hD1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨newY, hnewY, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨dy0, hdy0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨red, hred, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨y2, hy2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e1, he1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e2, he2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨dyv, hdyv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨fv, hfv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨amp, F, T, xp, D0, m, q, D1, newY, d, dy0, red, y2, e1, e2, hamp, hF, hT, hxp, hD0, hm,
    hq, hD1, hnewY, hd, hdy0, hred, hy2, he1, he2, hdyv, hfv⟩

/-- **A successful model `remove_liquidity_one_coin`, inverted.** -/
theorem removeLiquidityOneCoin_inv {s : State} {e : Env} {amount : Nat} {i : Fin 3}
    {minAmt : Nat} {o : Out} (h : removeLiquidityOneCoin s e amount i minAmt = some o) :
    s.isKilled = false ∧ ∃ dy fee p q take bi,
      calcWithdrawOne s e amount i = some (dy, fee) ∧ minAmt ≤ dy ∧
      chkMul fee s.adminFee = some p ∧ chkDiv p feeDen = some q ∧ chkAdd dy q = some take ∧
      chkSub (s.balances.get i) take = some bi ∧ e.burnOk = true ∧ (e.coin i).pushOk = true ∧
      o = ⟨{ s with balances := s.balances.set i bi }, none,
        [.removeLiquidityOne e.caller amount dy], [.burn e.caller amount, .push i e.caller dy]⟩ := by
  unfold removeLiquidityOneCoin req at h
  obtain ⟨u0, hk, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨dy, fee⟩, hcw, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u1, hmin, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨take, htake, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨bi, hbi, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u2, hburn, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u3, hpush, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := (Option.some.inj h).symm
  refine ⟨?_, dy, fee, p, q, take, bi, hcw, ?_, hp, hq, htake, hbi, ?_, ?_, rfl⟩
  · split_ifs at hk with hc
    · exact hc
  · split_ifs at hmin with hc
    · exact hc
  · split_ifs at hburn with hc
    · exact hc
  · split_ifs at hpush with hc
    · exact hc

theorem chkSub_word {x y : B256} {z : Nat} (h : chkSub x.toNat y.toNat = some z) :
    y.toNat ≤ x.toNat ∧ z = (x - y).toNat := by
  obtain ⟨g, v⟩ := ex_sub_of h
  exact ⟨toNat_le_of_not_lt g, v.symm⟩

theorem chkDiv_word {x y : B256} {z : Nat} (h : chkDiv x.toNat y.toNat = some z) :
    y ≠ 0 ∧ z = (x / y).toNat := by
  obtain ⟨g, v⟩ := fwdChkDiv h
  exact ⟨g, v.symm⟩

/-- **One fee-loop step, read back from the model** into the backward walk's `CwStep`. -/
theorem cwStep_of_chk {P eqk : Prop} [Decidable P] (hP : P ↔ eqk) {xk D1 D0 y F : B256} {rn : Nat}
    (h : (do
      let scaled ← chkDiv (← chkMul xk.toNat D1.toNat) D0.toNat
      let dxExp ← if P then chkSub scaled y.toNat else chkSub xk.toNat scaled
      chkSub xk.toNat (← chkDiv (← chkMul F.toNat dxExp) feeDen)) = some rn) :
    CwStep eqk xk D1 D0 y F xk (Nat.toB256 rn) ∧ rn < 2 ^ 256 := by
  obtain ⟨m, hm, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨sc, hsc, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hn, rfl⟩ := chkMul_inv hm
  obtain ⟨hD0, rfl⟩ := chkDiv_word hsc
  have hfd : feeDen = cwFeeDen.toNat := by decide
  dsimp only at h
  have fin : ∀ dxw : B256, ((eqk ∧ y.toNat ≤ (xk * D1 / D0).toNat ∧ dxw = xk * D1 / D0 - y) ∨
        (¬ eqk ∧ (xk * D1 / D0).toNat ≤ xk.toNat ∧ dxw = xk - xk * D1 / D0)) →
      ((chkMul F.toNat dxw.toNat).bind fun p => (chkDiv p feeDen).bind fun q =>
        chkSub xk.toNat q) = some rn →
      CwStep eqk xk D1 D0 y F xk (Nat.toB256 rn) ∧ rn < 2 ^ 256 := by
    intro dxw hbr h
    obtain ⟨mf, hmf, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hn2, rfl⟩ := chkMul_inv hmf
    rw [hfd] at hq
    obtain ⟨-, rfl⟩ := chkDiv_word hq
    obtain ⟨hle2, rfl⟩ := chkSub_word h
    exact ⟨⟨hn, hD0, dxw, hbr, hn2, hle2, by rw [toB256_toNat]⟩, B256.toNat_lt _⟩
  split at h
  · rename_i hp
    obtain ⟨dx, hdx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hle, rfl⟩ := chkSub_word hdx
    exact fin _ (.inl ⟨hP.mp hp, hle, rfl⟩) h
  · rename_i hp
    obtain ⟨dx, hdx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hle, rfl⟩ := chkSub_word hdx
    exact fin _ (.inr ⟨fun e => hp (hP.mpr e), hle, rfl⟩) h


end Blanc.Lift.Curve3Pool
