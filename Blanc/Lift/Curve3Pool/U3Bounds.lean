import Blanc.Lift.Curve3Pool.Model
import Blanc.Lift.StableSwapNewton.D
import Blanc.Lift.StableSwapNewton.Y

/-!
# U3 bounds: virtual price is monotone up to the Newton loops' integer errors

Goal `curve-3pool-stableswap-v1` §11: U3 is refuted (`U3Refute.lean`); what holds is
monotonicity **up to the loops' integer errors**. Every statement is about one successful model
step. `amp` is `_A()` at the block (`aChk s e.time = some amp` where the step reads it), each
step leaves the ramp fields alone (`∀ t, aChk o.state t = aChk s t`, so `D` and `D'` are taken at
the same `A`), `D = get_D(_xp(), A)` before and `D'` after, as the bytecode computes them, and
`T'` is the 3Crv supply after the frame's own `mint`/`burnFrom` calls (`supplyAfter`; that 3Crv
moves its supply exactly so is the premise U8 discharges). `E(x) = get_D(x) − ⌊D*(x)⌋ ≥ 0` is
`get_D`'s overestimate at scaled balances `x` (`floorRoot_le_getD`).

| operation | bound | extra premise |
|---|---|---|
| `remove_liquidity` | `D·T' ≤ (D' + 1)·T + E(pre)·T'` | `T > 0` |
| `donate_admin_fees` | `⌊D*(pre)⌋ ≤ D'`, so `D ≤ D' + E(pre)`, `T' = T` | each coin's `balanceOf(pool) ≥ balances[i]` |
| `add_liquidity` | `D·T' ≤ (D' + E(mid))·T`, `mid` the post-fee balances of line 335 | `T > 0`, `admin_fee ≤ 10^10` |
| `remove_liquidity_imbalance` | `D·T' ≤ (D' + E(mid))·T`, `mid` those of line 555 | `admin_fee ≤ 10^10` |
| `exchange` | `D ≤ D' + yGap`, `T' = T` | `admin_fee ≤ 10^10` |
| `remove_liquidity_one_coin` | `D·T' ≤ (D' + oneGap)·T` | `admin_fee ≤ 10^10` |

`yGap`/`oneGap` are the `get_y`/`get_y_D` floor gaps in `D` units: how far below its target level
(`D`, resp. `D1 = D − ⌊a·D/T⌋`) the exact floor root of the floored-coefficient quadratic lands
(`yLanding`, `oneLanding`). They contain no loop error (the loops return that root or one more,
`getYChk_rootOrSucc`, `getYDChk_rootOrSucc`), and `get_D`'s own overestimate `E` does not appear
for these two: the `y` solve aims at the overestimated level itself. The counterexamples of
`U3Refute.lean` show neither gap can be dropped.

`admin_fee ≤ 10^10` is `MAX_ADMIN_FEE`, enforced by `commit_new_fee`/`apply_new_fee` but not by the
constructor; the proofs use it to keep the stored balances at or above the priced ones.

The generic root facts used here (`aboveRoot_scale`, `aboveRoot_anti`, `scale_cross`,
`getDChk_cases`, `floorRoot_le_of_getDChk`, `aboveRoot_of_getDChk`) are contract-neutral and
candidates for the Newton kit (`Blanc/Lift/StableSwapNewton/`).
-/

namespace Blanc.Lift.Curve3Pool

open Blanc.StableSwapNewton

/-! ## Generic root facts -/

/-- The invariant is homogeneous: scaling the balances and `D` by `c > 0` does not move `D`
relative to the root. -/
theorem aboveRoot_scale {x : Fin 3 → Nat} {ann D c : Nat} (hc : 0 < c) :
    aboveRoot (fun k => c * x k) ann (c * D) ↔ aboveRoot x ann D := by
  unfold aboveRoot prod3 sum3
  have e1 : 27 * (c * x 0 * (c * x 1) * (c * x 2)) * ann * (c * x 0 + c * x 1 + c * x 2) =
      c ^ 4 * (27 * (x 0 * x 1 * x 2) * ann * (x 0 + x 1 + x 2)) := by ring
  have e2 : (c * D) ^ 4 + 27 * (c * x 0 * (c * x 1) * (c * x 2)) * (ann - 1) * (c * D) =
      c ^ 4 * (D ^ 4 + 27 * (x 0 * x 1 * x 2) * (ann - 1) * D) := by ring
  rw [e1, e2]
  exact Nat.mul_lt_mul_left (Nat.pow_pos hc)

/-- Being above the root is antitone in the balances: a point above the root for larger
balances is above it for smaller ones. -/
theorem aboveRoot_anti {x x' : Fin 3 → Nat} {ann D : Nat} (h : ∀ i, x i ≤ x' i)
    (h' : aboveRoot x' ann D) : aboveRoot x ann D := by
  have hS : sum3 x ≤ sum3 x' := by
    unfold sum3
    have := h 0
    have := h 1
    have := h 2
    omega
  have hP : prod3 x ≤ prod3 x' := by
    unfold prod3
    exact Nat.mul_le_mul (Nat.mul_le_mul (h 0) (h 1)) (h 2)
  unfold aboveRoot at *
  have hK : 27 * prod3 x ≤ 27 * prod3 x' := Nat.mul_le_mul_left _ hP
  generalize 27 * prod3 x = K at hK ⊢
  generalize 27 * prod3 x' = K' at hK h'
  generalize sum3 x = S at hS ⊢
  generalize sum3 x' = S' at hS h'
  rw [Nat.mul_assoc, Nat.mul_assoc K] at ⊢
  rw [Nat.mul_assoc, Nat.mul_assoc K'] at h'
  by_cases hc : (ann - 1) * D ≤ ann * S
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hc
    have hS2 : ann * S ≤ ann * S' := Nat.mul_le_mul_left _ hS
    have h1 : K' * (ann * S) ≤ K' * (ann * S') := Nat.mul_le_mul_left _ hS2
    have e1 : K * (ann * S) = K * ((ann - 1) * D) + K * t := by rw [ht, Nat.mul_add]
    have e2 : K' * (ann * S) = K' * ((ann - 1) * D) + K' * t := by rw [ht, Nat.mul_add]
    have h2 : K * t ≤ K' * t := Nat.mul_le_mul_right _ hK
    omega
  · have hD : 0 < D := by
      rcases Nat.eq_zero_or_pos D with rfl | hD
      · simp only [Nat.mul_zero, Nat.zero_le, not_true_eq_false] at hc
      · exact hD
    have hD4 : 0 < D ^ 4 := Nat.pow_pos hD
    rcases Nat.eq_zero_or_pos K with rfl | hK0
    · simp only [Nat.zero_mul, Nat.add_zero]
      exact hD4
    · have := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_le hc) hK0
      omega

/-- **Scaling across a cut.** If `T'·x ≤ T·x'` coordinatewise, `m` is not above the root at
`x` and `v` is above the root at `x'`, then `T'·m < T·v`: the root moves at least
proportionally. -/
theorem scale_cross {x x' : Fin 3 → Nat} {ann m v T T' : Nat} (hT : 0 < T)
    (hx : ∀ i, T' * x i ≤ T * x' i) (hm : ¬ aboveRoot x ann m) (hv : aboveRoot x' ann v) :
    T' * m < T * v := by
  have hv0 : 0 < v := by
    rcases Nat.eq_zero_or_pos v with rfl | h
    · exact absurd hv (not_aboveRoot_zero x' ann)
    · exact h
  rcases Nat.eq_zero_or_pos T' with rfl | hT'
  · rw [Nat.zero_mul]
    exact Nat.mul_pos hT hv0
  · have h1 : ¬ aboveRoot (fun k => T' * x k) ann (T' * m) := fun h => hm ((aboveRoot_scale hT').mp h)
    have h2 : aboveRoot (fun k => T * x' k) ann (T * v) := (aboveRoot_scale hT).mpr hv
    have h3 : aboveRoot (fun k => T' * x k) ann (T * v) := aboveRoot_anti hx h2
    exact Nat.lt_of_not_le fun hle => h1 (aboveRoot_mono h3 hle)

/-! ## What a non-reverting `get_D` gives -/

/-- A non-reverting `get_D` has `S = 0`, or positive balances and `A ≥ 1`. -/
theorem getDChk_cases {x : Fin 3 → Nat} {amp v : Nat} (h : getDChk x amp 1 = some v) :
    sum3 x = 0 ∨ ((∀ i, 0 < x i) ∧ 1 ≤ amp) := by
  unfold getDChk at h
  obtain ⟨s0, hs0, h⟩ := bind_some h
  obtain ⟨s1, hs1, h⟩ := bind_some h
  obtain ⟨S, hS, h⟩ := bind_some h
  have eS : S = sum3 x := by
    rw [chkAdd_some hS, chkAdd_some hs1, chkAdd_some hs0]
    unfold sum3
    omega
  subst eS
  by_cases h0 : sum3 x = 0
  · exact Or.inl h0
  · right
    simp only [h0, ↓reduceIte] at h
    obtain ⟨ann, hann, h⟩ := bind_some h
    rw [chkMul_some hann] at h
    unfold loopDChk at h
    obtain ⟨D', hD', -⟩ := bind_some h
    unfold bodyDChk at hD'
    obtain ⟨p, hp, h2⟩ := bind_some hD'
    obtain ⟨_, _, h2⟩ := bind_some h2
    obtain ⟨_, _, h2⟩ := bind_some h2
    obtain ⟨_, _, h2⟩ := bind_some h2
    obtain ⟨_, _, h2⟩ := bind_some h2
    obtain ⟨s, hs, -⟩ := bind_some h2
    have hamp := (chkSub_some hs).2
    unfold dPChk at hp
    obtain ⟨_, _, hp⟩ := bind_some hp
    obtain ⟨b0, hb0, hp⟩ := bind_some hp
    obtain ⟨p0, hp0, hp⟩ := bind_some hp
    obtain ⟨_, _, hp⟩ := bind_some hp
    obtain ⟨b1, hb1, hp⟩ := bind_some hp
    obtain ⟨p1, hp1, hp⟩ := bind_some hp
    obtain ⟨_, _, hp⟩ := bind_some hp
    obtain ⟨b2, hb2, hp⟩ := bind_some hp
    have n0 := (chkDiv_some hp0).2
    have n1 := (chkDiv_some hp1).2
    have n2 := (chkDiv_some hp).2
    rw [chkMul_some hb0] at n0
    rw [chkMul_some hb1] at n1
    rw [chkMul_some hb2] at n2
    refine ⟨fun i => ?_, by omega⟩
    match i with
    | 0 => exact Nat.pos_of_ne_zero fun e => n0 (by rw [e])
    | 1 => exact Nat.pos_of_ne_zero fun e => n1 (by rw [e])
    | 2 => exact Nat.pos_of_ne_zero fun e => n2 (by rw [e])

/-- A non-reverting `get_D` is never below the floor root. -/
theorem floorRoot_le_of_getDChk {x : Fin 3 → Nat} {amp v : Nat} (h : getDChk x amp 1 = some v) :
    floorRoot x (amp * 3) ≤ v := by
  rcases getDChk_cases h with h0 | ⟨hx, hamp⟩
  · have := floorRoot_le_sum3 x (amp * 3)
    omega
  · rw [getDChk_some h]
    exact floorRoot_le_getD hx hamp 1

/-- A non-reverting `get_D`'s successor is above the root. -/
theorem aboveRoot_of_getDChk {x : Fin 3 → Nat} {amp v : Nat} (h : getDChk x amp 1 = some v) :
    aboveRoot x (amp * 3) (v + 1) := by
  rcases getDChk_cases h with h0 | ⟨hx, hamp⟩
  · have hx0 : x 0 = 0 := by unfold sum3 at h0; omega
    unfold aboveRoot prod3
    rw [hx0]
    simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
    exact Nat.pow_pos (Nat.succ_pos v)
  · exact getDChk_lower h hx hamp


/-! ## Model plumbing -/

/-- The scaled balances `_xp_mem(b)` over unbounded naturals: `RATES[k] * b[k] / 10^18` is exactly
`PRECISION_MUL[k] * b[k]`. -/
def xpOf (b : V3) : Fin 3 → Nat := fun k => precMul.get k * b.get k

/-- The 3Crv supply after the frame's own `mint`/`burnFrom` calls, as an exact token moves it. -/
def supplyAfter : Nat → List ExtCall → Nat
  | T, [] => T
  | T, .mint _ v :: cs => supplyAfter (T + v) cs
  | T, .burn _ v :: cs => supplyAfter (T - v) cs
  | T, _ :: cs => supplyAfter T cs

theorem ofFnM_some {f : Fin 3 → Option Nat} {v : V3} (h : V3.ofFnM f = some v) :
    ∀ k, f k = some (v.get k) := by
  unfold V3.ofFnM at h
  obtain ⟨a, ha, h⟩ := bind_some h
  obtain ⟨b, hb, h⟩ := bind_some h
  obtain ⟨c, hc, h⟩ := bind_some h
  cases Option.some.inj h
  intro k
  match k with
  | 0 => exact ha
  | 1 => exact hb
  | 2 => exact hc

theorem xpChk_some {b v : V3} (h : xpChk b = some v) : v.get = xpOf b := by
  have h' := ofFnM_some h
  funext k
  have hk := h' k
  obtain ⟨p, hp, hk⟩ := bind_some hk
  rw [(chkDiv_some hk).1, chkMul_some hp]
  unfold xpOf
  match k with
  | 0 =>
    show 10 ^ 18 * b.v0 / 10 ^ 18 = 1 * b.v0
    rw [Nat.mul_comm, Nat.mul_div_cancel _ (Nat.pow_pos (by decide)), Nat.one_mul]
  | 1 =>
    show 10 ^ 30 * b.v1 / 10 ^ 18 = 10 ^ 12 * b.v1
    rw [show (10 : Nat) ^ 30 * b.v1 = 10 ^ 12 * b.v1 * 10 ^ 18 by ring,
      Nat.mul_div_cancel _ (Nat.pow_pos (by decide))]
  | 2 =>
    show 10 ^ 30 * b.v2 / 10 ^ 18 = 10 ^ 12 * b.v2
    rw [show (10 : Nat) ^ 30 * b.v2 = 10 ^ 12 * b.v2 * 10 ^ 18 by ring,
      Nat.mul_div_cancel _ (Nat.pow_pos (by decide))]

theorem getDMem_some {b : V3} {amp D : Nat} (h : getDMem b amp = some D) :
    getDChk (xpOf b) amp 1 = some D := by
  unfold getDMem at h
  obtain ⟨v, hv, h⟩ := bind_some h
  rwa [xpChk_some hv] at h

/-! ## `remove_liquidity` -/

/-- `remove_liquidity`'s effect: the supply read, the new balances `b_k − ⌊b_k·a/T⌋`, the
supply after the burn `T − a`, with `a ≤ T`. -/
theorem removeLiquidity_some {s : State} {e : Env} {a : Nat} {mins : V3} {o : Out}
    (h : removeLiquidity s e a mins = some o) :
    (∀ t, aChk o.state t = aChk s t) ∧ ∃ T, e.supply = some T ∧ a ≤ T ∧ supplyAfter T o.calls = T - a ∧
      (∀ k, o.state.balances.get k = s.balances.get k - s.balances.get k * a / T) ∧
      (∀ k, s.balances.get k * a / T ≤ s.balances.get k) := by
  unfold removeLiquidity at h
  obtain ⟨T, hT, h⟩ := bind_some h
  obtain ⟨vals, hvals, h⟩ := bind_some h
  obtain ⟨b, hb, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨T', hT', h⟩ := bind_some h
  cases Option.some.inj h
  have hv : ∀ k, vals.get k = s.balances.get k * a / T := fun k => by
    obtain ⟨p, hp, h1⟩ := bind_some (ofFnM_some hvals k)
    obtain ⟨q, hq, h1⟩ := bind_some h1
    obtain ⟨_, -, h1⟩ := bind_some h1
    obtain ⟨_, -, h1⟩ := bind_some h1
    rw [← Option.some.inj h1, (chkDiv_some hq).1, chkMul_some hp]
  have hb' : ∀ k, b.get k = s.balances.get k - vals.get k ∧ vals.get k ≤ s.balances.get k :=
    fun k => chkSub_some (ofFnM_some hb k)
  refine ⟨fun _ => rfl, T, hT, (chkSub_some hT').2, ?_, fun k => ?_, fun k => ?_⟩
  · simp only [supplyAfter]
  · rw [(hb' k).1, hv k]
  · rw [← hv k]
    exact (hb' k).2

/-- **U3 bound for `remove_liquidity`**: `D·T' ≤ (D' + 1)·T + E·T'`, with `E` the pre-state
loop error. In fact `⌊D*⌋·T' < (D' + 1)·T`: the exact root at the stored balances falls no
faster than the supply, because each balance loses at most its pro-rata share. -/
theorem u3_bound_remove_liquidity {s : State} {e : Env} {a : Nat} {mins : V3} {o : Out}
    {T amp D D' : Nat} (h : removeLiquidity s e a mins = some o) (hT : e.supply = some T)
    (hT0 : 0 < T) (hD : getDMem s.balances amp = some D)
    (hD' : getDMem o.state.balances amp = some D') :
    (∀ t, aChk o.state t = aChk s t) ∧
    D * supplyAfter T o.calls ≤
      (D' + 1) * T + (D - floorRoot (xpOf s.balances) (amp * 3)) * supplyAfter T o.calls := by
  obtain ⟨hAk, T0, hT0', haT, hsup, hbal, hle⟩ := removeLiquidity_some h
  refine ⟨hAk, ?_⟩
  rw [hT] at hT0'
  cases Option.some.inj hT0'
  rw [hsup]
  have hx : ∀ k, (T - a) * xpOf s.balances k ≤ T * xpOf o.state.balances k := fun k => by
    unfold xpOf
    rw [hbal k]
    generalize s.balances.get k = b at hle ⊢
    generalize precMul.get k = m
    have h1 : b * a / T * T ≤ b * a := Nat.div_mul_le_self _ _
    have h2 : (T - a) * b ≤ T * (b - b * a / T) := by
      generalize b * a / T = q at h1
      rw [Nat.sub_mul, Nat.mul_sub]
      have h3 : T * q ≤ a * b := by
        rw [Nat.mul_comm T q, Nat.mul_comm a b]
        exact h1
      omega
    calc (T - a) * (m * b) = m * ((T - a) * b) := by ring
      _ ≤ m * (T * (b - b * a / T)) := Nat.mul_le_mul_left _ h2
      _ = T * (m * (b - b * a / T)) := by ring
  have hc := scale_cross hT0 hx (floorRoot_spec (xpOf s.balances) (amp * 3))
    (aboveRoot_of_getDChk (getDMem_some hD'))
  have hm := floorRoot_le_of_getDChk (getDMem_some hD)
  generalize floorRoot (xpOf s.balances) (amp * 3) = m at hc hm ⊢
  obtain ⟨E, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_sub_cancel_left, Nat.add_mul, Nat.mul_comm m, Nat.mul_comm (D' + 1)]
  omega

/-! ## Shared steps -/

theorem xpOf_mono {b b' : V3} (h : ∀ k, b.get k ≤ b'.get k) (k : Fin 3) :
    xpOf b k ≤ xpOf b' k :=
  Nat.mul_le_mul_left _ (h k)

/-- The floor root at balances below a state's is below that state's `get_D`. -/
theorem floorRoot_le_of_below {b b' : V3} {amp D' : Nat} (h : ∀ k, b.get k ≤ b'.get k)
    (hD' : getDMem b' amp = some D') : floorRoot (xpOf b) (amp * 3) ≤ D' :=
  Nat.le_trans (floorRoot_mono (xpOf_mono h) _) (floorRoot_le_of_getDChk (getDMem_some hD'))

/-- One coin of the imbalance-fee loop: the stored balance keeps the admin share of the fee out
of the post-fee balance, so with `admin_fee ≤ 10^10` it is at least the post-fee balance. -/
theorem feeAt_some {fee adm D0 D1 : Nat} {old new : V3} {i : Fin 3} {f st af : Nat}
    (h : feeAt fee adm D0 D1 old new i = some (f, st, af)) (hadm : adm ≤ feeDen) : af ≤ st := by
  unfold feeAt at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  dsimp only at h
  split at h <;> obtain ⟨_, -, h⟩ := bind_some h <;> obtain ⟨p, hp, h⟩ := bind_some h <;>
    obtain ⟨f', hf, h⟩ := bind_some h <;> obtain ⟨q, hq, h⟩ := bind_some h <;>
    obtain ⟨r, hr, h⟩ := bind_some h <;> obtain ⟨st', hst, h⟩ := bind_some h <;>
    obtain ⟨af', haf, h⟩ := bind_some h <;> cases Option.some.inj h <;>
  · have hr' := (chkDiv_some hr).1
    rw [chkMul_some hq] at hr'
    have hle : r ≤ f := by
      rw [hr']
      exact Nat.div_le_of_le_mul
        (Nat.le_trans (Nat.mul_le_mul_left f hadm) (Nat.le_of_eq (Nat.mul_comm f feeDen)))
    rw [(chkSub_some hst).1, (chkSub_some haf).1]
    omega

theorem feeLoop_some {fee adm D0 D1 : Nat} {old new fees st af : V3}
    (h : feeLoop fee adm D0 D1 old new = some (fees, st, af)) (hadm : adm ≤ feeDen) :
    ∀ k, af.get k ≤ st.get k := by
  unfold feeLoop at h
  obtain ⟨r0, h0, h⟩ := bind_some h
  obtain ⟨r1, h1, h⟩ := bind_some h
  obtain ⟨r2, h2, h⟩ := bind_some h
  cases Option.some.inj h
  intro k
  match k with
  | 0 => exact feeAt_some h0 hadm
  | 1 => exact feeAt_some h1 hadm
  | 2 => exact feeAt_some h2 hadm

/-! ## `donate_admin_fees` -/

/-- **U3 bound for `donate_admin_fees`**, under the coin premise that each coin's
`balanceOf(pool)` is at least the pool's recorded balance: at an unchanged supply the post-state
`D'` is at least the pre-state floor root, so `D ≤ D' + E` for the pre-state `D = ⌊D*⌋ + E`.
Without the premise a coin reporting less than `balances` lowers `D` arbitrarily. -/
theorem u3_bound_donate_admin_fees {s : State} {e : Env} {o : Out} {T amp D D' : Nat}
    (h : donateAdminFees s e = some o)
    (hcoin : ∀ k v, (e.coin k).balPre = some v → s.balances.get k ≤ v)
    (hD' : getDMem o.state.balances amp = some D') :
    (∀ t, aChk o.state t = aChk s t) ∧ supplyAfter T o.calls = T ∧ floorRoot (xpOf s.balances) (amp * 3) ≤ D' ∧
      D ≤ D' + (D - floorRoot (xpOf s.balances) (amp * 3)) := by
  unfold donateAdminFees at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨b, hb, h⟩ := bind_some h
  cases Option.some.inj h
  refine ⟨fun _ => rfl, rfl, ?_⟩
  have hle : ∀ k, s.balances.get k ≤ b.get k := fun k => hcoin k _ (ofFnM_some hb k)
  have := floorRoot_le_of_below hle hD'
  exact ⟨this, by omega⟩

theorem supplyAfter_pullCalls (T c : Nat) (am : V3) (r : List ExtCall) :
    supplyAfter T (pullCalls c am ++ r) = supplyAfter T r := by
  unfold pullCalls
  simp only [List.filterMap_cons, List.filterMap_nil]
  split_ifs <;> simp only [List.cons_append, List.nil_append, supplyAfter]

theorem supplyAfter_pushCalls (T c : Nat) (am : V3) :
    supplyAfter T (pushCalls c am) = T := by
  unfold pushCalls
  simp only [List.filterMap_cons, List.filterMap_nil]
  split_ifs <;> simp only [supplyAfter]

/-! ## `add_liquidity` -/

/-- **U3 bound for `add_liquidity`** (not the first deposit): `D·T' ≤ (D' + E(mid))·T`, where
`mid` is the post-fee balance vector `new − fees` whose `get_D` (line 335) prices the mint and
`E(mid)` its loop error. Premise `admin_fee ≤ 10^10` (`MAX_ADMIN_FEE`, enforced by the fee
setters, not by the constructor): it keeps the stored balances at or above `mid`. -/
theorem u3_bound_add_liquidity {s : State} {e : Env} {am : V3} {mm : Nat} {o : Out}
    {T amp D D' : Nat} (h : addLiquidity s e am mm = some o) (hA : aChk s e.time = some amp)
    (hT : e.supply = some T) (hT0 : 0 < T) (hadm : s.adminFee ≤ feeDen)
    (hD : getDMem s.balances amp = some D) (hD' : getDMem o.state.balances amp = some D') :
    (∀ t, aChk o.state t = aChk s t) ∧ ∃ mid D2, getDMem mid amp = some D2 ∧
      (∀ k, mid.get k ≤ o.state.balances.get k) ∧
      D * supplyAfter T o.calls ≤ (D' + (D2 - floorRoot (xpOf mid) (amp * 3))) * T := by
  unfold addLiquidity at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨fee, -, h⟩ := bind_some h
  obtain ⟨amp', hA', h⟩ := bind_some h
  rw [hA] at hA'
  cases Option.some.inj hA'
  obtain ⟨T', hT', h⟩ := bind_some h
  rw [hT] at hT'
  cases Option.some.inj hT'
  dsimp only at h
  simp only [hT0, ↓reduceIte] at h
  obtain ⟨D0, hD0, h⟩ := bind_some h
  rw [hD] at hD0
  cases Option.some.inj hD0
  obtain ⟨new, -, h⟩ := bind_some h
  obtain ⟨D1, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨x3, hfl, h⟩ := bind_some h
  obtain ⟨fees, stored, mid⟩ := x3
  obtain ⟨D2, hD2, h⟩ := bind_some h
  obtain ⟨x4, hx4, h⟩ := bind_some h
  cases Option.some.inj hx4
  simp only [Nat.pos_iff_ne_zero.mp hT0, ↓reduceIte] at h
  obtain ⟨d, hd, h⟩ := bind_some h
  obtain ⟨p, hp, h⟩ := bind_some h
  obtain ⟨mint, hmint, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  cases Option.some.inj h
  refine ⟨fun _ => rfl, mid, D2, hD2, feeLoop_some hfl hadm, ?_⟩
  rw [supplyAfter_pullCalls]
  simp only [supplyAfter]
  have hm := floorRoot_le_of_below (feeLoop_some hfl hadm) hD'
  obtain ⟨rfl, hDD2⟩ := chkSub_some hd
  rw [chkMul_some hp] at hmint
  obtain ⟨rfl, -⟩ := chkDiv_some hmint
  have h1 : D * (T * (D2 - D) / D) ≤ T * (D2 - D) := Nat.mul_div_le _ _
  generalize floorRoot (xpOf mid) (amp * 3) = m at hm ⊢
  generalize T * (D2 - D) / D = q at h1 ⊢
  have e1 : D * (T + q) = D * T + D * q := Nat.mul_add _ _ _
  have e2 : T * (D2 - D) + T * D = T * D2 := by rw [← Nat.mul_add, Nat.sub_add_cancel hDD2]
  have e3 : D2 * T ≤ (D' + (D2 - m)) * T := Nat.mul_le_mul_right _ (by omega)
  have e4 : D * T = T * D := Nat.mul_comm _ _
  have e5 : D2 * T = T * D2 := Nat.mul_comm _ _
  omega

/-! ## `remove_liquidity_imbalance` -/

/-- **U3 bound for `remove_liquidity_imbalance`**: `D·T' ≤ (D' + E(mid))·T`, with `mid` the
post-fee balances whose `get_D` (line 555) prices the burn. The `+ 1` of line 559 and the
floor of line 557 together burn at least `(D − D2)·T / D`. Premise `admin_fee ≤ 10^10` as for
`add_liquidity`. -/
theorem u3_bound_remove_liquidity_imbalance {s : State} {e : Env} {am : V3} {mb : Nat}
    {o : Out} {T amp D D' : Nat} (h : removeLiquidityImbalance s e am mb = some o)
    (hA : aChk s e.time = some amp) (hT : e.supply = some T) (hadm : s.adminFee ≤ feeDen)
    (hD : getDMem s.balances amp = some D) (hD' : getDMem o.state.balances amp = some D') :
    (∀ t, aChk o.state t = aChk s t) ∧ ∃ mid D2, getDMem mid amp = some D2 ∧
      (∀ k, mid.get k ≤ o.state.balances.get k) ∧
      D * supplyAfter T o.calls ≤ (D' + (D2 - floorRoot (xpOf mid) (amp * 3))) * T := by
  unfold removeLiquidityImbalance at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨T', hT', h⟩ := bind_some h
  rw [hT] at hT'
  cases Option.some.inj hT'
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨fee, -, h⟩ := bind_some h
  obtain ⟨amp', hA', h⟩ := bind_some h
  rw [hA] at hA'
  cases Option.some.inj hA'
  obtain ⟨D0, hD0, h⟩ := bind_some h
  rw [hD] at hD0
  cases Option.some.inj hD0
  obtain ⟨new, -, h⟩ := bind_some h
  obtain ⟨D1, -, h⟩ := bind_some h
  obtain ⟨x3, hfl, h⟩ := bind_some h
  obtain ⟨fees, stored, mid⟩ := x3
  obtain ⟨D2, hD2, h⟩ := bind_some h
  obtain ⟨d, hd, h⟩ := bind_some h
  obtain ⟨p, hp, h⟩ := bind_some h
  obtain ⟨q, hq, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨burn, hburn, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨T'', hT'', h⟩ := bind_some h
  cases Option.some.inj h
  refine ⟨fun _ => rfl, mid, D2, hD2, feeLoop_some hfl hadm, ?_⟩
  simp only [supplyAfter, supplyAfter_pushCalls]
  have hm := floorRoot_le_of_below (feeLoop_some hfl hadm) hD'
  obtain ⟨rfl, hD2D⟩ := chkSub_some hd
  rw [chkMul_some hp] at hq
  obtain ⟨rfl, hD0⟩ := chkDiv_some hq
  rw [chkAdd_some hburn] at hT''
  have hle := (chkSub_some hT'').2
  have h1 : (D - D2) * T < D * ((D - D2) * T / D + 1) :=
    Nat.lt_mul_div_succ _ (Nat.pos_of_ne_zero hD0)
  rw [chkAdd_some hburn]
  generalize floorRoot (xpOf mid) (amp * 3) = m at hm ⊢
  generalize (D - D2) * T / D + 1 = b at h1 hle ⊢
  have e1 : D * (T - b) + D * b = D * T := by rw [← Nat.mul_add, Nat.sub_add_cancel hle]
  have e2 : (D - D2) * T + D2 * T = D * T := by rw [← Nat.add_mul, Nat.sub_add_cancel hD2D]
  have e3 : D2 * T ≤ (D' + (D2 - m)) * T := Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## The `y` floor gap: `exchange` and `remove_liquidity_one_coin` -/

theorem V3.get_set_self (v : V3) (k : Fin 3) (x : Nat) : (v.set k x).get k = x := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

theorem V3.get_set_ne (v : V3) {k k' : Fin 3} (h : k' ≠ k) (x : Nat) :
    (v.set k x).get k' = v.get k' := by
  match k, k' with
  | 0, 0 => exact absurd rfl h
  | 0, 1 => rfl
  | 0, 2 => rfl
  | 1, 0 => rfl
  | 1, 1 => exact absurd rfl h
  | 1, 2 => rfl
  | 2, 0 => rfl
  | 2, 1 => rfl
  | 2, 2 => exact absurd rfl h

theorem rates_eq (k : Fin 3) : rates.get k = precMul.get k * precision := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

theorem precMul_pos (k : Fin 3) : 0 < precMul.get k := by
  match k with
  | 0 => decide
  | 1 => decide
  | 2 => decide

theorem toUnits (z : Nat) (k : Fin 3) : z * precision / rates.get k = z / precMul.get k := by
  rw [rates_eq]
  exact Nat.mul_div_mul_right _ _ (Nat.pow_pos (by decide))

theorem fromUnits (z : Nat) (k : Fin 3) : z * rates.get k / precision = precMul.get k * z := by
  rw [rates_eq, ← Nat.mul_assoc, Nat.mul_comm z]
  exact Nat.mul_div_cancel _ (Nat.pow_pos (by decide))

/-- The point `get_y` lands on at level `D`: `x` at `i`, the exact floor root of its
floored-coefficient quadratic plus the source's 1-wei margin (line 465) at `j`, the third
balance as it was. -/
def yLanding (xp : Fin 3 → Nat) (i j : Fin 3) (x D ann : Nat) (k : Fin 3) : Nat :=
  if k = j then
    rootQ (cOf (withAt xp i x (others j).1) (withAt xp i x (others j).2) D ann)
      (bOf (withAt xp i x (others j).1) (withAt xp i x (others j).2) D ann) D + 1
  else withAt xp i x k

/-- **The `get_y` floor gap** in `D` units: how far below level `D` the landing point lies.
It is zero when the floored-coefficient root plus 1 reaches the invariant at `D`; the
counterexamples show it is not always zero. It contains no loop error: the loop returns the
floor root or one more (`getYChk_rootOrSucc`). -/
def yGap (xp : Fin 3 → Nat) (i j : Fin 3) (x D ann : Nat) : Nat :=
  D - floorRoot (yLanding xp i j x D ann) ann

/-- **U3 bound for `exchange`**: at an unchanged supply, `D ≤ D' + G`, with `G` the `get_y`
floor gap at the pre-state level `D` and the new scaled balance `x` of the sold coin. `get_D`'s
own overestimate does not appear: `get_y` solves at level `D`, and the fee and the roundings at
lines 465–478 keep the bought coin's new balance at or above the landing point. Premise
`admin_fee ≤ 10^10`. -/
theorem u3_bound_exchange {s : State} {e : Env} {i j : Fin 3} {dx md : Nat} {o : Out}
    {T amp D D' : Nat} (h : exchange s e i j dx md = some o) (hA : aChk s e.time = some amp)
    (hadm : s.adminFee ≤ feeDen) (hD : getDMem s.balances amp = some D)
    (hD' : getDMem o.state.balances amp = some D') :
    (∀ t, aChk o.state t = aChk s t) ∧ supplyAfter T o.calls = T ∧
      D ≤ D' + yGap (xpOf s.balances) i j (xpOf o.state.balances i) D (amp * 3) := by
  unfold exchange at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨xp, hxp, h⟩ := bind_some h
  have exp := xpChk_some hxp
  obtain ⟨dxw, -, h⟩ := bind_some h
  obtain ⟨p1, hp1, h⟩ := bind_some h
  obtain ⟨q1, hq1, h⟩ := bind_some h
  obtain ⟨x, hx, h⟩ := bind_some h
  obtain ⟨amp', hA', h⟩ := bind_some h
  rw [hA] at hA'
  cases Option.some.inj hA'
  obtain ⟨y, hy, h⟩ := bind_some h
  obtain ⟨d1, hd1, h⟩ := bind_some h
  obtain ⟨dy, hdy, h⟩ := bind_some h
  obtain ⟨p2, hp2, h⟩ := bind_some h
  obtain ⟨dyFee, hdyFee, h⟩ := bind_some h
  obtain ⟨d3, hd3, h⟩ := bind_some h
  obtain ⟨p3, hp3, h⟩ := bind_some h
  obtain ⟨dyOut, hdyOut, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨p4, hp4, h⟩ := bind_some h
  obtain ⟨adm1, hadm1, h⟩ := bind_some h
  obtain ⟨p5, hp5, h⟩ := bind_some h
  obtain ⟨adm2, hadm2, h⟩ := bind_some h
  obtain ⟨bi, hbi, h⟩ := bind_some h
  obtain ⟨d6, hd6, h⟩ := bind_some h
  obtain ⟨bj, hbj, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  cases Option.some.inj h
  refine ⟨fun _ => rfl, rfl, ?_⟩
  have hij : i ≠ j := fun e => by
    unfold getYChk at hy
    simp only [e, ↓reduceIte, reduceCtorEq] at hy
  have hry := getYChk_rootOrSucc hy
  rw [exp, ← getDChk_some (getDMem_some hD)] at hry
  have hry' : rootQ (cOf (withAt (xpOf s.balances) i x (others j).1)
      (withAt (xpOf s.balances) i x (others j).2) D (amp * 3))
      (bOf (withAt (xpOf s.balances) i x (others j).1)
      (withAt (xpOf s.balances) i x (others j).2) D (amp * 3)) D ≤ y := by
    rcases hry with hr | hr
    · exact Nat.le_of_eq hr.symm
    · omega
  -- the sold coin's new scaled balance is `x`
  rw [exp] at hx
  have ex : x = xpOf s.balances i + precMul.get i * dxw := by
    rw [chkAdd_some hx, (chkDiv_some hq1).1, chkMul_some hp1, fromUnits]
  have hpi : (((s.balances.set i bi).set j bj)).get i = bi := by
    rw [V3.get_set_ne _ hij, V3.get_set_self]
  have hxi : xpOf ((s.balances.set i bi).set j bj) i = x := by
    unfold xpOf at ex ⊢
    rw [hpi, chkAdd_some hbi, ex, Nat.mul_add]
  rw [hxi]
  -- the bought coin keeps at least the landing point
  rw [exp] at hd1
  obtain ⟨rfl, hyj⟩ := chkSub_some hd1
  obtain ⟨rfl, h1⟩ := chkSub_some hdy
  rw [chkMul_some hp2] at hdyFee
  obtain ⟨rfl, -⟩ := chkDiv_some hdyFee
  obtain ⟨rfl, hfd⟩ := chkSub_some hd3
  rw [chkMul_some hp3] at hdyOut
  obtain ⟨e3, -⟩ := chkDiv_some hdyOut
  rw [toUnits] at e3
  subst e3
  rw [chkMul_some hp4] at hadm1
  obtain ⟨rfl, -⟩ := chkDiv_some hadm1
  rw [chkMul_some hp5] at hadm2
  obtain ⟨e5, -⟩ := chkDiv_some hadm2
  rw [toUnits] at e5
  subst e5
  obtain ⟨ed6, hd6'⟩ := chkSub_some hd6
  obtain ⟨ebj, hbj'⟩ := chkSub_some hbj
  generalize hF : (xpOf s.balances j - y - 1) * s.fee / feeDen = F at hfd ed6 ebj hd6' hbj'
  have hA1 := Nat.mul_div_le (xpOf s.balances j - y - 1 - F) (precMul.get j)
  have hA3 : F * s.adminFee / feeDen ≤ F := Nat.div_le_of_le_mul
    (Nat.le_trans (Nat.mul_le_mul_left F hadm) (Nat.le_of_eq (Nat.mul_comm F feeDen)))
  have hA2 := Nat.mul_div_le (F * s.adminFee / feeDen) (precMul.get j)
  generalize (xpOf s.balances j - y - 1 - F) / precMul.get j = o1 at hA1 hd6' ed6
  generalize (F * s.adminFee / feeDen) / precMul.get j = o2 at hA2 hbj' ebj
  generalize F * s.adminFee / feeDen = a1 at hA2 hA3
  have hpj : (((s.balances.set i bi).set j bj)).get j = bj := V3.get_set_self _ _ _
  have hsum : precMul.get j * bj + precMul.get j * o2 +
      precMul.get j * o1 = xpOf s.balances j := by
    unfold xpOf
    rw [← Nat.mul_add, ← Nat.mul_add]
    congr 1
    omega
  have hland : ∀ k, yLanding (xpOf s.balances) i j x D (amp * 3) k ≤
      xpOf ((s.balances.set i bi).set j bj) k := fun k => by
    unfold yLanding
    by_cases hkj : k = j
    · subst hkj
      simp only [↓reduceIte]
      have hpost : xpOf ((s.balances.set i bi).set k bj) k = precMul.get k * bj := by
        unfold xpOf
        rw [hpj]
      rw [hpost]
      omega
    · simp only [hkj, ↓reduceIte]
      unfold withAt
      by_cases hki : k = i
      · subst hki
        simp only [↓reduceIte, hxi, Nat.le_refl]
      · simp only [hki, ↓reduceIte]
        unfold xpOf
        rw [V3.get_set_ne _ hkj, V3.get_set_ne _ hki]
  have hfl := Nat.le_trans (floorRoot_mono hland (amp * 3))
    (floorRoot_le_of_getDChk (getDMem_some hD'))
  unfold yGap
  omega

/-- The point the first `get_y_D` (line 645) lands on at the reduced level `D1`: the floor root
of its floored-coefficient quadratic at `i`, the other balances as they were. -/
def oneLanding (xp : Fin 3 → Nat) (i : Fin 3) (D1 ann : Nat) (k : Fin 3) : Nat :=
  if k = i then
    rootQ (cOf (xp (others i).1) (xp (others i).2) D1 ann)
      (bOf (xp (others i).1) (xp (others i).2) D1 ann) D1
  else xp k

/-- **The `get_y_D` floor gap** in `D` units at level `D1`. -/
def oneGap (xp : Fin 3 → Nat) (i : Fin 3) (D1 ann : Nat) : Nat :=
  D1 - floorRoot (oneLanding xp i D1 ann) ann

/-- **U3 bound for `remove_liquidity_one_coin`**: `D·T' ≤ (D' + G)·T`, with `G` the `get_y_D`
floor gap at the reduced level `D1 = D − ⌊a·D/T⌋` (line 642). The withdrawn amount plus the
admin share never exceeds `dy_0` (line 646), so the coin's new balance stays at or above the
landing point; `D1·T ≥ D·T'` by the floor at line 642. Premise `admin_fee ≤ 10^10`. -/
theorem u3_bound_remove_liquidity_one_coin {s : State} {e : Env} {a : Nat} {i : Fin 3}
    {mn : Nat} {o : Out} {T amp D D' : Nat} (h : removeLiquidityOneCoin s e a i mn = some o)
    (hA : aChk s e.time = some amp) (hT : e.supply = some T) (hadm : s.adminFee ≤ feeDen)
    (hD : getDMem s.balances amp = some D) (hD' : getDMem o.state.balances amp = some D') :
    (∀ t, aChk o.state t = aChk s t) ∧
    D * supplyAfter T o.calls ≤
      (D' + oneGap (xpOf s.balances) i (D - a * D / T) (amp * 3)) * T := by
  unfold removeLiquidityOneCoin at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨x2, hc, h⟩ := bind_some h
  obtain ⟨dy, dyFee⟩ := x2
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨p, hp, h⟩ := bind_some h
  obtain ⟨r, hr, h⟩ := bind_some h
  obtain ⟨take, htake, h⟩ := bind_some h
  obtain ⟨bi, hbi, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  cases Option.some.inj h
  refine ⟨fun _ => rfl, ?_⟩
  unfold calcWithdrawOne at hc
  obtain ⟨amp', hA', hc⟩ := bind_some hc
  rw [hA] at hA'
  cases Option.some.inj hA'
  obtain ⟨_, -, hc⟩ := bind_some hc
  obtain ⟨T', hT', hc⟩ := bind_some hc
  rw [hT] at hT'
  cases Option.some.inj hT'
  obtain ⟨xp, hxp, hc⟩ := bind_some hc
  have exp := xpChk_some hxp
  obtain ⟨D0, hD0, hc⟩ := bind_some hc
  rw [exp, getDMem_some hD] at hD0
  cases Option.some.inj hD0
  obtain ⟨p1, hp1, hc⟩ := bind_some hc
  obtain ⟨q1, hq1, hc⟩ := bind_some hc
  obtain ⟨D1, hD1, hc⟩ := bind_some hc
  obtain ⟨newY, hNY, hc⟩ := bind_some hc
  obtain ⟨d1, hd1, hc⟩ := bind_some hc
  obtain ⟨dy0, hdy0, hc⟩ := bind_some hc
  obtain ⟨_, -, hc⟩ := bind_some hc
  obtain ⟨_, -, hc⟩ := bind_some hc
  obtain ⟨_, -, hc⟩ := bind_some hc
  obtain ⟨_, -, hc⟩ := bind_some hc
  obtain ⟨dyv, hdyv, hc⟩ := bind_some hc
  obtain ⟨df, hdf, hc⟩ := bind_some hc
  cases Option.some.inj hc
  simp only [supplyAfter]
  -- the reduced level
  rw [chkMul_some hp1] at hq1
  obtain ⟨rfl, hT0⟩ := chkDiv_some hq1
  obtain ⟨rfl, hqD⟩ := chkSub_some hD1
  have hTD : (T - a) * D ≤ T * (D - a * D / T) := by
    have h1 : T * (a * D / T) ≤ a * D := Nat.mul_div_le _ _
    rw [Nat.sub_mul, Nat.mul_sub]
    omega
  -- the landing point lies below the new balances
  have hry := getYDChk_rootOrSucc hNY
  rw [exp] at hry hd1
  have hry' : oneLanding (xpOf s.balances) i (D - a * D / T) (amp * 3) i ≤ newY := by
    unfold oneLanding
    simp only [↓reduceIte]
    rcases hry with hr' | hr'
    · exact Nat.le_of_eq hr'.symm
    · omega
  obtain ⟨rfl, hNYle⟩ := chkSub_some hd1
  obtain ⟨rfl, -⟩ := chkDiv_some hdy0
  have hm0 := Nat.mul_div_le (xpOf s.balances i - newY) (precMul.get i)
  obtain ⟨rfl, hdyle⟩ := chkSub_some hdf
  rw [chkMul_some hp] at hr
  obtain ⟨rfl, -⟩ := chkDiv_some hr
  rw [chkAdd_some htake] at hbi
  obtain ⟨ebi, hbile⟩ := chkSub_some hbi
  generalize (xpOf s.balances i - newY) / precMul.get i = dy0 at hm0 hdyle ebi hbile
  have hA3 : (dy0 - dy) * s.adminFee / feeDen ≤ dy0 - dy := Nat.div_le_of_le_mul
    (Nat.le_trans (Nat.mul_le_mul_left _ hadm) (Nat.le_of_eq (Nat.mul_comm _ feeDen)))
  generalize (dy0 - dy) * s.adminFee / feeDen = r at hA3 ebi hbile
  have htk : dy + r ≤ dy0 := by omega
  have hmt : precMul.get i * (dy + r) ≤ precMul.get i * dy0 := Nat.mul_le_mul_left _ htk
  have hsum : precMul.get i * bi + precMul.get i * (dy + r) = xpOf s.balances i := by
    unfold xpOf
    rw [← Nat.mul_add]
    congr 1
    omega
  have hland : ∀ k, oneLanding (xpOf s.balances) i (D - a * D / T) (amp * 3) k ≤
      xpOf (s.balances.set i bi) k := fun k => by
    by_cases hki : k = i
    · subst hki
      have hpost : xpOf (s.balances.set k bi) k = precMul.get k * bi := by
        unfold xpOf
        rw [V3.get_set_self]
      rw [hpost]
      omega
    · unfold oneLanding xpOf
      simp only [hki, ↓reduceIte]
      rw [V3.get_set_ne _ hki]
  have hfl := Nat.le_trans (floorRoot_mono hland (amp * 3))
    (floorRoot_le_of_getDChk (getDMem_some hD'))
  unfold oneGap
  generalize D - a * D / T = D1 at hTD hfl ⊢
  have e1 : D1 * T ≤ (D' + (D1 - floorRoot (oneLanding (xpOf s.balances) i D1 (amp * 3))
      (amp * 3))) * T := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.mul_comm D, Nat.mul_comm D1] at *
  omega

end Blanc.Lift.Curve3Pool
