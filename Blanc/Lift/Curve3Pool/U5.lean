import Blanc.Lift.Curve3Pool.Model
import Blanc.Lift.StableSwapNewton.D

/-!
# U5 on the model: the amplification law

Goal `curve-3pool-stableswap-v1`, row U5, at the model level.

* `aChk_eq_aInterp`: `_A()` (lines 147–166) at block timestamp `t` is the stored linear
  interpolation `aInterp` between `initial_A` and `future_A` over
  `[initial_A_time, future_A_time]`, in the source's exact integer form (truncating division,
  separately for a rising and a falling ramp), whenever `t` is not before `initial_A_time` and the
  one product of the source does not overflow; `aChk_of_le` and `aInterp_of_le`: outside a ramp
  (`t ≥ future_A_time`, including the never-ramped `future_A_time = 0`) `A` is the constant
  `future_A`. `aInterp_between`: the interpolation stays between the two end points.
* `rampA_eq`: `ramp_A`'s guards exactly (owner, `MIN_RAMP_TIME` since the last ramp start and
  until the new end, `0 < A < MAX_A`, factor at most `MAX_A_CHANGE` either way) and its stores;
  `rampA_guards` reads the duration and factor bounds off any accepted ramp; `stopRampA_const`:
  after `stop_ramp_A()` `A` is constant at its value then.
* `u5_ramp_control`: the ramp control (spec report §5, also U3's negative control): from the
  constructor, one deposit, then `ramp_A(200, t0 + 2 days)` from `A = 2000` at `t0 + 1 day`;
  with no further operation `get_D(_xp(), _A())` falls from `200044801219456106169` to
  `192793226260180884069` while the supply stays put, so `D/T` falls.
* `dMonoInA`: the direction of `D`'s change when only `A` moves (`DMonoInA`): the exact root
  `⌊D*⌋` is non-decreasing in `A`, and the bytecode's `get_D` follows it only up to its loop
  error `E` at the smaller `A`.
-/

namespace Blanc.Lift.Curve3Pool

open Blanc.StableSwapNewton

/-! ## `_A` is the stored linear interpolation -/

/-- The stored linear interpolation of lines 156–166 at timestamp `t`, over unbounded naturals. -/
def aInterp (s : State) (t : Nat) : Nat :=
  if t < s.futureATime then
    if s.futureA > s.initialA then
      s.initialA + (s.futureA - s.initialA) * (t - s.initialATime) /
        (s.futureATime - s.initialATime)
    else
      s.initialA - (s.initialA - s.futureA) * (t - s.initialATime) /
        (s.futureATime - s.initialATime)
  else s.futureA

/-- Outside a ramp `_A()` is `future_A`. -/
theorem aInterp_of_le {s : State} {t : Nat} (h : s.futureATime ≤ t) : aInterp s t = s.futureA := by
  simp only [aInterp, Nat.not_lt.mpr h, ↓reduceIte]

/-- Outside a ramp the checked `_A()` succeeds with `future_A`. -/
theorem aChk_of_le {s : State} {t : Nat} (h : s.futureATime ≤ t) : aChk s t = some s.futureA := by
  simp only [aChk, Nat.not_lt.mpr h, ↓reduceIte]

/-- The truncated interpolation step never exceeds the full change. -/
private theorem step_le (d u v : Nat) (h : u < v) : d * u / v ≤ d :=
  Nat.div_le_of_le_mul (Nat.mul_comm v d ▸ Nat.mul_le_mul_left d (Nat.le_of_lt h))

/-- **`_A()` is the stored linear interpolation** at every timestamp not before the ramp start,
given that `future_A` is a word and the source's one product does not overflow. -/
theorem aChk_eq_aInterp {s : State} {t : Nat} (ht : s.initialATime ≤ t)
    (hA1 : s.futureA < wordSize)
    (hmul : (max s.futureA s.initialA - min s.futureA s.initialA) * (t - s.initialATime) <
      wordSize) :
    aChk s t = some (aInterp s t) := by
  unfold aChk aInterp
  by_cases hlt : t < s.futureATime
  · have hle0 : s.initialATime ≤ s.futureATime := by omega
    have hden : (s.futureATime - s.initialATime = 0) = False := eq_false (by omega)
    have hu : t - s.initialATime < s.futureATime - s.initialATime := by omega
    by_cases hup : s.futureA > s.initialA
    · have hm : (s.futureA - s.initialA) * (t - s.initialATime) < wordSize := by
        rwa [Nat.max_eq_left (Nat.le_of_lt hup), Nat.min_eq_right (Nat.le_of_lt hup)] at hmul
      have hd := step_le (s.futureA - s.initialA) _ _ hu
      simp only [hlt, hup, chkSub, chkMul, chkDiv, chkAdd, Nat.le_of_lt hup, ht, hle0, hm, hden,
        ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
      generalize (s.futureA - s.initialA) * (t - s.initialATime) / (s.futureATime - s.initialATime)
        = q at hd ⊢
      have hfin : s.initialA + q < wordSize := by omega
      simp only [hfin, ↓reduceIte]
    · have hle : s.futureA ≤ s.initialA := Nat.not_lt.mp hup
      have hm : (s.initialA - s.futureA) * (t - s.initialATime) < wordSize := by
        rwa [Nat.max_eq_right hle, Nat.min_eq_left hle] at hmul
      have hd := step_le (s.initialA - s.futureA) _ _ hu
      simp only [hlt, hup, chkSub, chkMul, chkDiv, hle, ht, hle0, hm, hden, ↓reduceIte,
        Option.bind_eq_bind, Option.bind_some]
      generalize (s.initialA - s.futureA) * (t - s.initialATime) / (s.futureATime - s.initialATime)
        = q at hd ⊢
      have hfin : q ≤ s.initialA := by omega
      simp only [hfin, ↓reduceIte]
  · simp only [hlt, ↓reduceIte]

/-- The interpolation stays between its end points. -/
theorem aInterp_between {s : State} {t : Nat} (ht : s.initialATime ≤ t) :
    min s.initialA s.futureA ≤ aInterp s t ∧ aInterp s t ≤ max s.initialA s.futureA := by
  unfold aInterp
  by_cases hlt : t < s.futureATime
  · have hu : t - s.initialATime < s.futureATime - s.initialATime := by omega
    by_cases hup : s.futureA > s.initialA
    · have hd := step_le (s.futureA - s.initialA) _ _ hu
      generalize (s.futureA - s.initialA) * (t - s.initialATime) / (s.futureATime - s.initialATime)
        = q at hd ⊢
      simp only [hlt, hup, ↓reduceIte]
      omega
    · have hd := step_le (s.initialA - s.futureA) _ _ hu
      generalize (s.initialA - s.futureA) * (t - s.initialATime) / (s.futureATime - s.initialATime)
        = q at hd ⊢
      simp only [hlt, hup, ↓reduceIte]
      omega
  · simp only [hlt, ↓reduceIte]
    omega

/-! ## `ramp_A`'s guards are exact -/

/-- **`ramp_A` exactly**: given the current `_A()` value `iA` and that the two timestamp sums are
words, the call succeeds iff the owner calls it at least `MIN_RAMP_TIME` after the last ramp
start, the new end is at least `MIN_RAMP_TIME` away, `0 < future_A < MAX_A`, and `future_A` is
within a factor `MAX_A_CHANGE` of `iA` in the direction of the change; it then stores the new ramp
and logs `RampA`. -/
theorem rampA_eq {s : State} {e : Env} {fA fT iA : Nat} (hA : aChk s e.time = some iA)
    (h1 : s.initialATime + minRampTime < wordSize) (h2 : e.time + minRampTime < wordSize) :
    rampA s e fA fT =
      if e.caller = s.owner ∧ s.initialATime + minRampTime ≤ e.time ∧
          e.time + minRampTime ≤ fT ∧ 0 < fA ∧ fA < maxA ∧
          ((iA ≤ fA ∧ fA ≤ iA * maxAChange) ∨ (fA < iA ∧ iA ≤ fA * maxAChange)) then
        some ⟨{ s with initialA := iA, futureA := fA, initialATime := e.time, futureATime := fT },
          none, [.rampA iA fA e.time fT], []⟩
      else none := by
  unfold rampA req
  simp only [chkAdd, h1, h2, hA, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  by_cases hc : e.caller = s.owner <;>
    simp only [hc, ↓reduceIte, true_and, false_and, Option.bind_none, Option.bind_some]
  by_cases g1 : s.initialATime + minRampTime ≤ e.time <;>
    simp only [g1, ge_iff_le, ↓reduceIte, true_and, false_and, Option.bind_none, Option.bind_some]
  by_cases g2 : e.time + minRampTime ≤ fT <;>
    simp only [g2, ↓reduceIte, true_and, false_and, Option.bind_none, Option.bind_some]
  by_cases g3 : 0 < fA ∧ fA < maxA
  · by_cases g4 : (iA ≤ fA ∧ fA ≤ iA * maxAChange) ∨ (fA < iA ∧ iA ≤ fA * maxAChange) <;>
      simp only [g3, g4, ↓reduceIte, true_and, Option.bind_none,
        Option.bind_some]
  · have g3' : ¬(0 < fA ∧ fA < maxA ∧
        (iA ≤ fA ∧ fA ≤ iA * maxAChange ∨ fA < iA ∧ iA ≤ fA * maxAChange)) :=
      fun h => g3 ⟨h.1, h.2.1⟩
    simp only [g3, g3', gt_iff_lt, ↓reduceIte, Option.bind_none]

/-- Any accepted ramp lasts at least `MIN_RAMP_TIME` and changes `A` by a factor of at most
`MAX_A_CHANGE`, from the `A` in force when it was called. -/
theorem rampA_guards {s : State} {e : Env} {fA fT : Nat} {o : Out} (h : rampA s e fA fT = some o) :
    o.state.initialATime + minRampTime ≤ o.state.futureATime ∧ 0 < o.state.futureA ∧
      o.state.futureA < maxA ∧ aChk s e.time = some o.state.initialA ∧
      o.state.futureA ≤ o.state.initialA * maxAChange ∧
      o.state.initialA ≤ o.state.futureA * maxAChange := by
  unfold rampA req at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_some_none_eq_some,
    chkAdd, and_true, Option.some.injEq] at h
  obtain ⟨-, -, a1, ⟨-, rfl⟩, -, -, a2, ⟨-, rfl⟩, -, c3, iA, hA, -, c4, -, c5, rfl⟩ := h
  refine ⟨c3, c4.1, c4.2, hA, ?_, ?_⟩ <;> rcases c5 with c5 | c5 <;>
    simp only [maxAChange, ge_iff_le] at c5 ⊢ <;> omega

/-- After `stop_ramp_A()` at `t`, `_A()` is constant from `t` on, at the value it had at `t`. -/
theorem stopRampA_const {s : State} {e : Env} {o : Out} (h : stopRampA s e = some o) {t : Nat}
    (ht : e.time ≤ t) : aChk o.state t = aChk s e.time := by
  unfold stopRampA req at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.ite_some_none_eq_some,
    Option.some.injEq, and_true] at h
  obtain ⟨-, -, cA, hA, rfl⟩ := h
  rw [hA]
  exact aChk_of_le ht

/-! ## The ramp control -/

/-- Spec report §5's deployment time `t0`. -/
def rampT0 : Nat := 1700000000

/-- From the constructor (`A = 2000`, fee `4e6`, admin fee `5e9`) at `t0`: deposit
`[100e18, 100e6, 1e6]`, then the owner calls `ramp_A(200, t0 + 2 days)` at `t0 + 1 day`. -/
def rampWorld : Option World := do
  let w ← deploy 2000 4000000 5000000000 rampT0
  let (w, _) ← worldRun w rampT0 1 (.addLiquidity ⟨100 * 10 ^ 18, 100 * 10 ^ 6, 10 ^ 6⟩ 0)
  let (w, _) ← worldRun w (rampT0 + 86400) 1 (.rampA 200 (rampT0 + 2 * 86400))
  some w

/-- `_A()`, `get_D(_xp(), _A())` and the supply of a world at timestamp `t`. -/
def aDT (w : World) (t : Nat) : Option (Nat × Nat × Nat) := do
  some (← aChk w.pool t, ← vDChk w.pool t, w.supply)

/-- **The ramp control** (kernel-checked): in one reachable state, with no operation in between,
`A` moves from 2000 to 200 between `t0 + 1 day` and `t0 + 2 days`, `D` falls and the 3Crv supply
`T` is unchanged, so `D/T` falls. Without the fixed-`A` premise, U3's monotonicity fails. -/
theorem u5_ramp_control :
    (rampWorld.bind fun w => do some (← aDT w (rampT0 + 86400), ← aDT w (rampT0 + 2 * 86400))) =
      some ((2000, 200044801219456106169, 200044801219456106169),
            (200, 192793226260180884069, 200044801219456106169)) := by
  decide +kernel

/-- The ramp control's conclusion: `D' * T < D * T` at the same supply `T > 0`. -/
theorem u5_ramp_control_falls :
    192793226260180884069 * 200044801219456106169 <
      200044801219456106169 * 200044801219456106169 := by
  decide +kernel

/-! ## The direction of `D`'s change with `A` -/

/-- **The direction law**: the exact root `⌊D*⌋` is non-decreasing in `A`
(`∂f/∂ann = D − S ≤ 0` below the root), and the bytecode's `get_D` follows it up to its loop
error `E = get_D − ⌊D*⌋` at the smaller `A`. The ramp control above reads against it: `A`
falls 2000 → 200 and `D` falls. -/
def DMonoInA : Prop :=
  ∀ (x : Fin 3 → Nat) (amp amp' : Nat), (∀ k, 0 < x k) → 1 ≤ amp → amp ≤ amp' →
    floorRoot x (amp * 3) ≤ floorRoot x (amp' * 3) ∧
      getD x amp 1 ≤ getD x amp' 1 + (getD x amp 1 - floorRoot x (amp * 3))

/-- `DMonoInA` holds: from the kit's `floorRoot_mono_ann` and `floorRoot_le_getD`. -/
theorem dMonoInA : DMonoInA := by
  intro x amp amp' hx hamp hle
  have h1 := floorRoot_mono_ann x (Nat.mul_le_mul_right 3 hle)
  have h2 := floorRoot_le_getD hx (Nat.le_trans hamp hle) 1
  exact ⟨h1, by omega⟩

end Blanc.Lift.Curve3Pool
