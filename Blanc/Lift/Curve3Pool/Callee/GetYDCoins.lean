import Blanc.Lift.Curve3Pool.Callee.GetYDLoop

/-!
# `get_y_D` before its Newton loop, inverted

* `ric_ydPost`: the set-up after the coin loop (`c = c * D / (Ann * N_COINS)`,
  `b = S_ + D / Ann`, `y = D`) and the whole `y` loop: `ydPostRes`;
* `ric_ydCoinTail*`, `ric_ydAcc`, `ric_ydTest`: one iteration of the coin loop
  (`for _i in range(N_COINS)`, skipping `i`): `ydCoinStep`;
* `ric_ydEntry`: the prologue: the arguments into the frame, `0 ≤ i < 3`, `c = D`, `S_ = 0`,
  `Ann = A_ * N_COINS`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

/-- The coin loop's stack: the bound `3` over the counter address `0x2a0`. -/
abbrev ydCStk (S : List B256) : List B256 := Nat.toB256 3 :: Nat.toB256 0x2a0 :: S

/-- After the coin loop, on naturals: the last `c` step, `b`, and the `y` loop from `y = D`. -/
def ydPostRes (c s D ann : Nat) : Option Nat := do
  let c' ← chkDiv (← chkMul c D) (← chkMul ann 3)
  let b' ← chkAdd s (← chkDiv D ann)
  loopYChk c' b' D 1 255 D

/-- One coin-loop iteration on naturals, `(c, S_)` in and out: coin `j` is skipped when it is
`i`, else `S_ += x; c = c * D / (x * N_COINS)`. -/
def ydCoinStep (i j x D : Nat) (cs : Nat × Nat) : Option (Nat × Nat) :=
  if i = j then some cs else do
    let s ← chkAdd cs.2 x
    let c ← chkDiv (← chkMul cs.1 D) (← chkMul x 3)
    some (c, s)

section Walk

variable {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M0 M : Mem} {G : Nat}
  {r : Seg}

theorem toB256_255 : Bytes.toB256 [0xff] + Bytes.toB256 [0x00] = Nat.toB256 255 := by decide

theorem toB256_0x320 : Bytes.toB256 [0x03, 0x20] = Nat.toB256 0x320 := by decide

theorem toB256_zero : Bytes.toB256 [0x00] = Nat.toB256 0 := by decide

-- SEGMENT: ydPost
/-- **After the coin loop**, inverted through the whole `y` loop. -/
theorem ric_ydPost {A i x0 x1 x2 D ρ c s ann xv cc w12 w13 w14 w15 : B256}
    (hF : WordFrame M0 M 0x140 (ydFrame A i x0 x1 x2 D ρ c s ann xv cc w12 w13 w14 w15))
    (run : SFunc.RunCut progYD sevm [] (St b (ydCStk S) M G) ydPost0 r) :
    ydOut b S M0 (ydPostRes c.toNat s.toNat D.toNat ann.toNat) r := by
  unfold ydPost0 ydPost at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_pop s1
  obtain ⟨G4, run⟩ := ric_pushMloadF hF 7 (by decide) rfl run
  obtain ⟨G5, run⟩ := ric_pushMloadF hF 5 (by decide) rfl run
  obtain ⟨hm1, G6, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨G7, run⟩ := ric_pushMloadF hF 9 (by decide) rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_push s1
  obtain ⟨hm2, G9, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨hd1, G10, run⟩ := ric_vyDivT vyRevertT_noOk run
  obtain ⟨G11, M1, hF1, run⟩ := ric_pushMstoreF hF 7 (by decide) (lt16 (by decide)) run
  obtain ⟨G12, run⟩ := ric_pushMloadF hF1 8 (by decide) rfl run
  obtain ⟨G13, run⟩ := ric_pushMloadF hF1 5 (by decide) rfl run
  obtain ⟨G14, run⟩ := ric_pushMloadF hF1 9 (by decide) rfl run
  obtain ⟨hd2, G15, run⟩ := ric_vyDivT vyRevertT_noOk run
  obtain ⟨ha1, G16, run⟩ := ric_vyAddT vyRevertT_noOk run
  obtain ⟨G17, M2, hF2, run⟩ := ric_pushMstoreF hF1 12 (by decide) (lt16 (by decide)) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_push s1
  obtain ⟨G19, M3, hF3, run⟩ := ric_pushMstoreF hF2 13 (by decide) (lt16 (by decide)) run
  obtain ⟨G20, run⟩ := ric_pushMloadF hF3 5 (by decide) rfl run
  obtain ⟨G21, M4, hF4, run⟩ := ric_pushMstoreF hF3 14 (by decide) (lt16 (by decide)) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_dup (w := Bytes.toB256 [0x00]) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G26, rfl⟩ := ri_dup (w := Bytes.toB256 [0x03, 0x20]) rfl s1
  obtain ⟨G27, M5, hF5, run⟩ := ric_mstoreF hF4 15 (by decide) (lt16 (by decide)) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_add s1
  rw [toB256_255, toB256_0x320] at run
  rw [toB256_zero] at hF5
  have hDlt := B256.toNat_lt D
  have hAt : ydAt b S M0 D ρ ((c * D) / (ann * Bytes.toB256 [0x03]))
      (s + D / ann) 0 D.toNat (St b (ydStk S) M5 G28) := by
    refine ⟨hDlt, M5, G28, A, i, x0, x1, x2, s, ann, xv, cc, Bytes.toB256 [0x00], rfl, ?_⟩
    rw [toB256_toNat]; exact hF5
  have hloop := ydLoop_sound 0 D.toNat _ r (by decide) hAt run
  have hres : ydPostRes c.toNat s.toNat D.toNat ann.toNat =
      ydLoop ((c * D) / (ann * Bytes.toB256 [0x03])) (s + D / ann) D (255 - 0) D.toNat := by
    have e3 : (3 : Nat) = (Bytes.toB256 [0x03]).toNat := by decide
    unfold ydPostRes ydLoop
    rw [e3, chkMul_toNat_of_nofm hm1, chkMul_toNat_of_nofm hm2]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [chkDiv_toNat_of_ne hd1, chkDiv_toNat_of_ne hd2]
    simp only [Option.bind_some]
    rw [chkAdd_toNat_of_lt ha1]
    simp only [Option.bind_some]
    rw [loopYChk_eq_fuelLoop]
  rw [hres]
  exact hloop

end Walk

/-- The accumulation `S_ += x; c = c * D / (x * N_COINS)` on naturals. -/
def ydAccN (c s x D : Nat) : Option (Nat × Nat) := do
  let s' ← chkAdd s x
  let c' ← chkDiv (← chkMul c D) (← chkMul x 3)
  some (c', s')

theorem ydCoinStep_ne {i j x D : Nat} {cs : Nat × Nat} (h : i ≠ j) :
    ydCoinStep i j x D cs = ydAccN cs.1 cs.2 x D := by
  unfold ydCoinStep ydAccN; rw [ite_eq_right h]

theorem ydCoinStep_eq {i x D : Nat} {cs : Nat × Nat} : ydCoinStep i i x D cs = some cs := by
  unfold ydCoinStep; rw [ite_eq_left rfl]

section Walk

variable {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M0 M : Mem} {G : Nat}
  {r : Seg} {ws : List B256}

theorem toB256_0x2a0 : Bytes.toB256 [0x02, 0xa0] = Nat.toB256 0x2a0 := by decide

-- SEGMENT: ydCoinTail
/-- **The coin-loop counter tail**, inverted up to its `JUMPI`. -/
theorem ric_ydCoinTail (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {j : Nat}
    (hj : ws[11]? = some (Nat.toB256 j)) (hj3 : j < 3) {jmp : SFunc}
    (run : SFunc.RunCut progYD sevm C (St b (ydCStk S) M G) (ydCoinTail jmp) r) :
    ∃ G' M', WordFrame M0 M' 0x140 (ws.set 11 (Nat.toB256 (j + 1))) ∧
      SFunc.RunCut progYD sevm C (St b (Bytes.toB256 [0x3a, 0x1b] ::
        B256.eqCheck (B256.eqCheck (Nat.toB256 3) (Nat.toB256 (j + 1))) 0 :: ydCStk S) M' G')
        jmp r := by
  unfold ydCoinTail at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_dup (w := Nat.toB256 0x2a0) rfl s1
  obtain ⟨G3, run⟩ := ric_mloadF hF 11 (by decide) hj run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_add s1
  rw [one_add_toB256 (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_dup (w := Nat.toB256 (j + 1)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_dup (w := Nat.toB256 0x2a0) rfl s1
  obtain ⟨G8, M1, hF1, run⟩ := ric_mstoreF hF 11 (by decide) (by rw [hlen]; decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_dup (w := Nat.toB256 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
  exact ⟨G12, M1, hF1, run⟩

/-- The tail of a non-final iteration: on to the next test at entry `k`. -/
theorem ric_ydCoinTail_next (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {j k : Nat}
    {g : SFunc} (hj : ws[11]? = some (Nat.toB256 j)) (hj3 : j < 3) (hkC : k ∉ C)
    (hk : progYD[k]? = some g)
    (run : SFunc.RunCut progYD sevm C (St b (ydCStk S) M G)
      (ydCoinTail (.branchTo .undefined k)) r) :
    ∃ G' M', WordFrame M0 M' 0x140 (ws.set 11 (Nat.toB256 (j + 1))) ∧
      SFunc.RunCut progYD sevm C (St b (ydCStk S) M' G') g r := by
  obtain ⟨G1, M1, hF1, run⟩ := ric_ydCoinTail hF hlen hj hj3 run
  rcases ric_branchTo hkC hk run with ⟨-, G2, run⟩ | ⟨-, G2, run⟩
  · exact (ric_undefined run).elim
  · exact ⟨G2, M1, hF1, run⟩

/-- The tail of the final iteration: on to the post-loop `g`. -/
theorem ric_ydCoinTail_last (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {j : Nat}
    {g : SFunc} (hj : ws[11]? = some (Nat.toB256 j)) (hj3 : j < 3)
    (run : SFunc.RunCut progYD sevm C (St b (ydCStk S) M G) (ydCoinTail (.branch g .undefined))
      r) :
    ∃ G' M', WordFrame M0 M' 0x140 (ws.set 11 (Nat.toB256 (j + 1))) ∧
      SFunc.RunCut progYD sevm C (St b (ydCStk S) M' G') g r := by
  obtain ⟨G1, M1, hF1, run⟩ := ric_ydCoinTail hF hlen hj hj3 run
  rcases ric_branch run with ⟨-, G2, run⟩ | ⟨-, G2, run⟩
  · exact ⟨G2, M1, hF1, run⟩
  · exact (ric_undefined run).elim

-- SEGMENT: ydAcc
/-- **The coin-loop accumulation**, inverted: `ydAccN` on the frame's `c`, `S_`, `_x`, `D`. -/
theorem ric_ydAcc (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {c s x D : B256}
    (hc : ws[7]? = some c) (hs : ws[8]? = some s) (hx : ws[10]? = some x)
    (hD : ws[5]? = some D) {tail : SFunc}
    (run : SFunc.RunCut progYD sevm C (St b (ydCStk S) M G) (ydAcc tail) r) :
    ∃ G' M' c' s', ydAccN c.toNat s.toNat x.toNat D.toNat = some (c'.toNat, s'.toNat) ∧
      WordFrame M0 M' 0x140 ((ws.set 8 s').set 7 c') ∧
      SFunc.RunCut progYD sevm C (St b (ydCStk S) M' G') tail r := by
  unfold ydAcc at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_dup (w := Bytes.toB256 [0x02, 0x40]) rfl s1
  obtain ⟨G4, run⟩ := ric_mloadF hF 8 (by decide) hs run
  obtain ⟨G5, run⟩ := ric_pushMloadF hF 10 (by decide) hx run
  obtain ⟨ha1, G6, run⟩ := ric_vyAddT vyRevertT_noOk run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_dup (w := Bytes.toB256 [0x02, 0x40]) rfl s1
  obtain ⟨G8, M1, hF1, run⟩ := ric_mstoreF hF 8 (by decide) (by rw [hlen]; decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_pop s1
  have hc1 : (ws.set 8 (s + x))[7]? = some c := by rw [List.getElem?_set_ne (by decide)]; exact hc
  have hD1 : (ws.set 8 (s + x))[5]? = some D := by rw [List.getElem?_set_ne (by decide)]; exact hD
  have hx1 : (ws.set 8 (s + x))[10]? = some x := by
    rw [List.getElem?_set_ne (by decide)]; exact hx
  obtain ⟨G10, run⟩ := ric_pushMloadF hF1 7 (by decide) hc1 run
  obtain ⟨G11, run⟩ := ric_pushMloadF hF1 5 (by decide) hD1 run
  obtain ⟨hm1, G12, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨G13, run⟩ := ric_pushMloadF hF1 10 (by decide) hx1 run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨hm2, G15, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨hd, G16, run⟩ := ric_vyDivT vyRevertT_noOk run
  obtain ⟨G17, M2, hF2, run⟩ := ric_pushMstoreF hF1 7 (by decide)
    (by rw [List.length_set, hlen]; decide) run
  refine ⟨G17, M2, _, _, ?_, hF2, run⟩
  have e3 : (3 : Nat) = (Bytes.toB256 [0x03]).toNat := by decide
  unfold ydAccN
  rw [e3, chkAdd_toNat_of_lt ha1]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [chkMul_toNat_of_nofm hm1, chkMul_toNat_of_nofm hm2]
  simp only [Option.bind_some]
  rw [chkDiv_toNat_of_ne hd]
  simp only [Option.bind_some]

/-- The address of `xp[j]`, `0x180 + 32 j`, as the frame's slot `2 + j`. -/
theorem ydXpAddr {j : Nat} (hj : j < 3) :
    (Bytes.toB256 [0x20] * Nat.toB256 j + Bytes.toB256 [0x01, 0x80]).toNat =
      0x140 + 32 * (2 + j) := by
  rcases j with _ | _ | _ | j
  · decide
  · decide
  · decide
  · omega

-- SEGMENT: ydTest
/-- **The coin-loop test**, inverted: coin `j` is `i` (on to the tail `k2`), or `_x = xp[j]`
(on to the accumulation `k1`). -/
theorem ric_ydTest (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {i x : B256}
    {j k1 k2 : Nat} {g1 g2 : SFunc} (hi : ws[1]? = some i)
    (hj : ws[11]? = some (Nat.toB256 j)) (hj3 : j < 3) (hx : ws[2 + j]? = some x)
    (hk1C : k1 ∉ C) (hk2C : k2 ∉ C) (hk1 : progYD[k1]? = some g1)
    (hk2 : progYD[k2]? = some g2)
    (run : SFunc.RunCut progYD sevm C (St b (ydCStk S) M G) (ydTest k1 k2) r) :
    (i = Nat.toB256 j ∧ ∃ G', SFunc.RunCut progYD sevm C (St b (ydCStk S) M G') g2 r) ∨
      (i ≠ Nat.toB256 j ∧ ∃ G' M', WordFrame M0 M' 0x140 (ws.set 10 x) ∧
        SFunc.RunCut progYD sevm C (St b (ydCStk S) M' G') g1 r) := by
  unfold ydTest at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨G2, run⟩ := ric_pushMloadF hF 1 (by decide) hi run
  obtain ⟨G3, run⟩ := ric_pushMloadF hF 11 (by decide) hj run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_xor s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨hw, G7, run⟩ | ⟨hw, G7, run⟩
  · -- `i ≠ j`: load `xp[j]`
    have hne : i ≠ Nat.toB256 j := by
      intro he
      rw [he, (B256.xor_eq_zero_iff _ _).mpr rfl] at hw
      exact absurd hw (by decide)
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_push s1
    obtain ⟨G9, run⟩ := ric_pushMloadF hF 11 (by decide) hj run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_dup (w := Nat.toB256 j) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_lt s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_push s1
    rcases ric_branch run with ⟨-, G14, run⟩ | ⟨-, G14, run⟩
    · exact (ric_undefined run).elim
    obtain ⟨G15, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_mul s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_add s1
    obtain ⟨G19, run⟩ := ric_mloadF hF (2 + j) (ydXpAddr hj3) hx run
    obtain ⟨G20, M1, hF1, run⟩ := ric_pushMstoreF hF 10 (by decide) (by rw [hlen]; decide) run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_push s1
    obtain ⟨G22, run⟩ := ric_jump hk1C hk1 run
    exact .inr ⟨hne, G22, M1, hF1, run⟩
  · -- `i = j`: `continue`
    have heq : i = Nat.toB256 j := by
      have := eq_zero_of_iszero_ne_zero hw
      exact ((B256.xor_eq_zero_iff _ _).mp this).symm
    obtain ⟨G8, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
    obtain ⟨G10, run⟩ := ric_jump hk2C hk2 run
    exact .inl ⟨heq, G10, run⟩

end Walk

end Blanc.Lift.Curve3Pool
