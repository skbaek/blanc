import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceD1
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-!
# `remove_liquidity_imbalance` on the word carrier, part 4: the fee loop

The loop of lines 545–554 over the counter at `0x600`, unrolled: for coin `k`,
`xa_rli_feeA{k}` (the loop head `0x336e` → the branch join `0x3458`) computes `ideal = D1 *
old[k] / D0` and the `difference` (either branch), and `xa_rli_feeB{k}` (`0x3458` → the next
head, or past the loop for `k = 2`) computes `fees[k] = _fee * difference / FEE_DENOMINATOR`,
stores `balances[k] = new[k] - fees[k] * admin_fee / FEE_DENOMINATOR`, and sets `new[k] -=
fees[k]`. `RliFeeIter` collects the checks and values of one iteration, as `feeAt` reads them.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- `FEE_DENOMINATOR` as the runtime pushes it. -/
abbrev rliDen : B256 := Bytes.toB256 [0x02, 0x54, 0x0b, 0xe4, 0x00]

/-- The `difference` branch of one fee iteration. -/
def RliDif (I N dif : B256) : Prop := (N < I ∧ dif = I - N) ∨ (¬ N < I ∧ dif = N - I)

/-- The checks and values of one fee iteration over the stable words `F` (`_fee`), `AF`
(`admin_fee`), `D0`, `D1` and coin `k`'s old and new balances `B`, `N`: the fee `f`, the stored
balance and the new balance after the fee. -/
def RliFeeIter (F AF D0 D1 B N f stored aft : B256) : Prop :=
  D1.Nofm B ∧ D0 ≠ 0 ∧ ∃ dif, RliDif (D1 * B / D0) N dif ∧ F.Nofm dif ∧ f = F * dif / rliDen ∧
    f.Nofm AF ∧ ¬ N < f * AF / rliDen ∧ stored = N - f * AF / rliDen ∧ ¬ N < f ∧ aft = N - f

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}

-- SEGMENT: rliFeeA0
/-- **Fee iteration 0, up to the branch join** (`0x336e` → `0x3458`). -/
theorem xa_rli_feeA0 (hcode : sevm.code = code)
    {M : Mem} {D0 D1 T F AF A o0 o1 o2 m0 m1 m2  : B256}
    (hV : VW M [(0x600, Nat.toB256 0), (0x480, D1), (0x340, D0), (0x140, T), (0x1e0, F), (0x200, AF),
      (0x220, A), (0x280, o0), (0x2a0, o1), (0x2c0, o2), (0x2e0, m0), (0x300, m1), (0x320, m2)])
    (h : XAt sevm post 0x336e (St b [Bytes.toB256 [3], Bytes.toB256 [6, 0]] M G) L) :
    D1.Nofm o0 ∧ D0 ≠ 0 ∧ ∃ (dif : B256) (M' : Mem) (G' : Nat), RliDif (D1 * o0 / D0) m0 dif ∧
      XAt sevm post 0x3458 (St b [Bytes.toB256 [3], Bytes.toB256 [6, 0]] M' G') L ∧
      VW M' [(0x640, dif), (0x600, Nat.toB256 0), (0x480, D1), (0x340, D0), (0x140, T), (0x1e0, F),
      (0x200, AF), (0x220, A), (0x280, o0), (0x2a0, o1), (0x2c0, o2), (0x2e0, m0), (0x300, m1),
      (0x320, m2)] := by
  xa 2
  xl 0x3373 0x480  -- 3372 MLOAD
  xa 2
  xl 0x337a 0x600  -- 3379 MLOAD
  xa 4
  xji 0x3382 0x3386 hw
  · xdead
  clear hw
  xa 4
  xl 0x338c 0x280  -- 338b MLOAD
  xa 12
  xji 0x339b 0x339f hw
  · xdead
  have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xl 0x33ab 0x340  -- 33aa MLOAD
  xa 3
  xji 0x33b1 0x33b5 hw
  · xdead
  have hD0 := hw
  clear hw
  xa 8
  xsw 0x33c0 0x620  -- 33bf MSTORE
  xa 2
  xsw 0x33c6 0x640  -- 33c5 MSTORE
  xa 2
  xl 0x33cd 0x600  -- 33cc MLOAD
  xa 4
  xji 0x33d5 0x33d9 hw
  · xdead
  clear hw
  xa 4
  xl 0x33df 0x2e0  -- 33de MLOAD
  xs 0x33e2 (.push [0x06, 0x20] (by decide)) ri_push  -- 33df PUSH2 0x0620
  xl 0x33e3 0x620  -- 33e2 MLOAD
  xa 3
  refine ⟨hm1, hD0, ?_⟩
  xji 0x33e9 0x3422 hw
  · -- ideal > new
    have hgt := B256.lt_of_gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
    clear hw
    xs 0x33ec (.push [0x06, 0x20] (by decide)) ri_push  -- 33e9 PUSH2 0x0620
    xl 0x33ed 0x620  -- 33ec MLOAD
    xa 2
    xl 0x33f4 0x600  -- 33f3 MLOAD
    xa 4
    xji 0x33fc 0x3400 hw
    · xdead
    clear hw
    xa 4
    xl 0x3406 0x2e0  -- 3405 MLOAD
    xa 5
    xji 0x340e 0x3412 hw
    · xdead
    have hsub := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
    clear hw
    xa 9
    xsw 0x341e 0x640  -- 341d MSTORE
    xs 0x3421 (.push [0x34, 0x58] (by decide)) ri_push  -- 341e PUSH2 0x3458
    xjmp 0x3458  -- 3421 JUMP
    exact ⟨_, _, _, .inl ⟨hgt, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  · -- ideal ≤ new
    have hgt := gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
    clear hw
    xa 3
    xl 0x342a 0x600  -- 3429 MLOAD
    xa 4
    xji 0x3432 0x3436 hw
    · xdead
    clear hw
    xa 4
    xl 0x343c 0x2e0  -- 343b MLOAD
    xs 0x343f (.push [0x06, 0x20] (by decide)) ri_push  -- 343c PUSH2 0x0620
    xl 0x3440 0x620  -- 343f MLOAD
    xa 5
    xji 0x3448 0x344c hw
    · xdead
    have hsub := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
    clear hw
    xa 9
    xsw 0x3458 0x640  -- 3457 MSTORE
    exact ⟨_, _, _, .inr ⟨hgt, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩

-- SEGMENT: rliFeeB0
/-- **Fee iteration 0, from the branch join** (`0x3458` → `0x336e`). -/
theorem xa_rli_feeB0 (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {b0 : Devm} {σ : Stor} (hB : ExBase sevm b0 b σ)
    {M : Mem} {D0 D1 T F AF A o0 o1 o2 m0 m1 m2  dif : B256}
    (hV : VW M [(0x640, dif), (0x600, Nat.toB256 0), (0x480, D1), (0x340, D0), (0x140, T), (0x1e0, F),
      (0x200, AF), (0x220, A), (0x280, o0), (0x2a0, o1), (0x2c0, o2), (0x2e0, m0), (0x300, m1),
      (0x320, m2)])
    (h : XAt sevm post 0x3458 (St b [Bytes.toB256 [3], Bytes.toB256 [6, 0]] M G) L) :
    F.Nofm dif ∧ (F * dif / rliDen).Nofm AF ∧ ¬ m0 < F * dif / rliDen * AF / rliDen ∧
      ¬ m0 < F * dif / rliDen ∧
    ∃ (b' : Devm) (M' : Mem) (G' : Nat),
      ExBase sevm b0 b' (σ.set (balancesBase + Nat.toB256 0) (m0 - F * dif / rliDen * AF / rliDen)) ∧
      b'.logs = b.logs ∧ XAt sevm post 0x336e (St b' [Bytes.toB256 [3], Bytes.toB256 [6, 0]] M' G') L ∧
      VW M' [(0x600, Nat.toB256 1), (0x480, D1), (0x340, D0), (0x140, T), (0x1e0, F), (0x200, AF),
      (0x220, A), (0x280, o0), (0x2a0, o1), (0x2c0, o2), (0x2e0, m0 - F * dif / rliDen),
      (0x300, m1), (0x320, m2), (0x5a0, F * dif / rliDen)] := by
  xa 2
  xl 0x345d 0x1e0  -- 345c MLOAD
  xs 0x3460 (.push [0x06, 0x40] (by decide)) ri_push  -- 345d PUSH2 0x0640
  xl 0x3461 0x640  -- 3460 MLOAD
  xa 12
  xji 0x3470 0x3474 hw
  · xdead
  have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 12
  xji 0x3488 0x348c hw
  · xdead
  clear hw
  xa 9
  xl 0x349a 0x600  -- 3499 MLOAD
  xa 4
  xji 0x34a2 0x34a6 hw
  · xdead
  clear hw
  xa 4
  xsw 0x34ac 0x5a0  -- 34ab MSTORE
  xa 2
  xl 0x34b3 0x600  -- 34b2 MLOAD
  xa 4
  xji 0x34bb 0x34bf hw
  · xdead
  clear hw
  xa 4
  xl 0x34c5 0x2e0  -- 34c4 MLOAD
  xa 2
  xl 0x34cc 0x600  -- 34cb MLOAD
  xa 4
  xji 0x34d4 0x34d8 hw
  · xdead
  clear hw
  xa 4
  xl 0x34de 0x5a0  -- 34dd MLOAD
  xs 0x34e1 (.push [0x02, 0x00] (by decide)) ri_push  -- 34de PUSH2 0x0200
  xl 0x34e2 0x200  -- 34e1 MLOAD
  xa 12
  xji 0x34f1 0x34f5 hw
  · xdead
  have hm3 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 12
  xji 0x3509 0x350d hw
  · xdead
  clear hw
  xa 12
  xji 0x351c 0x3520 hw
  · xdead
  have hs3 := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xl 0x352c 0x600  -- 352b MLOAD
  xa 4
  xji 0x3534 0x3538 hw
  · xdead
  clear hw
  xa 3
  xsw 0x353e 0xc0  -- 353d MSTORE
  xa 2
  xk 0x3543 0xc0  -- 3542 SHA3
  xs 0x3544 (.reg .add) ri_add  -- 3543 ADD
  xw 0x3545 (.reg .sstore) ri_sstore  -- 3544 SSTORE
  xa 2
  xl 0x354c 0x600  -- 354b MLOAD
  xa 4
  xji 0x3554 0x3558 hw
  · xdead
  clear hw
  xa 5
  xl 0x355f 0x2e0  -- 355e MLOAD
  xa 2
  xl 0x3566 0x600  -- 3565 MLOAD
  xa 4
  xji 0x356e 0x3572 hw
  · xdead
  clear hw
  xa 4
  xl 0x3578 0x5a0  -- 3577 MLOAD
  xa 5
  xji 0x3580 0x3584 hw
  · xdead
  have hs4 := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xsw 0x358e 0x2e0  -- 358d MSTORE
  xa 3
  xl 0x3592 0x600  -- 3591 MLOAD
  xa 4
  xsw 0x3598 0x600  -- 3597 MSTORE
  xa 4
  xji 0x359f 0x336e hw
  · exact absurd hw (by decide)
  clear hw
  simp only [show Bytes.toB256 [1] = (1 : B256) from by decide, balancesBase_eq,
    show (1 : B256) + Nat.toB256 0 = Nat.toB256 1 from by decide] at h hV
  refine ⟨hm2, hm3, hs3, hs4, _, _, _, ⟨fun x => ?_, ?_, ?_, ?_⟩, ?_, h, hV.sub ?_⟩
  · rw [afterSstore_getStor_self, Stor.get_set_ite, Stor.get_set_ite, hB.stor]
  · rw [afterSstore_getCode, hB.code]
  · rw [afterSstore_output, hB.output]
  · exact hB.id.afterSstore _ _
  · rw [afterSstore_logs]
  · simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

-- SEGMENT: rliFeeA1
/-- **Fee iteration 1, up to the branch join** (`0x336e` → `0x3458`). -/
theorem xa_rli_feeA1 (hcode : sevm.code = code)
    {M : Mem} {D0 D1 T F AF A o0 o1 o2 m0 m1 m2 f0 : B256}
    (hV : VW M [(0x600, Nat.toB256 1), (0x480, D1), (0x340, D0), (0x140, T), (0x1e0, F), (0x200, AF),
      (0x220, A), (0x280, o0), (0x2a0, o1), (0x2c0, o2), (0x2e0, m0), (0x300, m1), (0x320, m2),
      (0x5a0, f0)])
    (h : XAt sevm post 0x336e (St b [Bytes.toB256 [3], Bytes.toB256 [6, 0]] M G) L) :
    D1.Nofm o1 ∧ D0 ≠ 0 ∧ ∃ (dif : B256) (M' : Mem) (G' : Nat), RliDif (D1 * o1 / D0) m1 dif ∧
      XAt sevm post 0x3458 (St b [Bytes.toB256 [3], Bytes.toB256 [6, 0]] M' G') L ∧
      VW M' [(0x640, dif), (0x600, Nat.toB256 1), (0x480, D1), (0x340, D0), (0x140, T), (0x1e0, F),
      (0x200, AF), (0x220, A), (0x280, o0), (0x2a0, o1), (0x2c0, o2), (0x2e0, m0), (0x300, m1),
      (0x320, m2), (0x5a0, f0)] := by
  xa 2
  xl 0x3373 0x480  -- 3372 MLOAD
  xa 2
  xl 0x337a 0x600  -- 3379 MLOAD
  xa 4
  xji 0x3382 0x3386 hw
  · xdead
  clear hw
  xa 4
  xl 0x338c 0x2a0  -- 338b MLOAD
  xa 12
  xji 0x339b 0x339f hw
  · xdead
  have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xl 0x33ab 0x340  -- 33aa MLOAD
  xa 3
  xji 0x33b1 0x33b5 hw
  · xdead
  have hD0 := hw
  clear hw
  xa 8
  xsw 0x33c0 0x620  -- 33bf MSTORE
  xa 2
  xsw 0x33c6 0x640  -- 33c5 MSTORE
  xa 2
  xl 0x33cd 0x600  -- 33cc MLOAD
  xa 4
  xji 0x33d5 0x33d9 hw
  · xdead
  clear hw
  xa 4
  xl 0x33df 0x300  -- 33de MLOAD
  xs 0x33e2 (.push [0x06, 0x20] (by decide)) ri_push  -- 33df PUSH2 0x0620
  xl 0x33e3 0x620  -- 33e2 MLOAD
  xa 3
  refine ⟨hm1, hD0, ?_⟩
  xji 0x33e9 0x3422 hw
  · -- ideal > new
    have hgt := B256.lt_of_gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
    clear hw
    xs 0x33ec (.push [0x06, 0x20] (by decide)) ri_push  -- 33e9 PUSH2 0x0620
    xl 0x33ed 0x620  -- 33ec MLOAD
    xa 2
    xl 0x33f4 0x600  -- 33f3 MLOAD
    xa 4
    xji 0x33fc 0x3400 hw
    · xdead
    clear hw
    xa 4
    xl 0x3406 0x300  -- 3405 MLOAD
    xa 5
    xji 0x340e 0x3412 hw
    · xdead
    have hsub := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
    clear hw
    xa 9
    xsw 0x341e 0x640  -- 341d MSTORE
    xs 0x3421 (.push [0x34, 0x58] (by decide)) ri_push  -- 341e PUSH2 0x3458
    xjmp 0x3458  -- 3421 JUMP
    exact ⟨_, _, _, .inl ⟨hgt, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  · -- ideal ≤ new
    have hgt := gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
    clear hw
    xa 3
    xl 0x342a 0x600  -- 3429 MLOAD
    xa 4
    xji 0x3432 0x3436 hw
    · xdead
    clear hw
    xa 4
    xl 0x343c 0x300  -- 343b MLOAD
    xs 0x343f (.push [0x06, 0x20] (by decide)) ri_push  -- 343c PUSH2 0x0620
    xl 0x3440 0x620  -- 343f MLOAD
    xa 5
    xji 0x3448 0x344c hw
    · xdead
    have hsub := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
    clear hw
    xa 9
    xsw 0x3458 0x640  -- 3457 MSTORE
    exact ⟨_, _, _, .inr ⟨hgt, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩

-- SEGMENT: rliFeeB1
/-- **Fee iteration 1, from the branch join** (`0x3458` → `0x336e`). -/
theorem xa_rli_feeB1 (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {b0 : Devm} {σ : Stor} (hB : ExBase sevm b0 b σ)
    {M : Mem} {D0 D1 T F AF A o0 o1 o2 m0 m1 m2 f0 dif : B256}
    (hV : VW M [(0x640, dif), (0x600, Nat.toB256 1), (0x480, D1), (0x340, D0), (0x140, T), (0x1e0, F),
      (0x200, AF), (0x220, A), (0x280, o0), (0x2a0, o1), (0x2c0, o2), (0x2e0, m0), (0x300, m1),
      (0x320, m2), (0x5a0, f0)])
    (h : XAt sevm post 0x3458 (St b [Bytes.toB256 [3], Bytes.toB256 [6, 0]] M G) L) :
    F.Nofm dif ∧ (F * dif / rliDen).Nofm AF ∧ ¬ m1 < F * dif / rliDen * AF / rliDen ∧
      ¬ m1 < F * dif / rliDen ∧
    ∃ (b' : Devm) (M' : Mem) (G' : Nat),
      ExBase sevm b0 b' (σ.set (balancesBase + Nat.toB256 1) (m1 - F * dif / rliDen * AF / rliDen)) ∧
      b'.logs = b.logs ∧ XAt sevm post 0x336e (St b' [Bytes.toB256 [3], Bytes.toB256 [6, 0]] M' G') L ∧
      VW M' [(0x600, Nat.toB256 2), (0x480, D1), (0x340, D0), (0x140, T), (0x1e0, F), (0x200, AF),
      (0x220, A), (0x280, o0), (0x2a0, o1), (0x2c0, o2), (0x2e0, m0),
      (0x300, m1 - F * dif / rliDen), (0x320, m2), (0x5a0, f0), (0x5c0, F * dif / rliDen)] := by
  xa 2
  xl 0x345d 0x1e0  -- 345c MLOAD
  xs 0x3460 (.push [0x06, 0x40] (by decide)) ri_push  -- 345d PUSH2 0x0640
  xl 0x3461 0x640  -- 3460 MLOAD
  xa 12
  xji 0x3470 0x3474 hw
  · xdead
  have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 12
  xji 0x3488 0x348c hw
  · xdead
  clear hw
  xa 9
  xl 0x349a 0x600  -- 3499 MLOAD
  xa 4
  xji 0x34a2 0x34a6 hw
  · xdead
  clear hw
  xa 4
  xsw 0x34ac 0x5c0  -- 34ab MSTORE
  xa 2
  xl 0x34b3 0x600  -- 34b2 MLOAD
  xa 4
  xji 0x34bb 0x34bf hw
  · xdead
  clear hw
  xa 4
  xl 0x34c5 0x300  -- 34c4 MLOAD
  xa 2
  xl 0x34cc 0x600  -- 34cb MLOAD
  xa 4
  xji 0x34d4 0x34d8 hw
  · xdead
  clear hw
  xa 4
  xl 0x34de 0x5c0  -- 34dd MLOAD
  xs 0x34e1 (.push [0x02, 0x00] (by decide)) ri_push  -- 34de PUSH2 0x0200
  xl 0x34e2 0x200  -- 34e1 MLOAD
  xa 12
  xji 0x34f1 0x34f5 hw
  · xdead
  have hm3 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 12
  xji 0x3509 0x350d hw
  · xdead
  clear hw
  xa 12
  xji 0x351c 0x3520 hw
  · xdead
  have hs3 := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xl 0x352c 0x600  -- 352b MLOAD
  xa 4
  xji 0x3534 0x3538 hw
  · xdead
  clear hw
  xa 3
  xsw 0x353e 0xc0  -- 353d MSTORE
  xa 2
  xk 0x3543 0xc0  -- 3542 SHA3
  xs 0x3544 (.reg .add) ri_add  -- 3543 ADD
  xw 0x3545 (.reg .sstore) ri_sstore  -- 3544 SSTORE
  xa 2
  xl 0x354c 0x600  -- 354b MLOAD
  xa 4
  xji 0x3554 0x3558 hw
  · xdead
  clear hw
  xa 5
  xl 0x355f 0x300  -- 355e MLOAD
  xa 2
  xl 0x3566 0x600  -- 3565 MLOAD
  xa 4
  xji 0x356e 0x3572 hw
  · xdead
  clear hw
  xa 4
  xl 0x3578 0x5c0  -- 3577 MLOAD
  xa 5
  xji 0x3580 0x3584 hw
  · xdead
  have hs4 := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xsw 0x358e 0x300  -- 358d MSTORE
  xa 3
  xl 0x3592 0x600  -- 3591 MLOAD
  xa 4
  xsw 0x3598 0x600  -- 3597 MSTORE
  xa 4
  xji 0x359f 0x336e hw
  · exact absurd hw (by decide)
  clear hw
  simp only [show Bytes.toB256 [1] = (1 : B256) from by decide, balancesBase_eq,
    show (1 : B256) + Nat.toB256 1 = Nat.toB256 2 from by decide] at h hV
  refine ⟨hm2, hm3, hs3, hs4, _, _, _, ⟨fun x => ?_, ?_, ?_, ?_⟩, ?_, h, hV.sub ?_⟩
  · rw [afterSstore_getStor_self, Stor.get_set_ite, Stor.get_set_ite, hB.stor]
  · rw [afterSstore_getCode, hB.code]
  · rw [afterSstore_output, hB.output]
  · exact hB.id.afterSstore _ _
  · rw [afterSstore_logs]
  · simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

-- SEGMENT: rliFeeA2
/-- **Fee iteration 2, up to the branch join** (`0x336e` → `0x3458`). -/
theorem xa_rli_feeA2 (hcode : sevm.code = code)
    {M : Mem} {D0 D1 T F AF A o0 o1 o2 m0 m1 m2 f0 f1 : B256}
    (hV : VW M [(0x600, Nat.toB256 2), (0x480, D1), (0x340, D0), (0x140, T), (0x1e0, F), (0x200, AF),
      (0x220, A), (0x280, o0), (0x2a0, o1), (0x2c0, o2), (0x2e0, m0), (0x300, m1), (0x320, m2),
      (0x5a0, f0), (0x5c0, f1)])
    (h : XAt sevm post 0x336e (St b [Bytes.toB256 [3], Bytes.toB256 [6, 0]] M G) L) :
    D1.Nofm o2 ∧ D0 ≠ 0 ∧ ∃ (dif : B256) (M' : Mem) (G' : Nat), RliDif (D1 * o2 / D0) m2 dif ∧
      XAt sevm post 0x3458 (St b [Bytes.toB256 [3], Bytes.toB256 [6, 0]] M' G') L ∧
      VW M' [(0x640, dif), (0x600, Nat.toB256 2), (0x480, D1), (0x340, D0), (0x140, T), (0x1e0, F),
      (0x200, AF), (0x220, A), (0x280, o0), (0x2a0, o1), (0x2c0, o2), (0x2e0, m0), (0x300, m1),
      (0x320, m2), (0x5a0, f0), (0x5c0, f1)] := by
  xa 2
  xl 0x3373 0x480  -- 3372 MLOAD
  xa 2
  xl 0x337a 0x600  -- 3379 MLOAD
  xa 4
  xji 0x3382 0x3386 hw
  · xdead
  clear hw
  xa 4
  xl 0x338c 0x2c0  -- 338b MLOAD
  xa 12
  xji 0x339b 0x339f hw
  · xdead
  have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xl 0x33ab 0x340  -- 33aa MLOAD
  xa 3
  xji 0x33b1 0x33b5 hw
  · xdead
  have hD0 := hw
  clear hw
  xa 8
  xsw 0x33c0 0x620  -- 33bf MSTORE
  xa 2
  xsw 0x33c6 0x640  -- 33c5 MSTORE
  xa 2
  xl 0x33cd 0x600  -- 33cc MLOAD
  xa 4
  xji 0x33d5 0x33d9 hw
  · xdead
  clear hw
  xa 4
  xl 0x33df 0x320  -- 33de MLOAD
  xs 0x33e2 (.push [0x06, 0x20] (by decide)) ri_push  -- 33df PUSH2 0x0620
  xl 0x33e3 0x620  -- 33e2 MLOAD
  xa 3
  refine ⟨hm1, hD0, ?_⟩
  xji 0x33e9 0x3422 hw
  · -- ideal > new
    have hgt := B256.lt_of_gtCheck_ne_zero (ne_of_eqCheck_eq_zero hw)
    clear hw
    xs 0x33ec (.push [0x06, 0x20] (by decide)) ri_push  -- 33e9 PUSH2 0x0620
    xl 0x33ed 0x620  -- 33ec MLOAD
    xa 2
    xl 0x33f4 0x600  -- 33f3 MLOAD
    xa 4
    xji 0x33fc 0x3400 hw
    · xdead
    clear hw
    xa 4
    xl 0x3406 0x320  -- 3405 MLOAD
    xa 5
    xji 0x340e 0x3412 hw
    · xdead
    have hsub := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
    clear hw
    xa 9
    xsw 0x341e 0x640  -- 341d MSTORE
    xs 0x3421 (.push [0x34, 0x58] (by decide)) ri_push  -- 341e PUSH2 0x3458
    xjmp 0x3458  -- 3421 JUMP
    exact ⟨_, _, _, .inl ⟨hgt, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  · -- ideal ≤ new
    have hgt := gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
    clear hw
    xa 3
    xl 0x342a 0x600  -- 3429 MLOAD
    xa 4
    xji 0x3432 0x3436 hw
    · xdead
    clear hw
    xa 4
    xl 0x343c 0x320  -- 343b MLOAD
    xs 0x343f (.push [0x06, 0x20] (by decide)) ri_push  -- 343c PUSH2 0x0620
    xl 0x3440 0x620  -- 343f MLOAD
    xa 5
    xji 0x3448 0x344c hw
    · xdead
    have hsub := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
    clear hw
    xa 9
    xsw 0x3458 0x640  -- 3457 MSTORE
    exact ⟨_, _, _, .inr ⟨hgt, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩

-- SEGMENT: rliFeeB2
/-- **Fee iteration 2, from the branch join** (`0x3458` → `0x35a2`). -/
theorem xa_rli_feeB2 (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {b0 : Devm} {σ : Stor} (hB : ExBase sevm b0 b σ)
    {M : Mem} {D0 D1 T F AF A o0 o1 o2 m0 m1 m2 f0 f1 dif : B256}
    (hV : VW M [(0x640, dif), (0x600, Nat.toB256 2), (0x480, D1), (0x340, D0), (0x140, T), (0x1e0, F),
      (0x200, AF), (0x220, A), (0x280, o0), (0x2a0, o1), (0x2c0, o2), (0x2e0, m0), (0x300, m1),
      (0x320, m2), (0x5a0, f0), (0x5c0, f1)])
    (h : XAt sevm post 0x3458 (St b [Bytes.toB256 [3], Bytes.toB256 [6, 0]] M G) L) :
    F.Nofm dif ∧ (F * dif / rliDen).Nofm AF ∧ ¬ m2 < F * dif / rliDen * AF / rliDen ∧
      ¬ m2 < F * dif / rliDen ∧
    ∃ (b' : Devm) (M' : Mem) (G' : Nat),
      ExBase sevm b0 b' (σ.set (balancesBase + Nat.toB256 2) (m2 - F * dif / rliDen * AF / rliDen)) ∧
      b'.logs = b.logs ∧ XAt sevm post 0x35a2 (St b' [] M' G') L ∧
      VW M' [(0x600, Nat.toB256 3), (0x480, D1), (0x340, D0), (0x140, T), (0x1e0, F), (0x200, AF),
      (0x220, A), (0x280, o0), (0x2a0, o1), (0x2c0, o2), (0x2e0, m0), (0x300, m1),
      (0x320, m2 - F * dif / rliDen), (0x5a0, f0), (0x5c0, f1), (0x5e0, F * dif / rliDen)] := by
  xa 2
  xl 0x345d 0x1e0  -- 345c MLOAD
  xs 0x3460 (.push [0x06, 0x40] (by decide)) ri_push  -- 345d PUSH2 0x0640
  xl 0x3461 0x640  -- 3460 MLOAD
  xa 12
  xji 0x3470 0x3474 hw
  · xdead
  have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 12
  xji 0x3488 0x348c hw
  · xdead
  clear hw
  xa 9
  xl 0x349a 0x600  -- 3499 MLOAD
  xa 4
  xji 0x34a2 0x34a6 hw
  · xdead
  clear hw
  xa 4
  xsw 0x34ac 0x5e0  -- 34ab MSTORE
  xa 2
  xl 0x34b3 0x600  -- 34b2 MLOAD
  xa 4
  xji 0x34bb 0x34bf hw
  · xdead
  clear hw
  xa 4
  xl 0x34c5 0x320  -- 34c4 MLOAD
  xa 2
  xl 0x34cc 0x600  -- 34cb MLOAD
  xa 4
  xji 0x34d4 0x34d8 hw
  · xdead
  clear hw
  xa 4
  xl 0x34de 0x5e0  -- 34dd MLOAD
  xs 0x34e1 (.push [0x02, 0x00] (by decide)) ri_push  -- 34de PUSH2 0x0200
  xl 0x34e2 0x200  -- 34e1 MLOAD
  xa 12
  xji 0x34f1 0x34f5 hw
  · xdead
  have hm3 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 12
  xji 0x3509 0x350d hw
  · xdead
  clear hw
  xa 12
  xji 0x351c 0x3520 hw
  · xdead
  have hs3 := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xl 0x352c 0x600  -- 352b MLOAD
  xa 4
  xji 0x3534 0x3538 hw
  · xdead
  clear hw
  xa 3
  xsw 0x353e 0xc0  -- 353d MSTORE
  xa 2
  xk 0x3543 0xc0  -- 3542 SHA3
  xs 0x3544 (.reg .add) ri_add  -- 3543 ADD
  xw 0x3545 (.reg .sstore) ri_sstore  -- 3544 SSTORE
  xa 2
  xl 0x354c 0x600  -- 354b MLOAD
  xa 4
  xji 0x3554 0x3558 hw
  · xdead
  clear hw
  xa 5
  xl 0x355f 0x320  -- 355e MLOAD
  xa 2
  xl 0x3566 0x600  -- 3565 MLOAD
  xa 4
  xji 0x356e 0x3572 hw
  · xdead
  clear hw
  xa 4
  xl 0x3578 0x5e0  -- 3577 MLOAD
  xa 5
  xji 0x3580 0x3584 hw
  · xdead
  have hs4 := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xsw 0x358e 0x320  -- 358d MSTORE
  xa 3
  xl 0x3592 0x600  -- 3591 MLOAD
  xa 4
  xsw 0x3598 0x600  -- 3597 MSTORE
  xa 4
  xji 0x359f 0x336e hw
  rotate_left
  · exact absurd hw (by decide)
  clear hw
  xa 3
  simp only [show Bytes.toB256 [1] = (1 : B256) from by decide, balancesBase_eq,
    show (1 : B256) + Nat.toB256 2 = Nat.toB256 3 from by decide] at h hV
  refine ⟨hm2, hm3, hs3, hs4, _, _, _, ⟨fun x => ?_, ?_, ?_, ?_⟩, ?_, h, hV.sub ?_⟩
  · rw [afterSstore_getStor_self, Stor.get_set_ite, Stor.get_set_ite, hB.stor]
  · rw [afterSstore_getCode, hB.code]
  · rw [afterSstore_output, hB.output]
  · exact hB.id.afterSstore _ _
  · rw [afterSstore_logs]
  · simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
