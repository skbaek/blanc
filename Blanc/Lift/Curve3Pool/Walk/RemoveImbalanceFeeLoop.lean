import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceD1

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
  xjd 0x336f  -- 336e JUMPDEST
  xs 0x3372 (.push [0x04, 0x80] (by decide)) ri_push  -- 336f PUSH2 0x0480
  xl 0x3373 0x480  -- 3372 MLOAD
  xs 0x3376 (.push [0x02, 0x80] (by decide)) ri_push  -- 3373 PUSH2 0x0280
  xs 0x3379 (.push [0x06, 0x00] (by decide)) ri_push  -- 3376 PUSH2 0x0600
  xl 0x337a 0x600  -- 3379 MLOAD
  xs 0x337c (.push [0x03] (by decide)) ri_push  -- 337a PUSH1 0x03
  xs 0x337d (.reg (.dup 1)) (ri_dup (by rfl))  -- 337c DUP2
  xs 0x337e (.reg .lt) ri_lt  -- 337d LT
  xs 0x3381 (.push [0x33, 0x86] (by decide)) ri_push  -- 337e PUSH2 0x3386
  xji 0x3382 0x3386 hw
  · xdead
  clear hw
  xjd 0x3387  -- 3386 JUMPDEST
  xs 0x3389 (.push [0x20] (by decide)) ri_push  -- 3387 PUSH1 0x20
  xs 0x338a (.reg .mul) ri_mul  -- 3389 MUL
  xs 0x338b (.reg .add) ri_add  -- 338a ADD
  xl 0x338c 0x280  -- 338b MLOAD
  xs 0x338d (.reg (.dup 0)) (ri_dup (by rfl))  -- 338c DUP1
  xs 0x338e (.reg (.dup 2)) (ri_dup (by rfl))  -- 338d DUP3
  xs 0x338f (.reg .mul) ri_mul  -- 338e MUL
  xs 0x3390 (.reg (.dup 2)) (ri_dup (by rfl))  -- 338f DUP3
  xs 0x3391 (.reg .iszero) ri_iszero  -- 3390 ISZERO
  xs 0x3392 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3391 DUP3
  xs 0x3393 (.reg (.dup 4)) (ri_dup (by rfl))  -- 3392 DUP5
  xs 0x3394 (.reg (.dup 3)) (ri_dup (by rfl))  -- 3393 DUP4
  xs 0x3395 (.reg .div) ri_div  -- 3394 DIV
  xs 0x3396 (.reg .eq) ri_eq  -- 3395 EQ
  xs 0x3397 (.reg .or) ri_or  -- 3396 OR
  xs 0x339a (.push [0x33, 0x9f] (by decide)) ri_push  -- 3397 PUSH2 0x339f
  xji 0x339b 0x339f hw
  · xdead
  have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x33a0  -- 339f JUMPDEST
  xs 0x33a1 (.reg (.dup 0)) (ri_dup (by rfl))  -- 33a0 DUP1
  xs 0x33a2 (.reg (.swap 0)) (ri_swap (by rfl))  -- 33a1 SWAP1
  xs 0x33a3 (.reg .pop) ri_pop  -- 33a2 POP
  xs 0x33a4 (.reg (.swap 0)) (ri_swap (by rfl))  -- 33a3 SWAP1
  xs 0x33a5 (.reg .pop) ri_pop  -- 33a4 POP
  xs 0x33a6 (.reg (.swap 0)) (ri_swap (by rfl))  -- 33a5 SWAP1
  xs 0x33a7 (.reg .pop) ri_pop  -- 33a6 POP
  xs 0x33aa (.push [0x03, 0x40] (by decide)) ri_push  -- 33a7 PUSH2 0x0340
  xl 0x33ab 0x340  -- 33aa MLOAD
  xs 0x33ac (.reg (.dup 0)) (ri_dup (by rfl))  -- 33ab DUP1
  xs 0x33ad (.reg (.dup 0)) (ri_dup (by rfl))  -- 33ac DUP1
  xs 0x33b0 (.push [0x33, 0xb5] (by decide)) ri_push  -- 33ad PUSH2 0x33b5
  xji 0x33b1 0x33b5 hw
  · xdead
  have hD0 := hw
  clear hw
  xjd 0x33b6  -- 33b5 JUMPDEST
  xs 0x33b7 (.reg (.dup 2)) (ri_dup (by rfl))  -- 33b6 DUP3
  xs 0x33b8 (.reg .div) ri_div  -- 33b7 DIV
  xs 0x33b9 (.reg (.swap 0)) (ri_swap (by rfl))  -- 33b8 SWAP1
  xs 0x33ba (.reg .pop) ri_pop  -- 33b9 POP
  xs 0x33bb (.reg (.swap 0)) (ri_swap (by rfl))  -- 33ba SWAP1
  xs 0x33bc (.reg .pop) ri_pop  -- 33bb POP
  xs 0x33bf (.push [0x06, 0x20] (by decide)) ri_push  -- 33bc PUSH2 0x0620
  xsw 0x33c0 0x620  -- 33bf MSTORE
  xs 0x33c2 (.push [0x00] (by decide)) ri_push  -- 33c0 PUSH1 0x00
  xs 0x33c5 (.push [0x06, 0x40] (by decide)) ri_push  -- 33c2 PUSH2 0x0640
  xsw 0x33c6 0x640  -- 33c5 MSTORE
  xs 0x33c9 (.push [0x02, 0xe0] (by decide)) ri_push  -- 33c6 PUSH2 0x02e0
  xs 0x33cc (.push [0x06, 0x00] (by decide)) ri_push  -- 33c9 PUSH2 0x0600
  xl 0x33cd 0x600  -- 33cc MLOAD
  xs 0x33cf (.push [0x03] (by decide)) ri_push  -- 33cd PUSH1 0x03
  xs 0x33d0 (.reg (.dup 1)) (ri_dup (by rfl))  -- 33cf DUP2
  xs 0x33d1 (.reg .lt) ri_lt  -- 33d0 LT
  xs 0x33d4 (.push [0x33, 0xd9] (by decide)) ri_push  -- 33d1 PUSH2 0x33d9
  xji 0x33d5 0x33d9 hw
  · xdead
  clear hw
  xjd 0x33da  -- 33d9 JUMPDEST
  xs 0x33dc (.push [0x20] (by decide)) ri_push  -- 33da PUSH1 0x20
  xs 0x33dd (.reg .mul) ri_mul  -- 33dc MUL
  xs 0x33de (.reg .add) ri_add  -- 33dd ADD
  xl 0x33df 0x2e0  -- 33de MLOAD
  xs 0x33e2 (.push [0x06, 0x20] (by decide)) ri_push  -- 33df PUSH2 0x0620
  xl 0x33e3 0x620  -- 33e2 MLOAD
  xs 0x33e4 (.reg .gt) ri_gt  -- 33e3 GT
  xs 0x33e5 (.reg .iszero) ri_iszero  -- 33e4 ISZERO
  xs 0x33e8 (.push [0x34, 0x22] (by decide)) ri_push  -- 33e5 PUSH2 0x3422
  refine ⟨hm1, hD0, ?_⟩
  xji 0x33e9 0x3422 hw
  · -- ideal > new
    have hgt := gtCheck_ne_zero (eqCheck_eq_zero hw)
    clear hw
    xs 0x33ec (.push [0x06, 0x20] (by decide)) ri_push  -- 33e9 PUSH2 0x0620
    xl 0x33ed 0x620  -- 33ec MLOAD
    xs 0x33f0 (.push [0x02, 0xe0] (by decide)) ri_push  -- 33ed PUSH2 0x02e0
    xs 0x33f3 (.push [0x06, 0x00] (by decide)) ri_push  -- 33f0 PUSH2 0x0600
    xl 0x33f4 0x600  -- 33f3 MLOAD
    xs 0x33f6 (.push [0x03] (by decide)) ri_push  -- 33f4 PUSH1 0x03
    xs 0x33f7 (.reg (.dup 1)) (ri_dup (by rfl))  -- 33f6 DUP2
    xs 0x33f8 (.reg .lt) ri_lt  -- 33f7 LT
    xs 0x33fb (.push [0x34, 0x00] (by decide)) ri_push  -- 33f8 PUSH2 0x3400
    xji 0x33fc 0x3400 hw
    · xdead
    clear hw
    xjd 0x3401  -- 3400 JUMPDEST
    xs 0x3403 (.push [0x20] (by decide)) ri_push  -- 3401 PUSH1 0x20
    xs 0x3404 (.reg .mul) ri_mul  -- 3403 MUL
    xs 0x3405 (.reg .add) ri_add  -- 3404 ADD
    xl 0x3406 0x2e0  -- 3405 MLOAD
    xs 0x3407 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3406 DUP1
    xs 0x3408 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3407 DUP3
    xs 0x3409 (.reg .lt) ri_lt  -- 3408 LT
    xs 0x340a (.reg .iszero) ri_iszero  -- 3409 ISZERO
    xs 0x340d (.push [0x34, 0x12] (by decide)) ri_push  -- 340a PUSH2 0x3412
    xji 0x340e 0x3412 hw
    · xdead
    have hsub := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
    clear hw
    xjd 0x3413  -- 3412 JUMPDEST
    xs 0x3414 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3413 DUP1
    xs 0x3415 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3414 DUP3
    xs 0x3416 (.reg .sub) ri_sub  -- 3415 SUB
    xs 0x3417 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3416 SWAP1
    xs 0x3418 (.reg .pop) ri_pop  -- 3417 POP
    xs 0x3419 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3418 SWAP1
    xs 0x341a (.reg .pop) ri_pop  -- 3419 POP
    xs 0x341d (.push [0x06, 0x40] (by decide)) ri_push  -- 341a PUSH2 0x0640
    xsw 0x341e 0x640  -- 341d MSTORE
    xs 0x3421 (.push [0x34, 0x58] (by decide)) ri_push  -- 341e PUSH2 0x3458
    xjmp 0x3458  -- 3421 JUMP
    exact ⟨_, _, _, .inl ⟨hgt, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  · -- ideal ≤ new
    have hgt := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
    clear hw
    xjd 0x3423  -- 3422 JUMPDEST
    xs 0x3426 (.push [0x02, 0xe0] (by decide)) ri_push  -- 3423 PUSH2 0x02e0
    xs 0x3429 (.push [0x06, 0x00] (by decide)) ri_push  -- 3426 PUSH2 0x0600
    xl 0x342a 0x600  -- 3429 MLOAD
    xs 0x342c (.push [0x03] (by decide)) ri_push  -- 342a PUSH1 0x03
    xs 0x342d (.reg (.dup 1)) (ri_dup (by rfl))  -- 342c DUP2
    xs 0x342e (.reg .lt) ri_lt  -- 342d LT
    xs 0x3431 (.push [0x34, 0x36] (by decide)) ri_push  -- 342e PUSH2 0x3436
    xji 0x3432 0x3436 hw
    · xdead
    clear hw
    xjd 0x3437  -- 3436 JUMPDEST
    xs 0x3439 (.push [0x20] (by decide)) ri_push  -- 3437 PUSH1 0x20
    xs 0x343a (.reg .mul) ri_mul  -- 3439 MUL
    xs 0x343b (.reg .add) ri_add  -- 343a ADD
    xl 0x343c 0x2e0  -- 343b MLOAD
    xs 0x343f (.push [0x06, 0x20] (by decide)) ri_push  -- 343c PUSH2 0x0620
    xl 0x3440 0x620  -- 343f MLOAD
    xs 0x3441 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3440 DUP1
    xs 0x3442 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3441 DUP3
    xs 0x3443 (.reg .lt) ri_lt  -- 3442 LT
    xs 0x3444 (.reg .iszero) ri_iszero  -- 3443 ISZERO
    xs 0x3447 (.push [0x34, 0x4c] (by decide)) ri_push  -- 3444 PUSH2 0x344c
    xji 0x3448 0x344c hw
    · xdead
    have hsub := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
    clear hw
    xjd 0x344d  -- 344c JUMPDEST
    xs 0x344e (.reg (.dup 0)) (ri_dup (by rfl))  -- 344d DUP1
    xs 0x344f (.reg (.dup 2)) (ri_dup (by rfl))  -- 344e DUP3
    xs 0x3450 (.reg .sub) ri_sub  -- 344f SUB
    xs 0x3451 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3450 SWAP1
    xs 0x3452 (.reg .pop) ri_pop  -- 3451 POP
    xs 0x3453 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3452 SWAP1
    xs 0x3454 (.reg .pop) ri_pop  -- 3453 POP
    xs 0x3457 (.push [0x06, 0x40] (by decide)) ri_push  -- 3454 PUSH2 0x0640
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
  xjd 0x3459  -- 3458 JUMPDEST
  xs 0x345c (.push [0x01, 0xe0] (by decide)) ri_push  -- 3459 PUSH2 0x01e0
  xl 0x345d 0x1e0  -- 345c MLOAD
  xs 0x3460 (.push [0x06, 0x40] (by decide)) ri_push  -- 345d PUSH2 0x0640
  xl 0x3461 0x640  -- 3460 MLOAD
  xs 0x3462 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3461 DUP1
  xs 0x3463 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3462 DUP3
  xs 0x3464 (.reg .mul) ri_mul  -- 3463 MUL
  xs 0x3465 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3464 DUP3
  xs 0x3466 (.reg .iszero) ri_iszero  -- 3465 ISZERO
  xs 0x3467 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3466 DUP3
  xs 0x3468 (.reg (.dup 4)) (ri_dup (by rfl))  -- 3467 DUP5
  xs 0x3469 (.reg (.dup 3)) (ri_dup (by rfl))  -- 3468 DUP4
  xs 0x346a (.reg .div) ri_div  -- 3469 DIV
  xs 0x346b (.reg .eq) ri_eq  -- 346a EQ
  xs 0x346c (.reg .or) ri_or  -- 346b OR
  xs 0x346f (.push [0x34, 0x74] (by decide)) ri_push  -- 346c PUSH2 0x3474
  xji 0x3470 0x3474 hw
  · xdead
  have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x3475  -- 3474 JUMPDEST
  xs 0x3476 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3475 DUP1
  xs 0x3477 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3476 SWAP1
  xs 0x3478 (.reg .pop) ri_pop  -- 3477 POP
  xs 0x3479 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3478 SWAP1
  xs 0x347a (.reg .pop) ri_pop  -- 3479 POP
  xs 0x347b (.reg (.swap 0)) (ri_swap (by rfl))  -- 347a SWAP1
  xs 0x347c (.reg .pop) ri_pop  -- 347b POP
  xs 0x3482 (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push  -- 347c PUSH5 0x02540be400
  xs 0x3483 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3482 DUP1
  xs 0x3484 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3483 DUP1
  xs 0x3487 (.push [0x34, 0x8c] (by decide)) ri_push  -- 3484 PUSH2 0x348c
  xji 0x3488 0x348c hw
  · xdead
  clear hw
  xjd 0x348d  -- 348c JUMPDEST
  xs 0x348e (.reg (.dup 2)) (ri_dup (by rfl))  -- 348d DUP3
  xs 0x348f (.reg .div) ri_div  -- 348e DIV
  xs 0x3490 (.reg (.swap 0)) (ri_swap (by rfl))  -- 348f SWAP1
  xs 0x3491 (.reg .pop) ri_pop  -- 3490 POP
  xs 0x3492 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3491 SWAP1
  xs 0x3493 (.reg .pop) ri_pop  -- 3492 POP
  xs 0x3496 (.push [0x05, 0xa0] (by decide)) ri_push  -- 3493 PUSH2 0x05a0
  xs 0x3499 (.push [0x06, 0x00] (by decide)) ri_push  -- 3496 PUSH2 0x0600
  xl 0x349a 0x600  -- 3499 MLOAD
  xs 0x349c (.push [0x03] (by decide)) ri_push  -- 349a PUSH1 0x03
  xs 0x349d (.reg (.dup 1)) (ri_dup (by rfl))  -- 349c DUP2
  xs 0x349e (.reg .lt) ri_lt  -- 349d LT
  xs 0x34a1 (.push [0x34, 0xa6] (by decide)) ri_push  -- 349e PUSH2 0x34a6
  xji 0x34a2 0x34a6 hw
  · xdead
  clear hw
  xjd 0x34a7  -- 34a6 JUMPDEST
  xs 0x34a9 (.push [0x20] (by decide)) ri_push  -- 34a7 PUSH1 0x20
  xs 0x34aa (.reg .mul) ri_mul  -- 34a9 MUL
  xs 0x34ab (.reg .add) ri_add  -- 34aa ADD
  xsw 0x34ac 0x5a0  -- 34ab MSTORE
  xs 0x34af (.push [0x02, 0xe0] (by decide)) ri_push  -- 34ac PUSH2 0x02e0
  xs 0x34b2 (.push [0x06, 0x00] (by decide)) ri_push  -- 34af PUSH2 0x0600
  xl 0x34b3 0x600  -- 34b2 MLOAD
  xs 0x34b5 (.push [0x03] (by decide)) ri_push  -- 34b3 PUSH1 0x03
  xs 0x34b6 (.reg (.dup 1)) (ri_dup (by rfl))  -- 34b5 DUP2
  xs 0x34b7 (.reg .lt) ri_lt  -- 34b6 LT
  xs 0x34ba (.push [0x34, 0xbf] (by decide)) ri_push  -- 34b7 PUSH2 0x34bf
  xji 0x34bb 0x34bf hw
  · xdead
  clear hw
  xjd 0x34c0  -- 34bf JUMPDEST
  xs 0x34c2 (.push [0x20] (by decide)) ri_push  -- 34c0 PUSH1 0x20
  xs 0x34c3 (.reg .mul) ri_mul  -- 34c2 MUL
  xs 0x34c4 (.reg .add) ri_add  -- 34c3 ADD
  xl 0x34c5 0x2e0  -- 34c4 MLOAD
  xs 0x34c8 (.push [0x05, 0xa0] (by decide)) ri_push  -- 34c5 PUSH2 0x05a0
  xs 0x34cb (.push [0x06, 0x00] (by decide)) ri_push  -- 34c8 PUSH2 0x0600
  xl 0x34cc 0x600  -- 34cb MLOAD
  xs 0x34ce (.push [0x03] (by decide)) ri_push  -- 34cc PUSH1 0x03
  xs 0x34cf (.reg (.dup 1)) (ri_dup (by rfl))  -- 34ce DUP2
  xs 0x34d0 (.reg .lt) ri_lt  -- 34cf LT
  xs 0x34d3 (.push [0x34, 0xd8] (by decide)) ri_push  -- 34d0 PUSH2 0x34d8
  xji 0x34d4 0x34d8 hw
  · xdead
  clear hw
  xjd 0x34d9  -- 34d8 JUMPDEST
  xs 0x34db (.push [0x20] (by decide)) ri_push  -- 34d9 PUSH1 0x20
  xs 0x34dc (.reg .mul) ri_mul  -- 34db MUL
  xs 0x34dd (.reg .add) ri_add  -- 34dc ADD
  xl 0x34de 0x5a0  -- 34dd MLOAD
  xs 0x34e1 (.push [0x02, 0x00] (by decide)) ri_push  -- 34de PUSH2 0x0200
  xl 0x34e2 0x200  -- 34e1 MLOAD
  xs 0x34e3 (.reg (.dup 0)) (ri_dup (by rfl))  -- 34e2 DUP1
  xs 0x34e4 (.reg (.dup 2)) (ri_dup (by rfl))  -- 34e3 DUP3
  xs 0x34e5 (.reg .mul) ri_mul  -- 34e4 MUL
  xs 0x34e6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 34e5 DUP3
  xs 0x34e7 (.reg .iszero) ri_iszero  -- 34e6 ISZERO
  xs 0x34e8 (.reg (.dup 2)) (ri_dup (by rfl))  -- 34e7 DUP3
  xs 0x34e9 (.reg (.dup 4)) (ri_dup (by rfl))  -- 34e8 DUP5
  xs 0x34ea (.reg (.dup 3)) (ri_dup (by rfl))  -- 34e9 DUP4
  xs 0x34eb (.reg .div) ri_div  -- 34ea DIV
  xs 0x34ec (.reg .eq) ri_eq  -- 34eb EQ
  xs 0x34ed (.reg .or) ri_or  -- 34ec OR
  xs 0x34f0 (.push [0x34, 0xf5] (by decide)) ri_push  -- 34ed PUSH2 0x34f5
  xji 0x34f1 0x34f5 hw
  · xdead
  have hm3 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x34f6  -- 34f5 JUMPDEST
  xs 0x34f7 (.reg (.dup 0)) (ri_dup (by rfl))  -- 34f6 DUP1
  xs 0x34f8 (.reg (.swap 0)) (ri_swap (by rfl))  -- 34f7 SWAP1
  xs 0x34f9 (.reg .pop) ri_pop  -- 34f8 POP
  xs 0x34fa (.reg (.swap 0)) (ri_swap (by rfl))  -- 34f9 SWAP1
  xs 0x34fb (.reg .pop) ri_pop  -- 34fa POP
  xs 0x34fc (.reg (.swap 0)) (ri_swap (by rfl))  -- 34fb SWAP1
  xs 0x34fd (.reg .pop) ri_pop  -- 34fc POP
  xs 0x3503 (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push  -- 34fd PUSH5 0x02540be400
  xs 0x3504 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3503 DUP1
  xs 0x3505 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3504 DUP1
  xs 0x3508 (.push [0x35, 0x0d] (by decide)) ri_push  -- 3505 PUSH2 0x350d
  xji 0x3509 0x350d hw
  · xdead
  clear hw
  xjd 0x350e  -- 350d JUMPDEST
  xs 0x350f (.reg (.dup 2)) (ri_dup (by rfl))  -- 350e DUP3
  xs 0x3510 (.reg .div) ri_div  -- 350f DIV
  xs 0x3511 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3510 SWAP1
  xs 0x3512 (.reg .pop) ri_pop  -- 3511 POP
  xs 0x3513 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3512 SWAP1
  xs 0x3514 (.reg .pop) ri_pop  -- 3513 POP
  xs 0x3515 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3514 DUP1
  xs 0x3516 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3515 DUP3
  xs 0x3517 (.reg .lt) ri_lt  -- 3516 LT
  xs 0x3518 (.reg .iszero) ri_iszero  -- 3517 ISZERO
  xs 0x351b (.push [0x35, 0x20] (by decide)) ri_push  -- 3518 PUSH2 0x3520
  xji 0x351c 0x3520 hw
  · xdead
  have hs3 := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x3521  -- 3520 JUMPDEST
  xs 0x3522 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3521 DUP1
  xs 0x3523 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3522 DUP3
  xs 0x3524 (.reg .sub) ri_sub  -- 3523 SUB
  xs 0x3525 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3524 SWAP1
  xs 0x3526 (.reg .pop) ri_pop  -- 3525 POP
  xs 0x3527 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3526 SWAP1
  xs 0x3528 (.reg .pop) ri_pop  -- 3527 POP
  xs 0x352b (.push [0x06, 0x00] (by decide)) ri_push  -- 3528 PUSH2 0x0600
  xl 0x352c 0x600  -- 352b MLOAD
  xs 0x352e (.push [0x03] (by decide)) ri_push  -- 352c PUSH1 0x03
  xs 0x352f (.reg (.dup 1)) (ri_dup (by rfl))  -- 352e DUP2
  xs 0x3530 (.reg .lt) ri_lt  -- 352f LT
  xs 0x3533 (.push [0x35, 0x38] (by decide)) ri_push  -- 3530 PUSH2 0x3538
  xji 0x3534 0x3538 hw
  · xdead
  clear hw
  xjd 0x3539  -- 3538 JUMPDEST
  xs 0x353b (.push [0x01] (by decide)) ri_push  -- 3539 PUSH1 0x01
  xs 0x353d (.push [0xc0] (by decide)) ri_push  -- 353b PUSH1 0xc0
  xsw 0x353e 0xc0  -- 353d MSTORE
  xs 0x3540 (.push [0x20] (by decide)) ri_push  -- 353e PUSH1 0x20
  xs 0x3542 (.push [0xc0] (by decide)) ri_push  -- 3540 PUSH1 0xc0
  xk 0x3543 0xc0  -- 3542 SHA3
  xs 0x3544 (.reg .add) ri_add  -- 3543 ADD
  xw 0x3545 (.reg .sstore) ri_sstore  -- 3544 SSTORE
  xs 0x3548 (.push [0x02, 0xe0] (by decide)) ri_push  -- 3545 PUSH2 0x02e0
  xs 0x354b (.push [0x06, 0x00] (by decide)) ri_push  -- 3548 PUSH2 0x0600
  xl 0x354c 0x600  -- 354b MLOAD
  xs 0x354e (.push [0x03] (by decide)) ri_push  -- 354c PUSH1 0x03
  xs 0x354f (.reg (.dup 1)) (ri_dup (by rfl))  -- 354e DUP2
  xs 0x3550 (.reg .lt) ri_lt  -- 354f LT
  xs 0x3553 (.push [0x35, 0x58] (by decide)) ri_push  -- 3550 PUSH2 0x3558
  xji 0x3554 0x3558 hw
  · xdead
  clear hw
  xjd 0x3559  -- 3558 JUMPDEST
  xs 0x355b (.push [0x20] (by decide)) ri_push  -- 3559 PUSH1 0x20
  xs 0x355c (.reg .mul) ri_mul  -- 355b MUL
  xs 0x355d (.reg .add) ri_add  -- 355c ADD
  xs 0x355e (.reg (.dup 0)) (ri_dup (by rfl))  -- 355d DUP1
  xl 0x355f 0x2e0  -- 355e MLOAD
  xs 0x3562 (.push [0x05, 0xa0] (by decide)) ri_push  -- 355f PUSH2 0x05a0
  xs 0x3565 (.push [0x06, 0x00] (by decide)) ri_push  -- 3562 PUSH2 0x0600
  xl 0x3566 0x600  -- 3565 MLOAD
  xs 0x3568 (.push [0x03] (by decide)) ri_push  -- 3566 PUSH1 0x03
  xs 0x3569 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3568 DUP2
  xs 0x356a (.reg .lt) ri_lt  -- 3569 LT
  xs 0x356d (.push [0x35, 0x72] (by decide)) ri_push  -- 356a PUSH2 0x3572
  xji 0x356e 0x3572 hw
  · xdead
  clear hw
  xjd 0x3573  -- 3572 JUMPDEST
  xs 0x3575 (.push [0x20] (by decide)) ri_push  -- 3573 PUSH1 0x20
  xs 0x3576 (.reg .mul) ri_mul  -- 3575 MUL
  xs 0x3577 (.reg .add) ri_add  -- 3576 ADD
  xl 0x3578 0x5a0  -- 3577 MLOAD
  xs 0x3579 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3578 DUP1
  xs 0x357a (.reg (.dup 2)) (ri_dup (by rfl))  -- 3579 DUP3
  xs 0x357b (.reg .lt) ri_lt  -- 357a LT
  xs 0x357c (.reg .iszero) ri_iszero  -- 357b ISZERO
  xs 0x357f (.push [0x35, 0x84] (by decide)) ri_push  -- 357c PUSH2 0x3584
  xji 0x3580 0x3584 hw
  · xdead
  have hs4 := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x3585  -- 3584 JUMPDEST
  xs 0x3586 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3585 DUP1
  xs 0x3587 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3586 DUP3
  xs 0x3588 (.reg .sub) ri_sub  -- 3587 SUB
  xs 0x3589 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3588 SWAP1
  xs 0x358a (.reg .pop) ri_pop  -- 3589 POP
  xs 0x358b (.reg (.swap 0)) (ri_swap (by rfl))  -- 358a SWAP1
  xs 0x358c (.reg .pop) ri_pop  -- 358b POP
  xs 0x358d (.reg (.dup 1)) (ri_dup (by rfl))  -- 358c DUP2
  xsw 0x358e 0x2e0  -- 358d MSTORE
  xs 0x358f (.reg .pop) ri_pop  -- 358e POP
  xjd 0x3590  -- 358f JUMPDEST
  xs 0x3591 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3590 DUP2
  xl 0x3592 0x600  -- 3591 MLOAD
  xs 0x3594 (.push [0x01] (by decide)) ri_push  -- 3592 PUSH1 0x01
  xs 0x3595 (.reg .add) ri_add  -- 3594 ADD
  xs 0x3596 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3595 DUP1
  xs 0x3597 (.reg (.dup 3)) (ri_dup (by rfl))  -- 3596 DUP4
  xsw 0x3598 0x600  -- 3597 MSTORE
  xs 0x3599 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3598 DUP2
  xs 0x359a (.reg .eq) ri_eq  -- 3599 EQ
  xs 0x359b (.reg .iszero) ri_iszero  -- 359a ISZERO
  xs 0x359e (.push [0x33, 0x6e] (by decide)) ri_push  -- 359b PUSH2 0x336e
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
  xjd 0x336f  -- 336e JUMPDEST
  xs 0x3372 (.push [0x04, 0x80] (by decide)) ri_push  -- 336f PUSH2 0x0480
  xl 0x3373 0x480  -- 3372 MLOAD
  xs 0x3376 (.push [0x02, 0x80] (by decide)) ri_push  -- 3373 PUSH2 0x0280
  xs 0x3379 (.push [0x06, 0x00] (by decide)) ri_push  -- 3376 PUSH2 0x0600
  xl 0x337a 0x600  -- 3379 MLOAD
  xs 0x337c (.push [0x03] (by decide)) ri_push  -- 337a PUSH1 0x03
  xs 0x337d (.reg (.dup 1)) (ri_dup (by rfl))  -- 337c DUP2
  xs 0x337e (.reg .lt) ri_lt  -- 337d LT
  xs 0x3381 (.push [0x33, 0x86] (by decide)) ri_push  -- 337e PUSH2 0x3386
  xji 0x3382 0x3386 hw
  · xdead
  clear hw
  xjd 0x3387  -- 3386 JUMPDEST
  xs 0x3389 (.push [0x20] (by decide)) ri_push  -- 3387 PUSH1 0x20
  xs 0x338a (.reg .mul) ri_mul  -- 3389 MUL
  xs 0x338b (.reg .add) ri_add  -- 338a ADD
  xl 0x338c 0x2a0  -- 338b MLOAD
  xs 0x338d (.reg (.dup 0)) (ri_dup (by rfl))  -- 338c DUP1
  xs 0x338e (.reg (.dup 2)) (ri_dup (by rfl))  -- 338d DUP3
  xs 0x338f (.reg .mul) ri_mul  -- 338e MUL
  xs 0x3390 (.reg (.dup 2)) (ri_dup (by rfl))  -- 338f DUP3
  xs 0x3391 (.reg .iszero) ri_iszero  -- 3390 ISZERO
  xs 0x3392 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3391 DUP3
  xs 0x3393 (.reg (.dup 4)) (ri_dup (by rfl))  -- 3392 DUP5
  xs 0x3394 (.reg (.dup 3)) (ri_dup (by rfl))  -- 3393 DUP4
  xs 0x3395 (.reg .div) ri_div  -- 3394 DIV
  xs 0x3396 (.reg .eq) ri_eq  -- 3395 EQ
  xs 0x3397 (.reg .or) ri_or  -- 3396 OR
  xs 0x339a (.push [0x33, 0x9f] (by decide)) ri_push  -- 3397 PUSH2 0x339f
  xji 0x339b 0x339f hw
  · xdead
  have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x33a0  -- 339f JUMPDEST
  xs 0x33a1 (.reg (.dup 0)) (ri_dup (by rfl))  -- 33a0 DUP1
  xs 0x33a2 (.reg (.swap 0)) (ri_swap (by rfl))  -- 33a1 SWAP1
  xs 0x33a3 (.reg .pop) ri_pop  -- 33a2 POP
  xs 0x33a4 (.reg (.swap 0)) (ri_swap (by rfl))  -- 33a3 SWAP1
  xs 0x33a5 (.reg .pop) ri_pop  -- 33a4 POP
  xs 0x33a6 (.reg (.swap 0)) (ri_swap (by rfl))  -- 33a5 SWAP1
  xs 0x33a7 (.reg .pop) ri_pop  -- 33a6 POP
  xs 0x33aa (.push [0x03, 0x40] (by decide)) ri_push  -- 33a7 PUSH2 0x0340
  xl 0x33ab 0x340  -- 33aa MLOAD
  xs 0x33ac (.reg (.dup 0)) (ri_dup (by rfl))  -- 33ab DUP1
  xs 0x33ad (.reg (.dup 0)) (ri_dup (by rfl))  -- 33ac DUP1
  xs 0x33b0 (.push [0x33, 0xb5] (by decide)) ri_push  -- 33ad PUSH2 0x33b5
  xji 0x33b1 0x33b5 hw
  · xdead
  have hD0 := hw
  clear hw
  xjd 0x33b6  -- 33b5 JUMPDEST
  xs 0x33b7 (.reg (.dup 2)) (ri_dup (by rfl))  -- 33b6 DUP3
  xs 0x33b8 (.reg .div) ri_div  -- 33b7 DIV
  xs 0x33b9 (.reg (.swap 0)) (ri_swap (by rfl))  -- 33b8 SWAP1
  xs 0x33ba (.reg .pop) ri_pop  -- 33b9 POP
  xs 0x33bb (.reg (.swap 0)) (ri_swap (by rfl))  -- 33ba SWAP1
  xs 0x33bc (.reg .pop) ri_pop  -- 33bb POP
  xs 0x33bf (.push [0x06, 0x20] (by decide)) ri_push  -- 33bc PUSH2 0x0620
  xsw 0x33c0 0x620  -- 33bf MSTORE
  xs 0x33c2 (.push [0x00] (by decide)) ri_push  -- 33c0 PUSH1 0x00
  xs 0x33c5 (.push [0x06, 0x40] (by decide)) ri_push  -- 33c2 PUSH2 0x0640
  xsw 0x33c6 0x640  -- 33c5 MSTORE
  xs 0x33c9 (.push [0x02, 0xe0] (by decide)) ri_push  -- 33c6 PUSH2 0x02e0
  xs 0x33cc (.push [0x06, 0x00] (by decide)) ri_push  -- 33c9 PUSH2 0x0600
  xl 0x33cd 0x600  -- 33cc MLOAD
  xs 0x33cf (.push [0x03] (by decide)) ri_push  -- 33cd PUSH1 0x03
  xs 0x33d0 (.reg (.dup 1)) (ri_dup (by rfl))  -- 33cf DUP2
  xs 0x33d1 (.reg .lt) ri_lt  -- 33d0 LT
  xs 0x33d4 (.push [0x33, 0xd9] (by decide)) ri_push  -- 33d1 PUSH2 0x33d9
  xji 0x33d5 0x33d9 hw
  · xdead
  clear hw
  xjd 0x33da  -- 33d9 JUMPDEST
  xs 0x33dc (.push [0x20] (by decide)) ri_push  -- 33da PUSH1 0x20
  xs 0x33dd (.reg .mul) ri_mul  -- 33dc MUL
  xs 0x33de (.reg .add) ri_add  -- 33dd ADD
  xl 0x33df 0x300  -- 33de MLOAD
  xs 0x33e2 (.push [0x06, 0x20] (by decide)) ri_push  -- 33df PUSH2 0x0620
  xl 0x33e3 0x620  -- 33e2 MLOAD
  xs 0x33e4 (.reg .gt) ri_gt  -- 33e3 GT
  xs 0x33e5 (.reg .iszero) ri_iszero  -- 33e4 ISZERO
  xs 0x33e8 (.push [0x34, 0x22] (by decide)) ri_push  -- 33e5 PUSH2 0x3422
  refine ⟨hm1, hD0, ?_⟩
  xji 0x33e9 0x3422 hw
  · -- ideal > new
    have hgt := gtCheck_ne_zero (eqCheck_eq_zero hw)
    clear hw
    xs 0x33ec (.push [0x06, 0x20] (by decide)) ri_push  -- 33e9 PUSH2 0x0620
    xl 0x33ed 0x620  -- 33ec MLOAD
    xs 0x33f0 (.push [0x02, 0xe0] (by decide)) ri_push  -- 33ed PUSH2 0x02e0
    xs 0x33f3 (.push [0x06, 0x00] (by decide)) ri_push  -- 33f0 PUSH2 0x0600
    xl 0x33f4 0x600  -- 33f3 MLOAD
    xs 0x33f6 (.push [0x03] (by decide)) ri_push  -- 33f4 PUSH1 0x03
    xs 0x33f7 (.reg (.dup 1)) (ri_dup (by rfl))  -- 33f6 DUP2
    xs 0x33f8 (.reg .lt) ri_lt  -- 33f7 LT
    xs 0x33fb (.push [0x34, 0x00] (by decide)) ri_push  -- 33f8 PUSH2 0x3400
    xji 0x33fc 0x3400 hw
    · xdead
    clear hw
    xjd 0x3401  -- 3400 JUMPDEST
    xs 0x3403 (.push [0x20] (by decide)) ri_push  -- 3401 PUSH1 0x20
    xs 0x3404 (.reg .mul) ri_mul  -- 3403 MUL
    xs 0x3405 (.reg .add) ri_add  -- 3404 ADD
    xl 0x3406 0x300  -- 3405 MLOAD
    xs 0x3407 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3406 DUP1
    xs 0x3408 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3407 DUP3
    xs 0x3409 (.reg .lt) ri_lt  -- 3408 LT
    xs 0x340a (.reg .iszero) ri_iszero  -- 3409 ISZERO
    xs 0x340d (.push [0x34, 0x12] (by decide)) ri_push  -- 340a PUSH2 0x3412
    xji 0x340e 0x3412 hw
    · xdead
    have hsub := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
    clear hw
    xjd 0x3413  -- 3412 JUMPDEST
    xs 0x3414 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3413 DUP1
    xs 0x3415 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3414 DUP3
    xs 0x3416 (.reg .sub) ri_sub  -- 3415 SUB
    xs 0x3417 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3416 SWAP1
    xs 0x3418 (.reg .pop) ri_pop  -- 3417 POP
    xs 0x3419 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3418 SWAP1
    xs 0x341a (.reg .pop) ri_pop  -- 3419 POP
    xs 0x341d (.push [0x06, 0x40] (by decide)) ri_push  -- 341a PUSH2 0x0640
    xsw 0x341e 0x640  -- 341d MSTORE
    xs 0x3421 (.push [0x34, 0x58] (by decide)) ri_push  -- 341e PUSH2 0x3458
    xjmp 0x3458  -- 3421 JUMP
    exact ⟨_, _, _, .inl ⟨hgt, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  · -- ideal ≤ new
    have hgt := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
    clear hw
    xjd 0x3423  -- 3422 JUMPDEST
    xs 0x3426 (.push [0x02, 0xe0] (by decide)) ri_push  -- 3423 PUSH2 0x02e0
    xs 0x3429 (.push [0x06, 0x00] (by decide)) ri_push  -- 3426 PUSH2 0x0600
    xl 0x342a 0x600  -- 3429 MLOAD
    xs 0x342c (.push [0x03] (by decide)) ri_push  -- 342a PUSH1 0x03
    xs 0x342d (.reg (.dup 1)) (ri_dup (by rfl))  -- 342c DUP2
    xs 0x342e (.reg .lt) ri_lt  -- 342d LT
    xs 0x3431 (.push [0x34, 0x36] (by decide)) ri_push  -- 342e PUSH2 0x3436
    xji 0x3432 0x3436 hw
    · xdead
    clear hw
    xjd 0x3437  -- 3436 JUMPDEST
    xs 0x3439 (.push [0x20] (by decide)) ri_push  -- 3437 PUSH1 0x20
    xs 0x343a (.reg .mul) ri_mul  -- 3439 MUL
    xs 0x343b (.reg .add) ri_add  -- 343a ADD
    xl 0x343c 0x300  -- 343b MLOAD
    xs 0x343f (.push [0x06, 0x20] (by decide)) ri_push  -- 343c PUSH2 0x0620
    xl 0x3440 0x620  -- 343f MLOAD
    xs 0x3441 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3440 DUP1
    xs 0x3442 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3441 DUP3
    xs 0x3443 (.reg .lt) ri_lt  -- 3442 LT
    xs 0x3444 (.reg .iszero) ri_iszero  -- 3443 ISZERO
    xs 0x3447 (.push [0x34, 0x4c] (by decide)) ri_push  -- 3444 PUSH2 0x344c
    xji 0x3448 0x344c hw
    · xdead
    have hsub := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
    clear hw
    xjd 0x344d  -- 344c JUMPDEST
    xs 0x344e (.reg (.dup 0)) (ri_dup (by rfl))  -- 344d DUP1
    xs 0x344f (.reg (.dup 2)) (ri_dup (by rfl))  -- 344e DUP3
    xs 0x3450 (.reg .sub) ri_sub  -- 344f SUB
    xs 0x3451 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3450 SWAP1
    xs 0x3452 (.reg .pop) ri_pop  -- 3451 POP
    xs 0x3453 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3452 SWAP1
    xs 0x3454 (.reg .pop) ri_pop  -- 3453 POP
    xs 0x3457 (.push [0x06, 0x40] (by decide)) ri_push  -- 3454 PUSH2 0x0640
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
  xjd 0x3459  -- 3458 JUMPDEST
  xs 0x345c (.push [0x01, 0xe0] (by decide)) ri_push  -- 3459 PUSH2 0x01e0
  xl 0x345d 0x1e0  -- 345c MLOAD
  xs 0x3460 (.push [0x06, 0x40] (by decide)) ri_push  -- 345d PUSH2 0x0640
  xl 0x3461 0x640  -- 3460 MLOAD
  xs 0x3462 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3461 DUP1
  xs 0x3463 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3462 DUP3
  xs 0x3464 (.reg .mul) ri_mul  -- 3463 MUL
  xs 0x3465 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3464 DUP3
  xs 0x3466 (.reg .iszero) ri_iszero  -- 3465 ISZERO
  xs 0x3467 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3466 DUP3
  xs 0x3468 (.reg (.dup 4)) (ri_dup (by rfl))  -- 3467 DUP5
  xs 0x3469 (.reg (.dup 3)) (ri_dup (by rfl))  -- 3468 DUP4
  xs 0x346a (.reg .div) ri_div  -- 3469 DIV
  xs 0x346b (.reg .eq) ri_eq  -- 346a EQ
  xs 0x346c (.reg .or) ri_or  -- 346b OR
  xs 0x346f (.push [0x34, 0x74] (by decide)) ri_push  -- 346c PUSH2 0x3474
  xji 0x3470 0x3474 hw
  · xdead
  have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x3475  -- 3474 JUMPDEST
  xs 0x3476 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3475 DUP1
  xs 0x3477 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3476 SWAP1
  xs 0x3478 (.reg .pop) ri_pop  -- 3477 POP
  xs 0x3479 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3478 SWAP1
  xs 0x347a (.reg .pop) ri_pop  -- 3479 POP
  xs 0x347b (.reg (.swap 0)) (ri_swap (by rfl))  -- 347a SWAP1
  xs 0x347c (.reg .pop) ri_pop  -- 347b POP
  xs 0x3482 (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push  -- 347c PUSH5 0x02540be400
  xs 0x3483 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3482 DUP1
  xs 0x3484 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3483 DUP1
  xs 0x3487 (.push [0x34, 0x8c] (by decide)) ri_push  -- 3484 PUSH2 0x348c
  xji 0x3488 0x348c hw
  · xdead
  clear hw
  xjd 0x348d  -- 348c JUMPDEST
  xs 0x348e (.reg (.dup 2)) (ri_dup (by rfl))  -- 348d DUP3
  xs 0x348f (.reg .div) ri_div  -- 348e DIV
  xs 0x3490 (.reg (.swap 0)) (ri_swap (by rfl))  -- 348f SWAP1
  xs 0x3491 (.reg .pop) ri_pop  -- 3490 POP
  xs 0x3492 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3491 SWAP1
  xs 0x3493 (.reg .pop) ri_pop  -- 3492 POP
  xs 0x3496 (.push [0x05, 0xa0] (by decide)) ri_push  -- 3493 PUSH2 0x05a0
  xs 0x3499 (.push [0x06, 0x00] (by decide)) ri_push  -- 3496 PUSH2 0x0600
  xl 0x349a 0x600  -- 3499 MLOAD
  xs 0x349c (.push [0x03] (by decide)) ri_push  -- 349a PUSH1 0x03
  xs 0x349d (.reg (.dup 1)) (ri_dup (by rfl))  -- 349c DUP2
  xs 0x349e (.reg .lt) ri_lt  -- 349d LT
  xs 0x34a1 (.push [0x34, 0xa6] (by decide)) ri_push  -- 349e PUSH2 0x34a6
  xji 0x34a2 0x34a6 hw
  · xdead
  clear hw
  xjd 0x34a7  -- 34a6 JUMPDEST
  xs 0x34a9 (.push [0x20] (by decide)) ri_push  -- 34a7 PUSH1 0x20
  xs 0x34aa (.reg .mul) ri_mul  -- 34a9 MUL
  xs 0x34ab (.reg .add) ri_add  -- 34aa ADD
  xsw 0x34ac 0x5c0  -- 34ab MSTORE
  xs 0x34af (.push [0x02, 0xe0] (by decide)) ri_push  -- 34ac PUSH2 0x02e0
  xs 0x34b2 (.push [0x06, 0x00] (by decide)) ri_push  -- 34af PUSH2 0x0600
  xl 0x34b3 0x600  -- 34b2 MLOAD
  xs 0x34b5 (.push [0x03] (by decide)) ri_push  -- 34b3 PUSH1 0x03
  xs 0x34b6 (.reg (.dup 1)) (ri_dup (by rfl))  -- 34b5 DUP2
  xs 0x34b7 (.reg .lt) ri_lt  -- 34b6 LT
  xs 0x34ba (.push [0x34, 0xbf] (by decide)) ri_push  -- 34b7 PUSH2 0x34bf
  xji 0x34bb 0x34bf hw
  · xdead
  clear hw
  xjd 0x34c0  -- 34bf JUMPDEST
  xs 0x34c2 (.push [0x20] (by decide)) ri_push  -- 34c0 PUSH1 0x20
  xs 0x34c3 (.reg .mul) ri_mul  -- 34c2 MUL
  xs 0x34c4 (.reg .add) ri_add  -- 34c3 ADD
  xl 0x34c5 0x300  -- 34c4 MLOAD
  xs 0x34c8 (.push [0x05, 0xa0] (by decide)) ri_push  -- 34c5 PUSH2 0x05a0
  xs 0x34cb (.push [0x06, 0x00] (by decide)) ri_push  -- 34c8 PUSH2 0x0600
  xl 0x34cc 0x600  -- 34cb MLOAD
  xs 0x34ce (.push [0x03] (by decide)) ri_push  -- 34cc PUSH1 0x03
  xs 0x34cf (.reg (.dup 1)) (ri_dup (by rfl))  -- 34ce DUP2
  xs 0x34d0 (.reg .lt) ri_lt  -- 34cf LT
  xs 0x34d3 (.push [0x34, 0xd8] (by decide)) ri_push  -- 34d0 PUSH2 0x34d8
  xji 0x34d4 0x34d8 hw
  · xdead
  clear hw
  xjd 0x34d9  -- 34d8 JUMPDEST
  xs 0x34db (.push [0x20] (by decide)) ri_push  -- 34d9 PUSH1 0x20
  xs 0x34dc (.reg .mul) ri_mul  -- 34db MUL
  xs 0x34dd (.reg .add) ri_add  -- 34dc ADD
  xl 0x34de 0x5c0  -- 34dd MLOAD
  xs 0x34e1 (.push [0x02, 0x00] (by decide)) ri_push  -- 34de PUSH2 0x0200
  xl 0x34e2 0x200  -- 34e1 MLOAD
  xs 0x34e3 (.reg (.dup 0)) (ri_dup (by rfl))  -- 34e2 DUP1
  xs 0x34e4 (.reg (.dup 2)) (ri_dup (by rfl))  -- 34e3 DUP3
  xs 0x34e5 (.reg .mul) ri_mul  -- 34e4 MUL
  xs 0x34e6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 34e5 DUP3
  xs 0x34e7 (.reg .iszero) ri_iszero  -- 34e6 ISZERO
  xs 0x34e8 (.reg (.dup 2)) (ri_dup (by rfl))  -- 34e7 DUP3
  xs 0x34e9 (.reg (.dup 4)) (ri_dup (by rfl))  -- 34e8 DUP5
  xs 0x34ea (.reg (.dup 3)) (ri_dup (by rfl))  -- 34e9 DUP4
  xs 0x34eb (.reg .div) ri_div  -- 34ea DIV
  xs 0x34ec (.reg .eq) ri_eq  -- 34eb EQ
  xs 0x34ed (.reg .or) ri_or  -- 34ec OR
  xs 0x34f0 (.push [0x34, 0xf5] (by decide)) ri_push  -- 34ed PUSH2 0x34f5
  xji 0x34f1 0x34f5 hw
  · xdead
  have hm3 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x34f6  -- 34f5 JUMPDEST
  xs 0x34f7 (.reg (.dup 0)) (ri_dup (by rfl))  -- 34f6 DUP1
  xs 0x34f8 (.reg (.swap 0)) (ri_swap (by rfl))  -- 34f7 SWAP1
  xs 0x34f9 (.reg .pop) ri_pop  -- 34f8 POP
  xs 0x34fa (.reg (.swap 0)) (ri_swap (by rfl))  -- 34f9 SWAP1
  xs 0x34fb (.reg .pop) ri_pop  -- 34fa POP
  xs 0x34fc (.reg (.swap 0)) (ri_swap (by rfl))  -- 34fb SWAP1
  xs 0x34fd (.reg .pop) ri_pop  -- 34fc POP
  xs 0x3503 (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push  -- 34fd PUSH5 0x02540be400
  xs 0x3504 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3503 DUP1
  xs 0x3505 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3504 DUP1
  xs 0x3508 (.push [0x35, 0x0d] (by decide)) ri_push  -- 3505 PUSH2 0x350d
  xji 0x3509 0x350d hw
  · xdead
  clear hw
  xjd 0x350e  -- 350d JUMPDEST
  xs 0x350f (.reg (.dup 2)) (ri_dup (by rfl))  -- 350e DUP3
  xs 0x3510 (.reg .div) ri_div  -- 350f DIV
  xs 0x3511 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3510 SWAP1
  xs 0x3512 (.reg .pop) ri_pop  -- 3511 POP
  xs 0x3513 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3512 SWAP1
  xs 0x3514 (.reg .pop) ri_pop  -- 3513 POP
  xs 0x3515 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3514 DUP1
  xs 0x3516 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3515 DUP3
  xs 0x3517 (.reg .lt) ri_lt  -- 3516 LT
  xs 0x3518 (.reg .iszero) ri_iszero  -- 3517 ISZERO
  xs 0x351b (.push [0x35, 0x20] (by decide)) ri_push  -- 3518 PUSH2 0x3520
  xji 0x351c 0x3520 hw
  · xdead
  have hs3 := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x3521  -- 3520 JUMPDEST
  xs 0x3522 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3521 DUP1
  xs 0x3523 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3522 DUP3
  xs 0x3524 (.reg .sub) ri_sub  -- 3523 SUB
  xs 0x3525 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3524 SWAP1
  xs 0x3526 (.reg .pop) ri_pop  -- 3525 POP
  xs 0x3527 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3526 SWAP1
  xs 0x3528 (.reg .pop) ri_pop  -- 3527 POP
  xs 0x352b (.push [0x06, 0x00] (by decide)) ri_push  -- 3528 PUSH2 0x0600
  xl 0x352c 0x600  -- 352b MLOAD
  xs 0x352e (.push [0x03] (by decide)) ri_push  -- 352c PUSH1 0x03
  xs 0x352f (.reg (.dup 1)) (ri_dup (by rfl))  -- 352e DUP2
  xs 0x3530 (.reg .lt) ri_lt  -- 352f LT
  xs 0x3533 (.push [0x35, 0x38] (by decide)) ri_push  -- 3530 PUSH2 0x3538
  xji 0x3534 0x3538 hw
  · xdead
  clear hw
  xjd 0x3539  -- 3538 JUMPDEST
  xs 0x353b (.push [0x01] (by decide)) ri_push  -- 3539 PUSH1 0x01
  xs 0x353d (.push [0xc0] (by decide)) ri_push  -- 353b PUSH1 0xc0
  xsw 0x353e 0xc0  -- 353d MSTORE
  xs 0x3540 (.push [0x20] (by decide)) ri_push  -- 353e PUSH1 0x20
  xs 0x3542 (.push [0xc0] (by decide)) ri_push  -- 3540 PUSH1 0xc0
  xk 0x3543 0xc0  -- 3542 SHA3
  xs 0x3544 (.reg .add) ri_add  -- 3543 ADD
  xw 0x3545 (.reg .sstore) ri_sstore  -- 3544 SSTORE
  xs 0x3548 (.push [0x02, 0xe0] (by decide)) ri_push  -- 3545 PUSH2 0x02e0
  xs 0x354b (.push [0x06, 0x00] (by decide)) ri_push  -- 3548 PUSH2 0x0600
  xl 0x354c 0x600  -- 354b MLOAD
  xs 0x354e (.push [0x03] (by decide)) ri_push  -- 354c PUSH1 0x03
  xs 0x354f (.reg (.dup 1)) (ri_dup (by rfl))  -- 354e DUP2
  xs 0x3550 (.reg .lt) ri_lt  -- 354f LT
  xs 0x3553 (.push [0x35, 0x58] (by decide)) ri_push  -- 3550 PUSH2 0x3558
  xji 0x3554 0x3558 hw
  · xdead
  clear hw
  xjd 0x3559  -- 3558 JUMPDEST
  xs 0x355b (.push [0x20] (by decide)) ri_push  -- 3559 PUSH1 0x20
  xs 0x355c (.reg .mul) ri_mul  -- 355b MUL
  xs 0x355d (.reg .add) ri_add  -- 355c ADD
  xs 0x355e (.reg (.dup 0)) (ri_dup (by rfl))  -- 355d DUP1
  xl 0x355f 0x300  -- 355e MLOAD
  xs 0x3562 (.push [0x05, 0xa0] (by decide)) ri_push  -- 355f PUSH2 0x05a0
  xs 0x3565 (.push [0x06, 0x00] (by decide)) ri_push  -- 3562 PUSH2 0x0600
  xl 0x3566 0x600  -- 3565 MLOAD
  xs 0x3568 (.push [0x03] (by decide)) ri_push  -- 3566 PUSH1 0x03
  xs 0x3569 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3568 DUP2
  xs 0x356a (.reg .lt) ri_lt  -- 3569 LT
  xs 0x356d (.push [0x35, 0x72] (by decide)) ri_push  -- 356a PUSH2 0x3572
  xji 0x356e 0x3572 hw
  · xdead
  clear hw
  xjd 0x3573  -- 3572 JUMPDEST
  xs 0x3575 (.push [0x20] (by decide)) ri_push  -- 3573 PUSH1 0x20
  xs 0x3576 (.reg .mul) ri_mul  -- 3575 MUL
  xs 0x3577 (.reg .add) ri_add  -- 3576 ADD
  xl 0x3578 0x5c0  -- 3577 MLOAD
  xs 0x3579 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3578 DUP1
  xs 0x357a (.reg (.dup 2)) (ri_dup (by rfl))  -- 3579 DUP3
  xs 0x357b (.reg .lt) ri_lt  -- 357a LT
  xs 0x357c (.reg .iszero) ri_iszero  -- 357b ISZERO
  xs 0x357f (.push [0x35, 0x84] (by decide)) ri_push  -- 357c PUSH2 0x3584
  xji 0x3580 0x3584 hw
  · xdead
  have hs4 := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x3585  -- 3584 JUMPDEST
  xs 0x3586 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3585 DUP1
  xs 0x3587 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3586 DUP3
  xs 0x3588 (.reg .sub) ri_sub  -- 3587 SUB
  xs 0x3589 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3588 SWAP1
  xs 0x358a (.reg .pop) ri_pop  -- 3589 POP
  xs 0x358b (.reg (.swap 0)) (ri_swap (by rfl))  -- 358a SWAP1
  xs 0x358c (.reg .pop) ri_pop  -- 358b POP
  xs 0x358d (.reg (.dup 1)) (ri_dup (by rfl))  -- 358c DUP2
  xsw 0x358e 0x300  -- 358d MSTORE
  xs 0x358f (.reg .pop) ri_pop  -- 358e POP
  xjd 0x3590  -- 358f JUMPDEST
  xs 0x3591 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3590 DUP2
  xl 0x3592 0x600  -- 3591 MLOAD
  xs 0x3594 (.push [0x01] (by decide)) ri_push  -- 3592 PUSH1 0x01
  xs 0x3595 (.reg .add) ri_add  -- 3594 ADD
  xs 0x3596 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3595 DUP1
  xs 0x3597 (.reg (.dup 3)) (ri_dup (by rfl))  -- 3596 DUP4
  xsw 0x3598 0x600  -- 3597 MSTORE
  xs 0x3599 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3598 DUP2
  xs 0x359a (.reg .eq) ri_eq  -- 3599 EQ
  xs 0x359b (.reg .iszero) ri_iszero  -- 359a ISZERO
  xs 0x359e (.push [0x33, 0x6e] (by decide)) ri_push  -- 359b PUSH2 0x336e
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
  xjd 0x336f  -- 336e JUMPDEST
  xs 0x3372 (.push [0x04, 0x80] (by decide)) ri_push  -- 336f PUSH2 0x0480
  xl 0x3373 0x480  -- 3372 MLOAD
  xs 0x3376 (.push [0x02, 0x80] (by decide)) ri_push  -- 3373 PUSH2 0x0280
  xs 0x3379 (.push [0x06, 0x00] (by decide)) ri_push  -- 3376 PUSH2 0x0600
  xl 0x337a 0x600  -- 3379 MLOAD
  xs 0x337c (.push [0x03] (by decide)) ri_push  -- 337a PUSH1 0x03
  xs 0x337d (.reg (.dup 1)) (ri_dup (by rfl))  -- 337c DUP2
  xs 0x337e (.reg .lt) ri_lt  -- 337d LT
  xs 0x3381 (.push [0x33, 0x86] (by decide)) ri_push  -- 337e PUSH2 0x3386
  xji 0x3382 0x3386 hw
  · xdead
  clear hw
  xjd 0x3387  -- 3386 JUMPDEST
  xs 0x3389 (.push [0x20] (by decide)) ri_push  -- 3387 PUSH1 0x20
  xs 0x338a (.reg .mul) ri_mul  -- 3389 MUL
  xs 0x338b (.reg .add) ri_add  -- 338a ADD
  xl 0x338c 0x2c0  -- 338b MLOAD
  xs 0x338d (.reg (.dup 0)) (ri_dup (by rfl))  -- 338c DUP1
  xs 0x338e (.reg (.dup 2)) (ri_dup (by rfl))  -- 338d DUP3
  xs 0x338f (.reg .mul) ri_mul  -- 338e MUL
  xs 0x3390 (.reg (.dup 2)) (ri_dup (by rfl))  -- 338f DUP3
  xs 0x3391 (.reg .iszero) ri_iszero  -- 3390 ISZERO
  xs 0x3392 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3391 DUP3
  xs 0x3393 (.reg (.dup 4)) (ri_dup (by rfl))  -- 3392 DUP5
  xs 0x3394 (.reg (.dup 3)) (ri_dup (by rfl))  -- 3393 DUP4
  xs 0x3395 (.reg .div) ri_div  -- 3394 DIV
  xs 0x3396 (.reg .eq) ri_eq  -- 3395 EQ
  xs 0x3397 (.reg .or) ri_or  -- 3396 OR
  xs 0x339a (.push [0x33, 0x9f] (by decide)) ri_push  -- 3397 PUSH2 0x339f
  xji 0x339b 0x339f hw
  · xdead
  have hm1 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x33a0  -- 339f JUMPDEST
  xs 0x33a1 (.reg (.dup 0)) (ri_dup (by rfl))  -- 33a0 DUP1
  xs 0x33a2 (.reg (.swap 0)) (ri_swap (by rfl))  -- 33a1 SWAP1
  xs 0x33a3 (.reg .pop) ri_pop  -- 33a2 POP
  xs 0x33a4 (.reg (.swap 0)) (ri_swap (by rfl))  -- 33a3 SWAP1
  xs 0x33a5 (.reg .pop) ri_pop  -- 33a4 POP
  xs 0x33a6 (.reg (.swap 0)) (ri_swap (by rfl))  -- 33a5 SWAP1
  xs 0x33a7 (.reg .pop) ri_pop  -- 33a6 POP
  xs 0x33aa (.push [0x03, 0x40] (by decide)) ri_push  -- 33a7 PUSH2 0x0340
  xl 0x33ab 0x340  -- 33aa MLOAD
  xs 0x33ac (.reg (.dup 0)) (ri_dup (by rfl))  -- 33ab DUP1
  xs 0x33ad (.reg (.dup 0)) (ri_dup (by rfl))  -- 33ac DUP1
  xs 0x33b0 (.push [0x33, 0xb5] (by decide)) ri_push  -- 33ad PUSH2 0x33b5
  xji 0x33b1 0x33b5 hw
  · xdead
  have hD0 := hw
  clear hw
  xjd 0x33b6  -- 33b5 JUMPDEST
  xs 0x33b7 (.reg (.dup 2)) (ri_dup (by rfl))  -- 33b6 DUP3
  xs 0x33b8 (.reg .div) ri_div  -- 33b7 DIV
  xs 0x33b9 (.reg (.swap 0)) (ri_swap (by rfl))  -- 33b8 SWAP1
  xs 0x33ba (.reg .pop) ri_pop  -- 33b9 POP
  xs 0x33bb (.reg (.swap 0)) (ri_swap (by rfl))  -- 33ba SWAP1
  xs 0x33bc (.reg .pop) ri_pop  -- 33bb POP
  xs 0x33bf (.push [0x06, 0x20] (by decide)) ri_push  -- 33bc PUSH2 0x0620
  xsw 0x33c0 0x620  -- 33bf MSTORE
  xs 0x33c2 (.push [0x00] (by decide)) ri_push  -- 33c0 PUSH1 0x00
  xs 0x33c5 (.push [0x06, 0x40] (by decide)) ri_push  -- 33c2 PUSH2 0x0640
  xsw 0x33c6 0x640  -- 33c5 MSTORE
  xs 0x33c9 (.push [0x02, 0xe0] (by decide)) ri_push  -- 33c6 PUSH2 0x02e0
  xs 0x33cc (.push [0x06, 0x00] (by decide)) ri_push  -- 33c9 PUSH2 0x0600
  xl 0x33cd 0x600  -- 33cc MLOAD
  xs 0x33cf (.push [0x03] (by decide)) ri_push  -- 33cd PUSH1 0x03
  xs 0x33d0 (.reg (.dup 1)) (ri_dup (by rfl))  -- 33cf DUP2
  xs 0x33d1 (.reg .lt) ri_lt  -- 33d0 LT
  xs 0x33d4 (.push [0x33, 0xd9] (by decide)) ri_push  -- 33d1 PUSH2 0x33d9
  xji 0x33d5 0x33d9 hw
  · xdead
  clear hw
  xjd 0x33da  -- 33d9 JUMPDEST
  xs 0x33dc (.push [0x20] (by decide)) ri_push  -- 33da PUSH1 0x20
  xs 0x33dd (.reg .mul) ri_mul  -- 33dc MUL
  xs 0x33de (.reg .add) ri_add  -- 33dd ADD
  xl 0x33df 0x320  -- 33de MLOAD
  xs 0x33e2 (.push [0x06, 0x20] (by decide)) ri_push  -- 33df PUSH2 0x0620
  xl 0x33e3 0x620  -- 33e2 MLOAD
  xs 0x33e4 (.reg .gt) ri_gt  -- 33e3 GT
  xs 0x33e5 (.reg .iszero) ri_iszero  -- 33e4 ISZERO
  xs 0x33e8 (.push [0x34, 0x22] (by decide)) ri_push  -- 33e5 PUSH2 0x3422
  refine ⟨hm1, hD0, ?_⟩
  xji 0x33e9 0x3422 hw
  · -- ideal > new
    have hgt := gtCheck_ne_zero (eqCheck_eq_zero hw)
    clear hw
    xs 0x33ec (.push [0x06, 0x20] (by decide)) ri_push  -- 33e9 PUSH2 0x0620
    xl 0x33ed 0x620  -- 33ec MLOAD
    xs 0x33f0 (.push [0x02, 0xe0] (by decide)) ri_push  -- 33ed PUSH2 0x02e0
    xs 0x33f3 (.push [0x06, 0x00] (by decide)) ri_push  -- 33f0 PUSH2 0x0600
    xl 0x33f4 0x600  -- 33f3 MLOAD
    xs 0x33f6 (.push [0x03] (by decide)) ri_push  -- 33f4 PUSH1 0x03
    xs 0x33f7 (.reg (.dup 1)) (ri_dup (by rfl))  -- 33f6 DUP2
    xs 0x33f8 (.reg .lt) ri_lt  -- 33f7 LT
    xs 0x33fb (.push [0x34, 0x00] (by decide)) ri_push  -- 33f8 PUSH2 0x3400
    xji 0x33fc 0x3400 hw
    · xdead
    clear hw
    xjd 0x3401  -- 3400 JUMPDEST
    xs 0x3403 (.push [0x20] (by decide)) ri_push  -- 3401 PUSH1 0x20
    xs 0x3404 (.reg .mul) ri_mul  -- 3403 MUL
    xs 0x3405 (.reg .add) ri_add  -- 3404 ADD
    xl 0x3406 0x320  -- 3405 MLOAD
    xs 0x3407 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3406 DUP1
    xs 0x3408 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3407 DUP3
    xs 0x3409 (.reg .lt) ri_lt  -- 3408 LT
    xs 0x340a (.reg .iszero) ri_iszero  -- 3409 ISZERO
    xs 0x340d (.push [0x34, 0x12] (by decide)) ri_push  -- 340a PUSH2 0x3412
    xji 0x340e 0x3412 hw
    · xdead
    have hsub := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
    clear hw
    xjd 0x3413  -- 3412 JUMPDEST
    xs 0x3414 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3413 DUP1
    xs 0x3415 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3414 DUP3
    xs 0x3416 (.reg .sub) ri_sub  -- 3415 SUB
    xs 0x3417 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3416 SWAP1
    xs 0x3418 (.reg .pop) ri_pop  -- 3417 POP
    xs 0x3419 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3418 SWAP1
    xs 0x341a (.reg .pop) ri_pop  -- 3419 POP
    xs 0x341d (.push [0x06, 0x40] (by decide)) ri_push  -- 341a PUSH2 0x0640
    xsw 0x341e 0x640  -- 341d MSTORE
    xs 0x3421 (.push [0x34, 0x58] (by decide)) ri_push  -- 341e PUSH2 0x3458
    xjmp 0x3458  -- 3421 JUMP
    exact ⟨_, _, _, .inl ⟨hgt, rfl⟩, h, hV.sub (by
      simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])⟩
  · -- ideal ≤ new
    have hgt := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
    clear hw
    xjd 0x3423  -- 3422 JUMPDEST
    xs 0x3426 (.push [0x02, 0xe0] (by decide)) ri_push  -- 3423 PUSH2 0x02e0
    xs 0x3429 (.push [0x06, 0x00] (by decide)) ri_push  -- 3426 PUSH2 0x0600
    xl 0x342a 0x600  -- 3429 MLOAD
    xs 0x342c (.push [0x03] (by decide)) ri_push  -- 342a PUSH1 0x03
    xs 0x342d (.reg (.dup 1)) (ri_dup (by rfl))  -- 342c DUP2
    xs 0x342e (.reg .lt) ri_lt  -- 342d LT
    xs 0x3431 (.push [0x34, 0x36] (by decide)) ri_push  -- 342e PUSH2 0x3436
    xji 0x3432 0x3436 hw
    · xdead
    clear hw
    xjd 0x3437  -- 3436 JUMPDEST
    xs 0x3439 (.push [0x20] (by decide)) ri_push  -- 3437 PUSH1 0x20
    xs 0x343a (.reg .mul) ri_mul  -- 3439 MUL
    xs 0x343b (.reg .add) ri_add  -- 343a ADD
    xl 0x343c 0x320  -- 343b MLOAD
    xs 0x343f (.push [0x06, 0x20] (by decide)) ri_push  -- 343c PUSH2 0x0620
    xl 0x3440 0x620  -- 343f MLOAD
    xs 0x3441 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3440 DUP1
    xs 0x3442 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3441 DUP3
    xs 0x3443 (.reg .lt) ri_lt  -- 3442 LT
    xs 0x3444 (.reg .iszero) ri_iszero  -- 3443 ISZERO
    xs 0x3447 (.push [0x34, 0x4c] (by decide)) ri_push  -- 3444 PUSH2 0x344c
    xji 0x3448 0x344c hw
    · xdead
    have hsub := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
    clear hw
    xjd 0x344d  -- 344c JUMPDEST
    xs 0x344e (.reg (.dup 0)) (ri_dup (by rfl))  -- 344d DUP1
    xs 0x344f (.reg (.dup 2)) (ri_dup (by rfl))  -- 344e DUP3
    xs 0x3450 (.reg .sub) ri_sub  -- 344f SUB
    xs 0x3451 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3450 SWAP1
    xs 0x3452 (.reg .pop) ri_pop  -- 3451 POP
    xs 0x3453 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3452 SWAP1
    xs 0x3454 (.reg .pop) ri_pop  -- 3453 POP
    xs 0x3457 (.push [0x06, 0x40] (by decide)) ri_push  -- 3454 PUSH2 0x0640
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
  xjd 0x3459  -- 3458 JUMPDEST
  xs 0x345c (.push [0x01, 0xe0] (by decide)) ri_push  -- 3459 PUSH2 0x01e0
  xl 0x345d 0x1e0  -- 345c MLOAD
  xs 0x3460 (.push [0x06, 0x40] (by decide)) ri_push  -- 345d PUSH2 0x0640
  xl 0x3461 0x640  -- 3460 MLOAD
  xs 0x3462 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3461 DUP1
  xs 0x3463 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3462 DUP3
  xs 0x3464 (.reg .mul) ri_mul  -- 3463 MUL
  xs 0x3465 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3464 DUP3
  xs 0x3466 (.reg .iszero) ri_iszero  -- 3465 ISZERO
  xs 0x3467 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3466 DUP3
  xs 0x3468 (.reg (.dup 4)) (ri_dup (by rfl))  -- 3467 DUP5
  xs 0x3469 (.reg (.dup 3)) (ri_dup (by rfl))  -- 3468 DUP4
  xs 0x346a (.reg .div) ri_div  -- 3469 DIV
  xs 0x346b (.reg .eq) ri_eq  -- 346a EQ
  xs 0x346c (.reg .or) ri_or  -- 346b OR
  xs 0x346f (.push [0x34, 0x74] (by decide)) ri_push  -- 346c PUSH2 0x3474
  xji 0x3470 0x3474 hw
  · xdead
  have hm2 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x3475  -- 3474 JUMPDEST
  xs 0x3476 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3475 DUP1
  xs 0x3477 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3476 SWAP1
  xs 0x3478 (.reg .pop) ri_pop  -- 3477 POP
  xs 0x3479 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3478 SWAP1
  xs 0x347a (.reg .pop) ri_pop  -- 3479 POP
  xs 0x347b (.reg (.swap 0)) (ri_swap (by rfl))  -- 347a SWAP1
  xs 0x347c (.reg .pop) ri_pop  -- 347b POP
  xs 0x3482 (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push  -- 347c PUSH5 0x02540be400
  xs 0x3483 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3482 DUP1
  xs 0x3484 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3483 DUP1
  xs 0x3487 (.push [0x34, 0x8c] (by decide)) ri_push  -- 3484 PUSH2 0x348c
  xji 0x3488 0x348c hw
  · xdead
  clear hw
  xjd 0x348d  -- 348c JUMPDEST
  xs 0x348e (.reg (.dup 2)) (ri_dup (by rfl))  -- 348d DUP3
  xs 0x348f (.reg .div) ri_div  -- 348e DIV
  xs 0x3490 (.reg (.swap 0)) (ri_swap (by rfl))  -- 348f SWAP1
  xs 0x3491 (.reg .pop) ri_pop  -- 3490 POP
  xs 0x3492 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3491 SWAP1
  xs 0x3493 (.reg .pop) ri_pop  -- 3492 POP
  xs 0x3496 (.push [0x05, 0xa0] (by decide)) ri_push  -- 3493 PUSH2 0x05a0
  xs 0x3499 (.push [0x06, 0x00] (by decide)) ri_push  -- 3496 PUSH2 0x0600
  xl 0x349a 0x600  -- 3499 MLOAD
  xs 0x349c (.push [0x03] (by decide)) ri_push  -- 349a PUSH1 0x03
  xs 0x349d (.reg (.dup 1)) (ri_dup (by rfl))  -- 349c DUP2
  xs 0x349e (.reg .lt) ri_lt  -- 349d LT
  xs 0x34a1 (.push [0x34, 0xa6] (by decide)) ri_push  -- 349e PUSH2 0x34a6
  xji 0x34a2 0x34a6 hw
  · xdead
  clear hw
  xjd 0x34a7  -- 34a6 JUMPDEST
  xs 0x34a9 (.push [0x20] (by decide)) ri_push  -- 34a7 PUSH1 0x20
  xs 0x34aa (.reg .mul) ri_mul  -- 34a9 MUL
  xs 0x34ab (.reg .add) ri_add  -- 34aa ADD
  xsw 0x34ac 0x5e0  -- 34ab MSTORE
  xs 0x34af (.push [0x02, 0xe0] (by decide)) ri_push  -- 34ac PUSH2 0x02e0
  xs 0x34b2 (.push [0x06, 0x00] (by decide)) ri_push  -- 34af PUSH2 0x0600
  xl 0x34b3 0x600  -- 34b2 MLOAD
  xs 0x34b5 (.push [0x03] (by decide)) ri_push  -- 34b3 PUSH1 0x03
  xs 0x34b6 (.reg (.dup 1)) (ri_dup (by rfl))  -- 34b5 DUP2
  xs 0x34b7 (.reg .lt) ri_lt  -- 34b6 LT
  xs 0x34ba (.push [0x34, 0xbf] (by decide)) ri_push  -- 34b7 PUSH2 0x34bf
  xji 0x34bb 0x34bf hw
  · xdead
  clear hw
  xjd 0x34c0  -- 34bf JUMPDEST
  xs 0x34c2 (.push [0x20] (by decide)) ri_push  -- 34c0 PUSH1 0x20
  xs 0x34c3 (.reg .mul) ri_mul  -- 34c2 MUL
  xs 0x34c4 (.reg .add) ri_add  -- 34c3 ADD
  xl 0x34c5 0x320  -- 34c4 MLOAD
  xs 0x34c8 (.push [0x05, 0xa0] (by decide)) ri_push  -- 34c5 PUSH2 0x05a0
  xs 0x34cb (.push [0x06, 0x00] (by decide)) ri_push  -- 34c8 PUSH2 0x0600
  xl 0x34cc 0x600  -- 34cb MLOAD
  xs 0x34ce (.push [0x03] (by decide)) ri_push  -- 34cc PUSH1 0x03
  xs 0x34cf (.reg (.dup 1)) (ri_dup (by rfl))  -- 34ce DUP2
  xs 0x34d0 (.reg .lt) ri_lt  -- 34cf LT
  xs 0x34d3 (.push [0x34, 0xd8] (by decide)) ri_push  -- 34d0 PUSH2 0x34d8
  xji 0x34d4 0x34d8 hw
  · xdead
  clear hw
  xjd 0x34d9  -- 34d8 JUMPDEST
  xs 0x34db (.push [0x20] (by decide)) ri_push  -- 34d9 PUSH1 0x20
  xs 0x34dc (.reg .mul) ri_mul  -- 34db MUL
  xs 0x34dd (.reg .add) ri_add  -- 34dc ADD
  xl 0x34de 0x5e0  -- 34dd MLOAD
  xs 0x34e1 (.push [0x02, 0x00] (by decide)) ri_push  -- 34de PUSH2 0x0200
  xl 0x34e2 0x200  -- 34e1 MLOAD
  xs 0x34e3 (.reg (.dup 0)) (ri_dup (by rfl))  -- 34e2 DUP1
  xs 0x34e4 (.reg (.dup 2)) (ri_dup (by rfl))  -- 34e3 DUP3
  xs 0x34e5 (.reg .mul) ri_mul  -- 34e4 MUL
  xs 0x34e6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 34e5 DUP3
  xs 0x34e7 (.reg .iszero) ri_iszero  -- 34e6 ISZERO
  xs 0x34e8 (.reg (.dup 2)) (ri_dup (by rfl))  -- 34e7 DUP3
  xs 0x34e9 (.reg (.dup 4)) (ri_dup (by rfl))  -- 34e8 DUP5
  xs 0x34ea (.reg (.dup 3)) (ri_dup (by rfl))  -- 34e9 DUP4
  xs 0x34eb (.reg .div) ri_div  -- 34ea DIV
  xs 0x34ec (.reg .eq) ri_eq  -- 34eb EQ
  xs 0x34ed (.reg .or) ri_or  -- 34ec OR
  xs 0x34f0 (.push [0x34, 0xf5] (by decide)) ri_push  -- 34ed PUSH2 0x34f5
  xji 0x34f1 0x34f5 hw
  · xdead
  have hm3 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x34f6  -- 34f5 JUMPDEST
  xs 0x34f7 (.reg (.dup 0)) (ri_dup (by rfl))  -- 34f6 DUP1
  xs 0x34f8 (.reg (.swap 0)) (ri_swap (by rfl))  -- 34f7 SWAP1
  xs 0x34f9 (.reg .pop) ri_pop  -- 34f8 POP
  xs 0x34fa (.reg (.swap 0)) (ri_swap (by rfl))  -- 34f9 SWAP1
  xs 0x34fb (.reg .pop) ri_pop  -- 34fa POP
  xs 0x34fc (.reg (.swap 0)) (ri_swap (by rfl))  -- 34fb SWAP1
  xs 0x34fd (.reg .pop) ri_pop  -- 34fc POP
  xs 0x3503 (.push [0x02, 0x54, 0x0b, 0xe4, 0x00] (by decide)) ri_push  -- 34fd PUSH5 0x02540be400
  xs 0x3504 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3503 DUP1
  xs 0x3505 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3504 DUP1
  xs 0x3508 (.push [0x35, 0x0d] (by decide)) ri_push  -- 3505 PUSH2 0x350d
  xji 0x3509 0x350d hw
  · xdead
  clear hw
  xjd 0x350e  -- 350d JUMPDEST
  xs 0x350f (.reg (.dup 2)) (ri_dup (by rfl))  -- 350e DUP3
  xs 0x3510 (.reg .div) ri_div  -- 350f DIV
  xs 0x3511 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3510 SWAP1
  xs 0x3512 (.reg .pop) ri_pop  -- 3511 POP
  xs 0x3513 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3512 SWAP1
  xs 0x3514 (.reg .pop) ri_pop  -- 3513 POP
  xs 0x3515 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3514 DUP1
  xs 0x3516 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3515 DUP3
  xs 0x3517 (.reg .lt) ri_lt  -- 3516 LT
  xs 0x3518 (.reg .iszero) ri_iszero  -- 3517 ISZERO
  xs 0x351b (.push [0x35, 0x20] (by decide)) ri_push  -- 3518 PUSH2 0x3520
  xji 0x351c 0x3520 hw
  · xdead
  have hs3 := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x3521  -- 3520 JUMPDEST
  xs 0x3522 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3521 DUP1
  xs 0x3523 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3522 DUP3
  xs 0x3524 (.reg .sub) ri_sub  -- 3523 SUB
  xs 0x3525 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3524 SWAP1
  xs 0x3526 (.reg .pop) ri_pop  -- 3525 POP
  xs 0x3527 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3526 SWAP1
  xs 0x3528 (.reg .pop) ri_pop  -- 3527 POP
  xs 0x352b (.push [0x06, 0x00] (by decide)) ri_push  -- 3528 PUSH2 0x0600
  xl 0x352c 0x600  -- 352b MLOAD
  xs 0x352e (.push [0x03] (by decide)) ri_push  -- 352c PUSH1 0x03
  xs 0x352f (.reg (.dup 1)) (ri_dup (by rfl))  -- 352e DUP2
  xs 0x3530 (.reg .lt) ri_lt  -- 352f LT
  xs 0x3533 (.push [0x35, 0x38] (by decide)) ri_push  -- 3530 PUSH2 0x3538
  xji 0x3534 0x3538 hw
  · xdead
  clear hw
  xjd 0x3539  -- 3538 JUMPDEST
  xs 0x353b (.push [0x01] (by decide)) ri_push  -- 3539 PUSH1 0x01
  xs 0x353d (.push [0xc0] (by decide)) ri_push  -- 353b PUSH1 0xc0
  xsw 0x353e 0xc0  -- 353d MSTORE
  xs 0x3540 (.push [0x20] (by decide)) ri_push  -- 353e PUSH1 0x20
  xs 0x3542 (.push [0xc0] (by decide)) ri_push  -- 3540 PUSH1 0xc0
  xk 0x3543 0xc0  -- 3542 SHA3
  xs 0x3544 (.reg .add) ri_add  -- 3543 ADD
  xw 0x3545 (.reg .sstore) ri_sstore  -- 3544 SSTORE
  xs 0x3548 (.push [0x02, 0xe0] (by decide)) ri_push  -- 3545 PUSH2 0x02e0
  xs 0x354b (.push [0x06, 0x00] (by decide)) ri_push  -- 3548 PUSH2 0x0600
  xl 0x354c 0x600  -- 354b MLOAD
  xs 0x354e (.push [0x03] (by decide)) ri_push  -- 354c PUSH1 0x03
  xs 0x354f (.reg (.dup 1)) (ri_dup (by rfl))  -- 354e DUP2
  xs 0x3550 (.reg .lt) ri_lt  -- 354f LT
  xs 0x3553 (.push [0x35, 0x58] (by decide)) ri_push  -- 3550 PUSH2 0x3558
  xji 0x3554 0x3558 hw
  · xdead
  clear hw
  xjd 0x3559  -- 3558 JUMPDEST
  xs 0x355b (.push [0x20] (by decide)) ri_push  -- 3559 PUSH1 0x20
  xs 0x355c (.reg .mul) ri_mul  -- 355b MUL
  xs 0x355d (.reg .add) ri_add  -- 355c ADD
  xs 0x355e (.reg (.dup 0)) (ri_dup (by rfl))  -- 355d DUP1
  xl 0x355f 0x320  -- 355e MLOAD
  xs 0x3562 (.push [0x05, 0xa0] (by decide)) ri_push  -- 355f PUSH2 0x05a0
  xs 0x3565 (.push [0x06, 0x00] (by decide)) ri_push  -- 3562 PUSH2 0x0600
  xl 0x3566 0x600  -- 3565 MLOAD
  xs 0x3568 (.push [0x03] (by decide)) ri_push  -- 3566 PUSH1 0x03
  xs 0x3569 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3568 DUP2
  xs 0x356a (.reg .lt) ri_lt  -- 3569 LT
  xs 0x356d (.push [0x35, 0x72] (by decide)) ri_push  -- 356a PUSH2 0x3572
  xji 0x356e 0x3572 hw
  · xdead
  clear hw
  xjd 0x3573  -- 3572 JUMPDEST
  xs 0x3575 (.push [0x20] (by decide)) ri_push  -- 3573 PUSH1 0x20
  xs 0x3576 (.reg .mul) ri_mul  -- 3575 MUL
  xs 0x3577 (.reg .add) ri_add  -- 3576 ADD
  xl 0x3578 0x5e0  -- 3577 MLOAD
  xs 0x3579 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3578 DUP1
  xs 0x357a (.reg (.dup 2)) (ri_dup (by rfl))  -- 3579 DUP3
  xs 0x357b (.reg .lt) ri_lt  -- 357a LT
  xs 0x357c (.reg .iszero) ri_iszero  -- 357b ISZERO
  xs 0x357f (.push [0x35, 0x84] (by decide)) ri_push  -- 357c PUSH2 0x3584
  xji 0x3580 0x3584 hw
  · xdead
  have hs4 := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x3585  -- 3584 JUMPDEST
  xs 0x3586 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3585 DUP1
  xs 0x3587 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3586 DUP3
  xs 0x3588 (.reg .sub) ri_sub  -- 3587 SUB
  xs 0x3589 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3588 SWAP1
  xs 0x358a (.reg .pop) ri_pop  -- 3589 POP
  xs 0x358b (.reg (.swap 0)) (ri_swap (by rfl))  -- 358a SWAP1
  xs 0x358c (.reg .pop) ri_pop  -- 358b POP
  xs 0x358d (.reg (.dup 1)) (ri_dup (by rfl))  -- 358c DUP2
  xsw 0x358e 0x320  -- 358d MSTORE
  xs 0x358f (.reg .pop) ri_pop  -- 358e POP
  xjd 0x3590  -- 358f JUMPDEST
  xs 0x3591 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3590 DUP2
  xl 0x3592 0x600  -- 3591 MLOAD
  xs 0x3594 (.push [0x01] (by decide)) ri_push  -- 3592 PUSH1 0x01
  xs 0x3595 (.reg .add) ri_add  -- 3594 ADD
  xs 0x3596 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3595 DUP1
  xs 0x3597 (.reg (.dup 3)) (ri_dup (by rfl))  -- 3596 DUP4
  xsw 0x3598 0x600  -- 3597 MSTORE
  xs 0x3599 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3598 DUP2
  xs 0x359a (.reg .eq) ri_eq  -- 3599 EQ
  xs 0x359b (.reg .iszero) ri_iszero  -- 359a ISZERO
  xs 0x359e (.push [0x33, 0x6e] (by decide)) ri_push  -- 359b PUSH2 0x336e
  xji 0x359f 0x336e hw
  rotate_left
  · exact absurd hw (by decide)
  clear hw
  xjd 0x35a0
  xs 0x35a1 (.reg .pop) ri_pop
  xs 0x35a2 (.reg .pop) ri_pop
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
