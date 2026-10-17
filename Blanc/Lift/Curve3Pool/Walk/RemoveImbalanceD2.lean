import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceFeeLoop

/-!
# `remove_liquidity_imbalance` on the word carrier, part 5: `D2` and the burn amount

`xa_rli_d2` (`0x35a2` → `0x3719`): the frame save of `[0x140, 0x680)`, `D2 = get_D_mem(new
balances after fees, amp)`, the restore, `token_amount = (D0 - D2) * token_supply / D0`
(checked), `assert token_amount != 0`, `token_amount += 1` (checked) and the slippage check
`token_amount <= max_burn_amount`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}

-- SEGMENT: rliD2
/-- **`D2` and the burn amount** (`0x35a2` → `0x3719`). -/
theorem xa_rli_d2 (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {M : Mem} {D0 D1 T F AF A o0 o1 o2 n0 n1 n2 f0 f1 f2 : B256}
    (hV : VW M ((0x600, Nat.toB256 3) :: [(0x480, D1), (0x340, D0), (0x140, T), (0x1e0, F), (0x200, AF), (0x220, A), (0x280, o0),
      (0x2a0, o1), (0x2c0, o2), (0x2e0, n0), (0x300, n1), (0x320, n2), (0x5a0, f0), (0x5c0, f1),
      (0x5e0, f2)]))
    (h : XAt sevm post 0x35a2 (St b [] M G) L) :
    ∃ (D2 : B256) (M' : Mem) (G' : Nat),
      getDMem ⟨n0.toNat, n1.toNat, n2.toNat⟩ A.toNat = some D2.toNat ∧ ¬ D0 < D2 ∧
      (D0 - D2).Nofm T ∧ D0 ≠ 0 ∧ (D0 - D2) * T / D0 ≠ 0 ∧
      ¬ (D0 - D2) * T / D0 + Bytes.toB256 [1] < (D0 - D2) * T / D0 ∧
      ¬ Sevm.dataWord sevm (Bytes.toB256 [0x64]) < (D0 - D2) * T / D0 + Bytes.toB256 [1] ∧
      XAt sevm post 0x3719 (St b [] M' G') L ∧
      VW M' [(0x780, (D0 - D2) * T / D0 + Bytes.toB256 [1]), (0x480, D1), (0x140, T),
        (0x5a0, f0), (0x5c0, f1), (0x5e0, f2)] := by
  xs 0x35a5 (.push [0x01, 0x40] (by decide)) ri_push  -- 35a2 PUSH2 0x0140
  xs 0x35a8 (.push [0x06, 0x80] (by decide)) ri_push  -- 35a5 PUSH2 0x0680
  xsw 0x35a9 0x680  -- 35a8 MSTORE
  have hF : Words _ [(0x480, D1), (0x340, D0), (0x140, T), (0x1e0, F), (0x200, AF), (0x220, A), (0x280, o0),
      (0x2a0, o1), (0x2c0, o2), (0x2e0, n0), (0x300, n1), (0x320, n2), (0x5a0, f0), (0x5c0, f1),
      (0x5e0, f2)] := hV.words.sub (by
    simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])
  -- the save loop over [0x140, 0x680)
  obtain ⟨ws, M1, _, hws, rfl, h, hV1⟩ := xa_saveV (H := 0x35a9)
    (t := ⟨0x06, 0x80, 0x06, 0x80, 0x35, 0xcb, 0x35, 0xa9⟩) (lo := 0x140) (n := 42) vsave
    (by decide) hV (by rfl) (by decide) (by decide) (by decide) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0x35cf (.push [0x06, 0xa0] (by decide)) ri_push  -- 35cc PUSH2 0x06a0
  xs 0x35d2 (.push [0x02, 0xe0] (by decide)) ri_push  -- 35cf PUSH2 0x02e0
  xs 0x35d3 (.reg (.dup 0)) (ri_dup (by rfl))  -- 35d2 DUP1
  xl 0x35d4 0x2e0  -- 35d3 MLOAD
  xs 0x35d5 (.reg (.dup 2)) (ri_dup (by rfl))  -- 35d4 DUP3
  xsw 0x35d6 0x6a0  -- 35d5 MSTORE
  xs 0x35d7 (.reg (.dup 0)) (ri_dup (by rfl))  -- 35d6 DUP1
  xs 0x35d9 (.push [0x20] (by decide)) ri_push  -- 35d7 PUSH1 0x20
  xs 0x35da (.reg .add) ri_add  -- 35d9 ADD
  xl 0x35db 0x300  -- 35da MLOAD
  xs 0x35dc (.reg (.dup 2)) (ri_dup (by rfl))  -- 35db DUP3
  xs 0x35de (.push [0x20] (by decide)) ri_push  -- 35dc PUSH1 0x20
  xs 0x35df (.reg .add) ri_add  -- 35de ADD
  xsw 0x35e0 0x6c0  -- 35df MSTORE
  xs 0x35e1 (.reg (.dup 0)) (ri_dup (by rfl))  -- 35e0 DUP1
  xs 0x35e3 (.push [0x40] (by decide)) ri_push  -- 35e1 PUSH1 0x40
  xs 0x35e4 (.reg .add) ri_add  -- 35e3 ADD
  xl 0x35e5 0x320  -- 35e4 MLOAD
  xs 0x35e6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 35e5 DUP3
  xs 0x35e8 (.push [0x40] (by decide)) ri_push  -- 35e6 PUSH1 0x40
  xs 0x35e9 (.reg .add) ri_add  -- 35e8 ADD
  xsw 0x35ea 0x6e0  -- 35e9 MSTORE
  xs 0x35eb (.reg .pop) ri_pop  -- 35ea POP
  xs 0x35ec (.reg .pop) ri_pop  -- 35eb POP
  xs 0x35ef (.push [0x02, 0x20] (by decide)) ri_push  -- 35ec PUSH2 0x0220
  xl 0x35f0 0x220  -- 35ef MLOAD
  xs 0x35f3 (.push [0x07, 0x00] (by decide)) ri_push  -- 35f0 PUSH2 0x0700
  xsw 0x35f4 0x700  -- 35f3 MSTORE
  xs 0x35f7 (.push [0x07, 0x00] (by decide)) ri_push  -- 35f4 PUSH2 0x0700
  xl 0x35f8 0x700  -- 35f7 MLOAD
  xs 0x35fb (.push [0x06, 0xe0] (by decide)) ri_push  -- 35f8 PUSH2 0x06e0
  xl 0x35fc 0x6e0  -- 35fb MLOAD
  xs 0x35ff (.push [0x06, 0xc0] (by decide)) ri_push  -- 35fc PUSH2 0x06c0
  xl 0x3600 0x6c0  -- 35ff MLOAD
  xs 0x3603 (.push [0x06, 0xa0] (by decide)) ri_push  -- 3600 PUSH2 0x06a0
  xl 0x3604 0x6a0  -- 3603 MLOAD
  xs 0x3606 (.push [0x06] (by decide)) ri_push  -- 3604 PUSH1 0x06
  cvpc 0x3607  -- 3606 PC
  xs 0x3608 (.reg .add) ri_add  -- 3607 ADD
  xs 0x360b (.push [0x07, 0xb7] (by decide)) ri_push  -- 3608 PUSH2 0x07b7
  xjmp 0x7b7  -- 360b JUMP
  obtain ⟨D2, M3, _, h, hD2, hV1⟩ := xa_vGetDMem hc hcode hfork hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xjd 0x360d  -- 360c JUMPDEST
  xs 0x3610 (.push [0x07, 0x60] (by decide)) ri_push  -- 360d PUSH2 0x0760
  xsw 0x3611 0x760  -- 3610 MSTORE
  xs 0x3614 (.push [0x06, 0x60] (by decide)) ri_push  -- 3611 PUSH2 0x0660
  xs 0x3617 (.push [0x06, 0x80] (by decide)) ri_push  -- 3614 PUSH2 0x0680
  xsw 0x3618 0x680  -- 3617 MSTORE
  -- the restore loop over [0x140, 0x680)
  rw [← List.append_nil (frameWords _ _ _).reverse] at h
  obtain ⟨M4, _, h, hV1⟩ := xa_restoreFrameV (H := 0x3618)
    (t := ⟨0x06, 0x80, 0x01, 0x40, 0x36, 0x3b, 0x36, 0x18⟩) (lo := 0x140) (n := 42) vrestore
    (by decide) (by decide) (by decide) hV (by rfl) (by decide) (by decide) hF (by
      intro o v hm
      refine ⟨(o - 0x140) / 32, ?_, ?_⟩ <;>
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm <;>
      rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide) h
  simp only [List.cons_append, List.nil_append] at hV1
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0x363f (.push [0x07, 0x60] (by decide)) ri_push  -- 363c PUSH2 0x0760
  xl 0x3640 0x760  -- 363f MLOAD
  xs 0x3643 (.push [0x06, 0x60] (by decide)) ri_push  -- 3640 PUSH2 0x0660
  xsw 0x3644 0x660  -- 3643 MSTORE
  xs 0x3647 (.push [0x03, 0x40] (by decide)) ri_push  -- 3644 PUSH2 0x0340
  xl 0x3648 0x340  -- 3647 MLOAD
  xs 0x364b (.push [0x06, 0x60] (by decide)) ri_push  -- 3648 PUSH2 0x0660
  xl 0x364c 0x660  -- 364b MLOAD
  xs 0x364d (.reg (.dup 0)) (ri_dup (by rfl))  -- 364c DUP1
  xs 0x364e (.reg (.dup 2)) (ri_dup (by rfl))  -- 364d DUP3
  xs 0x364f (.reg .lt) ri_lt  -- 364e LT
  xs 0x3650 (.reg .iszero) ri_iszero  -- 364f ISZERO
  xs 0x3653 (.push [0x36, 0x58] (by decide)) ri_push  -- 3650 PUSH2 0x3658
  xji 0x3654 0x3658 hw
  · xdead
  have hD02 := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x3659  -- 3658 JUMPDEST
  xs 0x365a (.reg (.dup 0)) (ri_dup (by rfl))  -- 3659 DUP1
  xs 0x365b (.reg (.dup 2)) (ri_dup (by rfl))  -- 365a DUP3
  xs 0x365c (.reg .sub) ri_sub  -- 365b SUB
  xs 0x365d (.reg (.swap 0)) (ri_swap (by rfl))  -- 365c SWAP1
  xs 0x365e (.reg .pop) ri_pop  -- 365d POP
  xs 0x365f (.reg (.swap 0)) (ri_swap (by rfl))  -- 365e SWAP1
  xs 0x3660 (.reg .pop) ri_pop  -- 365f POP
  xs 0x3663 (.push [0x01, 0x40] (by decide)) ri_push  -- 3660 PUSH2 0x0140
  xl 0x3664 0x140  -- 3663 MLOAD
  xs 0x3665 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3664 DUP1
  xs 0x3666 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3665 DUP3
  xs 0x3667 (.reg .mul) ri_mul  -- 3666 MUL
  xs 0x3668 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3667 DUP3
  xs 0x3669 (.reg .iszero) ri_iszero  -- 3668 ISZERO
  xs 0x366a (.reg (.dup 2)) (ri_dup (by rfl))  -- 3669 DUP3
  xs 0x366b (.reg (.dup 4)) (ri_dup (by rfl))  -- 366a DUP5
  xs 0x366c (.reg (.dup 3)) (ri_dup (by rfl))  -- 366b DUP4
  xs 0x366d (.reg .div) ri_div  -- 366c DIV
  xs 0x366e (.reg .eq) ri_eq  -- 366d EQ
  xs 0x366f (.reg .or) ri_or  -- 366e OR
  xs 0x3672 (.push [0x36, 0x77] (by decide)) ri_push  -- 366f PUSH2 0x3677
  xji 0x3673 0x3677 hw
  · xdead
  have hmT := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x3678  -- 3677 JUMPDEST
  xs 0x3679 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3678 DUP1
  xs 0x367a (.reg (.swap 0)) (ri_swap (by rfl))  -- 3679 SWAP1
  xs 0x367b (.reg .pop) ri_pop  -- 367a POP
  xs 0x367c (.reg (.swap 0)) (ri_swap (by rfl))  -- 367b SWAP1
  xs 0x367d (.reg .pop) ri_pop  -- 367c POP
  xs 0x367e (.reg (.swap 0)) (ri_swap (by rfl))  -- 367d SWAP1
  xs 0x367f (.reg .pop) ri_pop  -- 367e POP
  xs 0x3682 (.push [0x03, 0x40] (by decide)) ri_push  -- 367f PUSH2 0x0340
  xl 0x3683 0x340  -- 3682 MLOAD
  xs 0x3684 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3683 DUP1
  xs 0x3685 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3684 DUP1
  xs 0x3688 (.push [0x36, 0x8d] (by decide)) ri_push  -- 3685 PUSH2 0x368d
  xji 0x3689 0x368d hw
  · xdead
  have hD0 := hw
  clear hw
  xjd 0x368e  -- 368d JUMPDEST
  xs 0x368f (.reg (.dup 2)) (ri_dup (by rfl))  -- 368e DUP3
  xs 0x3690 (.reg .div) ri_div  -- 368f DIV
  xs 0x3691 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3690 SWAP1
  xs 0x3692 (.reg .pop) ri_pop  -- 3691 POP
  xs 0x3693 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3692 SWAP1
  xs 0x3694 (.reg .pop) ri_pop  -- 3693 POP
  xs 0x3697 (.push [0x07, 0x80] (by decide)) ri_push  -- 3694 PUSH2 0x0780
  xsw 0x3698 0x780  -- 3697 MSTORE
  xs 0x369a (.push [0x00] (by decide)) ri_push  -- 3698 PUSH1 0x00
  xs 0x369d (.push [0x07, 0x80] (by decide)) ri_push  -- 369a PUSH2 0x0780
  xl 0x369e 0x780  -- 369d MLOAD
  xs 0x369f (.reg .xor) ri_xor  -- 369e XOR
  xs 0x36a2 (.push [0x36, 0xa7] (by decide)) ri_push  -- 369f PUSH2 0x36a7
  xji 0x36a3 0x36a7 hw
  · xdead
  have hbn : (D0 - D2) * T / D0 ≠ 0 := by rw [zero_lit, B256.xor_zero] at hw; exact hw
  clear hw
  xjd 0x36a8  -- 36a7 JUMPDEST
  xs 0x36ab (.push [0x07, 0x80] (by decide)) ri_push  -- 36a8 PUSH2 0x0780
  xs 0x36ac (.reg (.dup 0)) (ri_dup (by rfl))  -- 36ab DUP1
  xl 0x36ad 0x780  -- 36ac MLOAD
  xs 0x36af (.push [0x01] (by decide)) ri_push  -- 36ad PUSH1 0x01
  xs 0x36b0 (.reg (.dup 1)) (ri_dup (by rfl))  -- 36af DUP2
  xs 0x36b1 (.reg (.dup 1)) (ri_dup (by rfl))  -- 36b0 DUP2
  xs 0x36b2 (.reg (.dup 3)) (ri_dup (by rfl))  -- 36b1 DUP4
  xs 0x36b3 (.reg .add) ri_add  -- 36b2 ADD
  xs 0x36b4 (.reg .lt) ri_lt  -- 36b3 LT
  xs 0x36b5 (.reg .iszero) ri_iszero  -- 36b4 ISZERO
  xs 0x36b8 (.push [0x36, 0xbd] (by decide)) ri_push  -- 36b5 PUSH2 0x36bd
  xji 0x36b9 0x36bd hw
  · xdead
  have hb1 := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x36be  -- 36bd JUMPDEST
  xs 0x36bf (.reg (.dup 0)) (ri_dup (by rfl))  -- 36be DUP1
  xs 0x36c0 (.reg (.dup 2)) (ri_dup (by rfl))  -- 36bf DUP3
  xs 0x36c1 (.reg .add) ri_add  -- 36c0 ADD
  xs 0x36c2 (.reg (.swap 0)) (ri_swap (by rfl))  -- 36c1 SWAP1
  xs 0x36c3 (.reg .pop) ri_pop  -- 36c2 POP
  xs 0x36c4 (.reg (.swap 0)) (ri_swap (by rfl))  -- 36c3 SWAP1
  xs 0x36c5 (.reg .pop) ri_pop  -- 36c4 POP
  xs 0x36c6 (.reg (.dup 1)) (ri_dup (by rfl))  -- 36c5 DUP2
  xsw 0x36c7 0x780  -- 36c6 MSTORE
  xs 0x36c8 (.reg .pop) ri_pop  -- 36c7 POP
  xs 0x36cd (.push [0x08, 0xc3, 0x79, 0xa0] (by decide)) ri_push  -- 36c8 PUSH4 0x08c379a0
  xs 0x36d0 (.push [0x07, 0xa0] (by decide)) ri_push  -- 36cd PUSH2 0x07a0
  xsw 0x36d1 0x7a0  -- 36d0 MSTORE
  xs 0x36d3 (.push [0x20] (by decide)) ri_push  -- 36d1 PUSH1 0x20
  xs 0x36d6 (.push [0x07, 0xc0] (by decide)) ri_push  -- 36d3 PUSH2 0x07c0
  xsw 0x36d7 0x7c0  -- 36d6 MSTORE
  xs 0x36d9 (.push [0x14] (by decide)) ri_push  -- 36d7 PUSH1 0x14
  xs 0x36dc (.push [0x07, 0xe0] (by decide)) ri_push  -- 36d9 PUSH2 0x07e0
  xsw 0x36dd 0x7e0  -- 36dc MSTORE
  xs 0x36fe (.push [0x53, 0x6c, 0x69, 0x70, 0x70, 0x61, 0x67, 0x65, 0x20, 0x73, 0x63, 0x72, 0x65, 0x77, 0x65, 0x64, 0x20, 0x79, 0x6f, 0x75, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 36dd PUSH32 0x536c697070616765207363726577656420796f75000000000000000000000000
  xs 0x3701 (.push [0x08, 0x00] (by decide)) ri_push  -- 36fe PUSH2 0x0800
  xsw 0x3702 0x800  -- 3701 MSTORE
  xs 0x3705 (.push [0x07, 0xe0] (by decide)) ri_push  -- 3702 PUSH2 0x07e0
  xs 0x3706 (.reg .pop) ri_pop  -- 3705 POP
  xs 0x3708 (.push [0x64] (by decide)) ri_push  -- 3706 PUSH1 0x64
  xs 0x3709 (.reg .calldataload) ri_calldataload  -- 3708 CALLDATALOAD
  xs 0x370c (.push [0x07, 0x80] (by decide)) ri_push  -- 3709 PUSH2 0x0780
  xl 0x370d 0x780  -- 370c MLOAD
  xs 0x370e (.reg .gt) ri_gt  -- 370d GT
  xs 0x370f (.reg .iszero) ri_iszero  -- 370e ISZERO
  xs 0x3712 (.push [0x37, 0x19] (by decide)) ri_push  -- 370f PUSH2 0x3719
  xji 0x3713 0x3719 hw
  · xs 0x3715 (.push [0x64] (by decide)) ri_push
    xs 0x3718 (.push [0x07, 0xbc] (by decide)) ri_push
    xrevert
  have hslip := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
  clear hw
  refine ⟨D2, _, _, hD2, hD02, hmT, hD0, hbn, hb1, hslip, h, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
