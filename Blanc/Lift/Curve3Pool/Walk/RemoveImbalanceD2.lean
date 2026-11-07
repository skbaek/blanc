import Blanc.Lift.HistIdentityCall
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceFeeLoop
import Blanc.Lift.Curve3Pool.Walk.AutoStep

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
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
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
  xa 2
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
  xa 3
  xl 0x35d4 0x2e0  -- 35d3 MLOAD
  xs 0x35d5 (.reg (.dup 2)) (ri_dup (by rfl))  -- 35d4 DUP3
  xsw 0x35d6 0x6a0  -- 35d5 MSTORE
  xa 3
  xl 0x35db 0x300  -- 35da MLOAD
  xa 3
  xsw 0x35e0 0x6c0  -- 35df MSTORE
  xa 3
  xl 0x35e5 0x320  -- 35e4 MLOAD
  xa 3
  xsw 0x35ea 0x6e0  -- 35e9 MSTORE
  xa 3
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
  xa 2
  xjmp 0x7b7  -- 360b JUMP
  obtain ⟨D2, M3, _, h, hD2, hV1⟩ := xa_vGetDMem hc hcode hfork hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
  xsw 0x3611 0x760  -- 3610 MSTORE
  xa 2
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
  xa 5
  xji 0x3654 0x3658 hw
  · xdead
  have hD02 := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xl 0x3664 0x140  -- 3663 MLOAD
  xa 12
  xji 0x3673 0x3677 hw
  · xdead
  have hmT := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xl 0x3683 0x340  -- 3682 MLOAD
  xa 3
  xji 0x3689 0x368d hw
  · xdead
  have hD0 := hw
  clear hw
  xa 8
  xsw 0x3698 0x780  -- 3697 MSTORE
  xa 2
  xl 0x369e 0x780  -- 369d MLOAD
  xa 2
  xji 0x36a3 0x36a7 hw
  · xdead
  have hbn : (D0 - D2) * T / D0 ≠ 0 := by rw [zero_lit, B256.xor_zero] at hw; exact hw
  clear hw
  xa 3
  xl 0x36ad 0x780  -- 36ac MLOAD
  xa 8
  xji 0x36b9 0x36bd hw
  · xdead
  have hb1 := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xsw 0x36c7 0x780  -- 36c6 MSTORE
  xa 3
  xsw 0x36d1 0x7a0  -- 36d0 MSTORE
  xa 2
  xsw 0x36d7 0x7c0  -- 36d6 MSTORE
  xa 2
  xsw 0x36dd 0x7e0  -- 36dc MSTORE
  xa 2
  xsw 0x3702 0x800  -- 3701 MSTORE
  xa 5
  xl 0x370d 0x780  -- 370c MLOAD
  xa 3
  xji 0x3713 0x3719 hw
  · xs 0x3715 (.push [0x64] (by decide)) ri_push
    xs 0x3718 (.push [0x07, 0xbc] (by decide)) ri_push
    xrevert
  have hslip := gtCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  refine ⟨D2, _, _, hD2, hD02, hmT, hD0, hbn, hb1, hslip, h, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
