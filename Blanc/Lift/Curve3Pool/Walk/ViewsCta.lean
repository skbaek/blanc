import Blanc.Lift.HistIdentityCall
import Blanc.Lift.Curve3Pool.Walk.ViewsKit
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-!
# `calc_token_amount(amounts, deposit)` on the derivation

From the body (`0xb07`): the non-payable guard and `deposit < 2`, the balances read into
`0x140…0x180` (`keccak(1) + i`), `_A` (inline save of four words), `D0 = get_D_mem(balances,
amp)` (inline save of seven words), the three-step loop over `amounts`, the frame save of
`[0x140, 0x360)` around `D1 = get_D_mem(new_balances, amp)`, `totalSupply()`, and
`diff * supply / D0`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

set_option hygiene false in
/-- `MLOAD` of a carried word, else of an uncarried one. -/
local macro "xlx " pc:term:max o:term:max : tactic =>
  `(tactic| first | xl $pc $o | xlu $pc)

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {s : State}

/-- The balance slots as the body computes them. -/
theorem cta_slot0 : (Bytes.toB256 [1]).toBytes.keccak = balanceSlot 0 := by
  rw [show Bytes.toB256 [1] = 1 by decide, balancesBase_eq]
  decide

theorem cta_slot1 : balanceSlot 0 + Bytes.toB256 [1] = balanceSlot 1 := by decide

theorem cta_slot2 : balanceSlot 0 + Bytes.toB256 [2] = balanceSlot 2 := by decide

-- SEGMENT: ctaPre
/-- The balance word `k` at the frame's entry. -/
abbrev ctaB (sevm : Sevm) (b : Devm) (k : Fin 3) : B256 :=
  (b.getStor sevm.currentTarget).get (balanceSlot k)

/-- **`calc_token_amount` up to its loop**: no value, `deposit < 2`, `amp = _A()`,
`D0 = get_D_mem(balances, amp)`; the balances at `0x140…0x180`, `amp` at `0x1a0`, `D0` at
`0x200`. -/
theorem xa_cta_pre (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (h : XAt sevm post 0xb07 (St b [] (vdMem sevm) G) L) :
    sevm.value = 0 ∧ Sevm.dataWord sevm (Bytes.toB256 [100]) < Bytes.toB256 [2] ∧
      ∃ amp D0 b2 M G', SloadsOnlyH sevm b b2 ∧
      aChk s sevm.benvStat.time.toNat = some amp.toNat ∧
      getDMem ⟨(ctaB sevm b 0).toNat, (ctaB sevm b 1).toNat, (ctaB sevm b 2).toNat⟩ amp.toNat =
        some D0.toNat ∧
      XAt sevm post 0xc14 (St b2 [] M G') L ∧
      VW M [(0x200, D0), (0x140, ctaB sevm b 0), (0x160, ctaB sevm b 1), (0x180, ctaB sevm b 2),
        (0x1a0, amp)] := by
  have hV : VW (vdMem sevm) [] := ⟨Words.nil _, vyMem_wf Mem.wf_empty _,
    by rw [vyMem_empty_size]⟩
  xa 3
  xji 0xb0d 0xb11 hw
  · xdead  -- 0b0c JUMPI
  have hval : sevm.value = 0 := B256.eq_of_eqCheck_ne_zero hw
  clear hw
  xa 7
  xji 0xb1d 0xb21 hw
  · xdead  -- 0b1c JUMPI
  have hdep : Sevm.dataWord sevm (Bytes.toB256 [100]) < Bytes.toB256 [2] := by
    have e := ltCheck_ne_zero hw
    rwa [← B256.lt_iff_toNat_lt_toNat] at e
  clear hw
  xa 6
  xsw 0xb2c 0xc0  -- 0b2b MSTORE
  xa 2
  xk 0xb31 0xc0  -- 0b30 SHA3
  xw 0xb32 (.reg .sload) ri_sloadF  -- 0b31 SLOAD
  xs 0xb33 (.reg (.dup 2)) (ri_dup (by rfl))  -- 0b32 DUP3
  xsw 0xb34 0x140  -- 0b33 MSTORE
  xa 3
  xsw 0xb3a 0xc0  -- 0b39 MSTORE
  xa 2
  xk 0xb3f 0xc0  -- 0b3e SHA3
  xs 0xb40 (.reg .add) ri_add  -- 0b3f ADD
  xw 0xb41 (.reg .sload) ri_sloadF  -- 0b40 SLOAD
  xa 3
  xsw 0xb46 0x160  -- 0b45 MSTORE
  xa 3
  xsw 0xb4c 0xc0  -- 0b4b MSTORE
  xa 2
  xk 0xb51 0xc0  -- 0b50 SHA3
  xs 0xb52 (.reg .add) ri_add  -- 0b51 ADD
  xw 0xb53 (.reg .sload) ri_sloadF  -- 0b52 SLOAD
  xa 3
  xsw 0xb58 0x180  -- 0b57 MSTORE
  xa 3
  xlx 0xb5e 0x140  -- 0b5d MLOAD
  xs 0xb61 (.push [0x01, 0x60] (by decide)) ri_push  -- 0b5e PUSH2 0x0160
  xlx 0xb62 0x160  -- 0b61 MLOAD
  xs 0xb65 (.push [0x01, 0x80] (by decide)) ri_push  -- 0b62 PUSH2 0x0180
  xlx 0xb66 0x180  -- 0b65 MLOAD
  xs 0xb69 (.push [0x01, 0xa0] (by decide)) ri_push  -- 0b66 PUSH2 0x01a0
  xlx 0xb6a 0x1a0  -- 0b69 MLOAD
  xs 0xb6c (.push [0x06] (by decide)) ri_push  -- 0b6a PUSH1 0x06
  cvpc 0xb6d  -- 0b6c PC
  xa 2
  xjmp 0xa9  -- 0b71 JUMP
  have hb1 := (((SloadsOnlyH.refl (sevm := sevm) (b := b)).sload
    (Bytes.toB256 [1]).toBytes.keccak).sload ((Bytes.toB256 [1]).toBytes.keccak + Bytes.toB256 [1])).sload
    ((Bytes.toB256 [1]).toBytes.keccak + Bytes.toB256 [2])
  generalize afterSloadH sevm (afterSloadH sevm (afterSloadH sevm b _) _) _ = b1 at h hb1
  simp only [getStorVal_eq, afterSloadH_getStor, cta_slot0, cta_slot1,
    cta_slot2] at hV h
  have ha1 : Abstracts (b1.getStor sevm.currentTarget) s := by rw [hb1.getStor]; exact ha
  obtain ⟨amp, b2, M, _, hb2, h, hamp, hV1⟩ := xa_vAV hc hcode hfork ha1 hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
  xsw 0xb77 0x1e0  -- 0b76 MSTORE
  xs 0xb7a (.push [0x01, 0xa0] (by decide)) ri_push  -- 0b77 PUSH2 0x01a0
  xsw 0xb7b 0x1a0  -- 0b7a MSTORE
  xs 0xb7e (.push [0x01, 0x80] (by decide)) ri_push  -- 0b7b PUSH2 0x0180
  xsw 0xb7f 0x180  -- 0b7e MSTORE
  xs 0xb82 (.push [0x01, 0x60] (by decide)) ri_push  -- 0b7f PUSH2 0x0160
  xsw 0xb83 0x160  -- 0b82 MSTORE
  xs 0xb86 (.push [0x01, 0x40] (by decide)) ri_push  -- 0b83 PUSH2 0x0140
  xsw 0xb87 0x140  -- 0b86 MSTORE
  xs 0xb8a (.push [0x01, 0xe0] (by decide)) ri_push  -- 0b87 PUSH2 0x01e0
  xlx 0xb8b 0x1e0  -- 0b8a MLOAD
  xs 0xb8e (.push [0x01, 0xa0] (by decide)) ri_push  -- 0b8b PUSH2 0x01a0
  xsw 0xb8f 0x1a0  -- 0b8e MSTORE
  xs 0xb92 (.push [0x01, 0x40] (by decide)) ri_push  -- 0b8f PUSH2 0x0140
  xlx 0xb93 0x140  -- 0b92 MLOAD
  xs 0xb96 (.push [0x01, 0x60] (by decide)) ri_push  -- 0b93 PUSH2 0x0160
  xlx 0xb97 0x160  -- 0b96 MLOAD
  xs 0xb9a (.push [0x01, 0x80] (by decide)) ri_push  -- 0b97 PUSH2 0x0180
  xlx 0xb9b 0x180  -- 0b9a MLOAD
  xs 0xb9e (.push [0x01, 0xa0] (by decide)) ri_push  -- 0b9b PUSH2 0x01a0
  xlx 0xb9f 0x1a0  -- 0b9e MLOAD
  xs 0xba2 (.push [0x01, 0xc0] (by decide)) ri_push  -- 0b9f PUSH2 0x01c0
  xlx 0xba3 0x1c0  -- 0ba2 MLOAD
  xs 0xba6 (.push [0x01, 0xe0] (by decide)) ri_push  -- 0ba3 PUSH2 0x01e0
  xlx 0xba7 0x1e0  -- 0ba6 MLOAD
  xs 0xbaa (.push [0x02, 0x00] (by decide)) ri_push  -- 0ba7 PUSH2 0x0200
  xlx 0xbab 0x200  -- 0baa MLOAD
  xa 3
  xlx 0xbb3 0x140  -- 0bb2 MLOAD
  xs 0xbb4 (.reg (.dup 2)) (ri_dup (by rfl))  -- 0bb3 DUP3
  xsw 0xbb5 0x240  -- 0bb4 MSTORE
  xa 3
  xlx 0xbba 0x160  -- 0bb9 MLOAD
  xa 3
  xsw 0xbbf 0x260  -- 0bbe MSTORE
  xa 3
  xlx 0xbc4 0x180  -- 0bc3 MLOAD
  xa 3
  xsw 0xbc9 0x280  -- 0bc8 MSTORE
  xa 3
  xlx 0xbcf 0x1a0  -- 0bce MLOAD
  xs 0xbd2 (.push [0x02, 0xa0] (by decide)) ri_push  -- 0bcf PUSH2 0x02a0
  xsw 0xbd3 0x2a0  -- 0bd2 MSTORE
  xs 0xbd6 (.push [0x02, 0xa0] (by decide)) ri_push  -- 0bd3 PUSH2 0x02a0
  xlx 0xbd7 0x2a0  -- 0bd6 MLOAD
  xs 0xbda (.push [0x02, 0x80] (by decide)) ri_push  -- 0bd7 PUSH2 0x0280
  xlx 0xbdb 0x280  -- 0bda MLOAD
  xs 0xbde (.push [0x02, 0x60] (by decide)) ri_push  -- 0bdb PUSH2 0x0260
  xlx 0xbdf 0x260  -- 0bde MLOAD
  xs 0xbe2 (.push [0x02, 0x40] (by decide)) ri_push  -- 0bdf PUSH2 0x0240
  xlx 0xbe3 0x240  -- 0be2 MLOAD
  xs 0xbe5 (.push [0x06] (by decide)) ri_push  -- 0be3 PUSH1 0x06
  cvpc 0xbe6  -- 0be5 PC
  xa 2
  xjmp 0x7b7  -- 0bea JUMP
  obtain ⟨D0, M, _, h, hD0, hV1⟩ := xa_vGetDMem hc hcode hfork hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
  xsw 0xbf0 0x300  -- 0bef MSTORE
  xs 0xbf3 (.push [0x02, 0x00] (by decide)) ri_push  -- 0bf0 PUSH2 0x0200
  xsw 0xbf4 0x200  -- 0bf3 MSTORE
  xs 0xbf7 (.push [0x01, 0xe0] (by decide)) ri_push  -- 0bf4 PUSH2 0x01e0
  xsw 0xbf8 0x1e0  -- 0bf7 MSTORE
  xs 0xbfb (.push [0x01, 0xc0] (by decide)) ri_push  -- 0bf8 PUSH2 0x01c0
  xsw 0xbfc 0x1c0  -- 0bfb MSTORE
  xs 0xbff (.push [0x01, 0xa0] (by decide)) ri_push  -- 0bfc PUSH2 0x01a0
  xsw 0xc00 0x1a0  -- 0bff MSTORE
  xs 0xc03 (.push [0x01, 0x80] (by decide)) ri_push  -- 0c00 PUSH2 0x0180
  xsw 0xc04 0x180  -- 0c03 MSTORE
  xs 0xc07 (.push [0x01, 0x60] (by decide)) ri_push  -- 0c04 PUSH2 0x0160
  xsw 0xc08 0x160  -- 0c07 MSTORE
  xs 0xc0b (.push [0x01, 0x40] (by decide)) ri_push  -- 0c08 PUSH2 0x0140
  xsw 0xc0c 0x140  -- 0c0b MSTORE
  xs 0xc0f (.push [0x03, 0x00] (by decide)) ri_push  -- 0c0c PUSH2 0x0300
  xlx 0xc10 0x300  -- 0c0f MLOAD
  xs 0xc13 (.push [0x02, 0x00] (by decide)) ri_push  -- 0c10 PUSH2 0x0200
  xsw 0xc14 0x200  -- 0c13 MSTORE
  refine ⟨hval, hdep, amp, D0, b2, _, _, hb1.trans hb2, hamp, hD0, h, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
