import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawX

/-! # `_calc_withdraw_one_coin`: `xp`, `D0 = get_D(xp, amp)`, `D1 = D0 - amount · D0 / supply` -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {post b : Devm} {ρ : B256} {S : List B256} {M : Mem} {G : Nat}
  {L : List Exec.Frame} {s : State}

-- SEGMENT: cwB
/-- **From the supply (`0x3d9a`) to `D1` at `0x520` (`0x3f1a`)**: `_xp()` inside the save of
`[0x140, 0x380)` (copied to `0x320…0x360`), `get_D(xp, amp)` inside the save of
`[0x140, 0x420)` (`D0` at `0x400`), and the checked `D0 - amount · D0 / supply`. -/
theorem xa_cw_b (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork) {a i A F T : B256}
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hV : VW M [(0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F),
      (0x1a0, A), (0x180, ρ), (0x160, i), (0x140, a)])
    (h : XAt sevm post 0x3d9a (St b S M G) L) :
    ∃ (x0 x1 x2 D0 : B256) (b' : Devm) (M' : Mem) (G' : Nat), SloadsOnly sevm b b' ∧
      xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get A.toNat 1 = some D0.toNat ∧
      B256.Nofm a D0 ∧ T ≠ 0 ∧ (a * D0 / T).toNat ≤ D0.toNat ∧
      XAt sevm post 0x3f1a (St b' S M' G') L ∧
      VW M' [(0x520, D0 - a * D0 / T), (0x400, D0), (0x360, x2), (0x340, x1), (0x320, x0),
        (0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F), (0x1a0, A),
        (0x180, ρ), (0x160, i), (0x140, a)] := by
  xs 0x3d9d (.push [0x03, 0x20] (by decide)) ri_push  -- 3d9a PUSH2 0x0320
  xs 0x3da0 (.push [0x01, 0x40] (by decide)) ri_push  -- 3d9d PUSH2 0x0140
  xs 0x3da3 (.push [0x03, 0x80] (by decide)) ri_push  -- 3da0 PUSH2 0x0380
  xsw 0x3da4 0x380  -- 3da3 MSTORE
  have hF1 : Words _ [(0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F), (0x1a0, A), (0x180, ρ),
      (0x160, i), (0x140, a)] := hV.words.sub (by
    simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])
  -- the save loop over [0x140, 0x380)
  obtain ⟨ws, M1, _, hws, rfl, h, hV1⟩ := xa_saveV (H := 0x3da4)
    (t := ⟨0x03, 0x80, 0x03, 0x80, 0x3d, 0xc6, 0x3d, 0xa4⟩) (lo := 0x140) (n := 18) vsave
    (by decide) hV (by rfl) (by decide) (by decide) (by decide) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0x3dc9 (.push [0x06] (by decide)) ri_push  -- 3dc7 PUSH1 0x06
  cvpc 0x3dca  -- 3dc9 PC
  xs 0x3dcb (.reg .add) ri_add  -- 3dca ADD
  xs 0x3dce (.push [0x02, 0x81] (by decide)) ri_push  -- 3dcb PUSH2 0x0281
  xjmp 0x281  -- 3dce JUMP
  obtain ⟨x0, x1, x2, b1, M2, _, hb1, h, hxp, hV1⟩ := xa_vXp hc hcode hfork ha hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xjd 0x3dd0  -- 3dcf JUMPDEST
  xs 0x3dd3 (.push [0x03, 0xa0] (by decide)) ri_push  -- 3dd0 PUSH2 0x03a0
  xsw 0x3dd4 0x3a0  -- 3dd3 MSTORE
  xs 0x3dd7 (.push [0x03, 0xc0] (by decide)) ri_push  -- 3dd4 PUSH2 0x03c0
  xsw 0x3dd8 0x3c0  -- 3dd7 MSTORE
  xs 0x3ddb (.push [0x03, 0xe0] (by decide)) ri_push  -- 3dd8 PUSH2 0x03e0
  xsw 0x3ddc 0x3e0  -- 3ddb MSTORE
  xs 0x3ddf (.push [0x03, 0x60] (by decide)) ri_push  -- 3ddc PUSH2 0x0360
  xs 0x3de2 (.push [0x03, 0x80] (by decide)) ri_push  -- 3ddf PUSH2 0x0380
  xsw 0x3de3 0x380  -- 3de2 MSTORE
  -- the restore loop over [0x140, 0x380)
  obtain ⟨M3, _, h, hV1⟩ := xa_restoreFrameV (H := 0x3de3)
    (t := ⟨0x03, 0x80, 0x01, 0x40, 0x3e, 0x06, 0x3d, 0xe3⟩) (lo := 0x140) (n := 18) vrestore
    (by decide) (by decide) (by decide) hV (by rfl) (by decide) (by decide) hF1 (by
      intro o v hm
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨10, by decide, rfl⟩
      · exact ⟨9, by decide, rfl⟩
      · exact ⟨8, by decide, rfl⟩
      · exact ⟨7, by decide, rfl⟩
      · exact ⟨6, by decide, rfl⟩
      · exact ⟨3, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨0, by decide, rfl⟩) h
  simp only [List.cons_append, List.nil_append] at hV1
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0x3e0a (.push [0x03, 0xa0] (by decide)) ri_push  -- 3e07 PUSH2 0x03a0
  xs 0x3e0b (.reg (.dup 0)) (ri_dup (by rfl))  -- 3e0a DUP1
  xl 0x3e0c 0x3a0  -- 3e0b MLOAD
  xs 0x3e0d (.reg (.dup 2)) (ri_dup (by rfl))  -- 3e0c DUP3
  xsw 0x3e0e 0x320  -- 3e0d MSTORE
  xs 0x3e0f (.reg (.dup 0)) (ri_dup (by rfl))  -- 3e0e DUP1
  xs 0x3e11 (.push [0x20] (by decide)) ri_push  -- 3e0f PUSH1 0x20
  xs 0x3e12 (.reg .add) ri_add  -- 3e11 ADD
  xl 0x3e13 0x3c0  -- 3e12 MLOAD
  xs 0x3e14 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3e13 DUP3
  xs 0x3e16 (.push [0x20] (by decide)) ri_push  -- 3e14 PUSH1 0x20
  xs 0x3e17 (.reg .add) ri_add  -- 3e16 ADD
  xsw 0x3e18 0x340  -- 3e17 MSTORE
  xs 0x3e19 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3e18 DUP1
  xs 0x3e1b (.push [0x40] (by decide)) ri_push  -- 3e19 PUSH1 0x40
  xs 0x3e1c (.reg .add) ri_add  -- 3e1b ADD
  xl 0x3e1d 0x3e0  -- 3e1c MLOAD
  xs 0x3e1e (.reg (.dup 2)) (ri_dup (by rfl))  -- 3e1d DUP3
  xs 0x3e20 (.push [0x40] (by decide)) ri_push  -- 3e1e PUSH1 0x40
  xs 0x3e21 (.reg .add) ri_add  -- 3e20 ADD
  xsw 0x3e22 0x360  -- 3e21 MSTORE
  xs 0x3e23 (.reg .pop) ri_pop  -- 3e22 POP
  xs 0x3e24 (.reg .pop) ri_pop  -- 3e23 POP
  xs 0x3e27 (.push [0x01, 0x40] (by decide)) ri_push  -- 3e24 PUSH2 0x0140
  xs 0x3e2a (.push [0x04, 0x20] (by decide)) ri_push  -- 3e27 PUSH2 0x0420
  xsw 0x3e2b 0x420  -- 3e2a MSTORE
  have hF2 : Words _ [(0x360, x2), (0x340, x1), (0x320, x0), (0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1),
      (0x200, F), (0x1a0, A), (0x180, ρ), (0x160, i), (0x140, a)] := hV.words.sub (by
    simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])
  -- the save loop over [0x140, 0x420)
  obtain ⟨ws', M4, _, hws', rfl, h, hV1⟩ := xa_saveV (H := 0x3e2b)
    (t := ⟨0x04, 0x20, 0x04, 0x20, 0x3e, 0x4d, 0x3e, 0x2b⟩) (lo := 0x140) (n := 23) vsave
    (by decide) hV (by rfl) (by decide) (by decide) (by decide) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0x3e51 (.push [0x04, 0x40] (by decide)) ri_push  -- 3e4e PUSH2 0x0440
  xs 0x3e54 (.push [0x03, 0x20] (by decide)) ri_push  -- 3e51 PUSH2 0x0320
  xs 0x3e55 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3e54 DUP1
  xl 0x3e56 0x320  -- 3e55 MLOAD
  xs 0x3e57 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3e56 DUP3
  xsw 0x3e58 0x440  -- 3e57 MSTORE
  xs 0x3e59 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3e58 DUP1
  xs 0x3e5b (.push [0x20] (by decide)) ri_push  -- 3e59 PUSH1 0x20
  xs 0x3e5c (.reg .add) ri_add  -- 3e5b ADD
  xl 0x3e5d 0x340  -- 3e5c MLOAD
  xs 0x3e5e (.reg (.dup 2)) (ri_dup (by rfl))  -- 3e5d DUP3
  xs 0x3e60 (.push [0x20] (by decide)) ri_push  -- 3e5e PUSH1 0x20
  xs 0x3e61 (.reg .add) ri_add  -- 3e60 ADD
  xsw 0x3e62 0x460  -- 3e61 MSTORE
  xs 0x3e63 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3e62 DUP1
  xs 0x3e65 (.push [0x40] (by decide)) ri_push  -- 3e63 PUSH1 0x40
  xs 0x3e66 (.reg .add) ri_add  -- 3e65 ADD
  xl 0x3e67 0x360  -- 3e66 MLOAD
  xs 0x3e68 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3e67 DUP3
  xs 0x3e6a (.push [0x40] (by decide)) ri_push  -- 3e68 PUSH1 0x40
  xs 0x3e6b (.reg .add) ri_add  -- 3e6a ADD
  xsw 0x3e6c 0x480  -- 3e6b MSTORE
  xs 0x3e6d (.reg .pop) ri_pop  -- 3e6c POP
  xs 0x3e6e (.reg .pop) ri_pop  -- 3e6d POP
  xs 0x3e71 (.push [0x01, 0xa0] (by decide)) ri_push  -- 3e6e PUSH2 0x01a0
  xl 0x3e72 0x1a0  -- 3e71 MLOAD
  xs 0x3e75 (.push [0x04, 0xa0] (by decide)) ri_push  -- 3e72 PUSH2 0x04a0
  xsw 0x3e76 0x4a0  -- 3e75 MSTORE
  xs 0x3e79 (.push [0x04, 0xa0] (by decide)) ri_push  -- 3e76 PUSH2 0x04a0
  xl 0x3e7a 0x4a0  -- 3e79 MLOAD
  xs 0x3e7d (.push [0x04, 0x80] (by decide)) ri_push  -- 3e7a PUSH2 0x0480
  xl 0x3e7e 0x480  -- 3e7d MLOAD
  xs 0x3e81 (.push [0x04, 0x60] (by decide)) ri_push  -- 3e7e PUSH2 0x0460
  xl 0x3e82 0x460  -- 3e81 MLOAD
  xs 0x3e85 (.push [0x04, 0x40] (by decide)) ri_push  -- 3e82 PUSH2 0x0440
  xl 0x3e86 0x440  -- 3e85 MLOAD
  xs 0x3e88 (.push [0x06] (by decide)) ri_push  -- 3e86 PUSH1 0x06
  cvpc 0x3e89  -- 3e88 PC
  xs 0x3e8a (.reg .add) ri_add  -- 3e89 ADD
  xs 0x3e8d (.push [0x04, 0xc9] (by decide)) ri_push  -- 3e8a PUSH2 0x04c9
  xjmp 0x4c9  -- 3e8d JUMP
  have hcov := (hV.words 0x4a0 A List.mem_cons_self).1
  obtain ⟨D0, M5, _, h, hD0, -, hV1⟩ := xa_vGetD hc hcode hfork hV (by omega) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xjd 0x3e8f  -- 3e8e JUMPDEST
  xs 0x3e92 (.push [0x05, 0x00] (by decide)) ri_push  -- 3e8f PUSH2 0x0500
  xsw 0x3e93 0x500  -- 3e92 MSTORE
  xs 0x3e96 (.push [0x04, 0x00] (by decide)) ri_push  -- 3e93 PUSH2 0x0400
  xs 0x3e99 (.push [0x04, 0x20] (by decide)) ri_push  -- 3e96 PUSH2 0x0420
  xsw 0x3e9a 0x420  -- 3e99 MSTORE
  -- the restore loop over [0x140, 0x420)
  obtain ⟨M6, _, h, hV1⟩ := xa_restoreFrameV (H := 0x3e9a)
    (t := ⟨0x04, 0x20, 0x01, 0x40, 0x3e, 0xbd, 0x3e, 0x9a⟩) (lo := 0x140) (n := 23) vrestore
    (by decide) (by decide) (by decide) hV (by rfl) (by decide) (by decide) hF2 (by
      intro o v hm
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨17, by decide, rfl⟩
      · exact ⟨16, by decide, rfl⟩
      · exact ⟨15, by decide, rfl⟩
      · exact ⟨10, by decide, rfl⟩
      · exact ⟨9, by decide, rfl⟩
      · exact ⟨8, by decide, rfl⟩
      · exact ⟨7, by decide, rfl⟩
      · exact ⟨6, by decide, rfl⟩
      · exact ⟨3, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨0, by decide, rfl⟩) h
  simp only [List.cons_append, List.nil_append] at hV1
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0x3ec1 (.push [0x05, 0x00] (by decide)) ri_push  -- 3ebe PUSH2 0x0500
  xl 0x3ec2 0x500  -- 3ec1 MLOAD
  xs 0x3ec5 (.push [0x04, 0x00] (by decide)) ri_push  -- 3ec2 PUSH2 0x0400
  xsw 0x3ec6 0x400  -- 3ec5 MSTORE
  xs 0x3ec9 (.push [0x04, 0x00] (by decide)) ri_push  -- 3ec6 PUSH2 0x0400
  xl 0x3eca 0x400  -- 3ec9 MLOAD
  xs 0x3ecd (.push [0x01, 0x40] (by decide)) ri_push  -- 3eca PUSH2 0x0140
  xl 0x3ece 0x140  -- 3ecd MLOAD
  xs 0x3ed1 (.push [0x04, 0x00] (by decide)) ri_push  -- 3ece PUSH2 0x0400
  xl 0x3ed2 0x400  -- 3ed1 MLOAD
  xs 0x3ed3 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3ed2 DUP1
  xs 0x3ed4 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3ed3 DUP3
  xs 0x3ed5 (.reg .mul) ri_mul  -- 3ed4 MUL
  xs 0x3ed6 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3ed5 DUP3
  xs 0x3ed7 (.reg .iszero) ri_iszero  -- 3ed6 ISZERO
  xs 0x3ed8 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3ed7 DUP3
  xs 0x3ed9 (.reg (.dup 4)) (ri_dup (by rfl))  -- 3ed8 DUP5
  xs 0x3eda (.reg (.dup 3)) (ri_dup (by rfl))  -- 3ed9 DUP4
  xs 0x3edb (.reg .div) ri_div  -- 3eda DIV
  xs 0x3edc (.reg .eq) ri_eq  -- 3edb EQ
  xs 0x3edd (.reg .or) ri_or  -- 3edc OR
  xs 0x3ee0 (.push [0x3e, 0xe5] (by decide)) ri_push  -- 3edd PUSH2 0x3ee5
  xji 0x3ee1 0x3ee5 hw
  · xdead
  have hm0 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xjd 0x3ee6  -- 3ee5 JUMPDEST
  xs 0x3ee7 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3ee6 DUP1
  xs 0x3ee8 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3ee7 SWAP1
  xs 0x3ee9 (.reg .pop) ri_pop  -- 3ee8 POP
  xs 0x3eea (.reg (.swap 0)) (ri_swap (by rfl))  -- 3ee9 SWAP1
  xs 0x3eeb (.reg .pop) ri_pop  -- 3eea POP
  xs 0x3eec (.reg (.swap 0)) (ri_swap (by rfl))  -- 3eeb SWAP1
  xs 0x3eed (.reg .pop) ri_pop  -- 3eec POP
  xs 0x3ef0 (.push [0x02, 0x80] (by decide)) ri_push  -- 3eed PUSH2 0x0280
  xl 0x3ef1 0x280  -- 3ef0 MLOAD
  xs 0x3ef2 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3ef1 DUP1
  xs 0x3ef3 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3ef2 DUP1
  xs 0x3ef6 (.push [0x3e, 0xfb] (by decide)) ri_push  -- 3ef3 PUSH2 0x3efb
  xji 0x3ef7 0x3efb hw
  · xdead
  have hT := hw
  clear hw
  xjd 0x3efc  -- 3efb JUMPDEST
  xs 0x3efd (.reg (.dup 2)) (ri_dup (by rfl))  -- 3efc DUP3
  xs 0x3efe (.reg .div) ri_div  -- 3efd DIV
  xs 0x3eff (.reg (.swap 0)) (ri_swap (by rfl))  -- 3efe SWAP1
  xs 0x3f00 (.reg .pop) ri_pop  -- 3eff POP
  xs 0x3f01 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3f00 SWAP1
  xs 0x3f02 (.reg .pop) ri_pop  -- 3f01 POP
  xs 0x3f03 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3f02 DUP1
  xs 0x3f04 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3f03 DUP3
  xs 0x3f05 (.reg .lt) ri_lt  -- 3f04 LT
  xs 0x3f06 (.reg .iszero) ri_iszero  -- 3f05 ISZERO
  xs 0x3f09 (.push [0x3f, 0x0e] (by decide)) ri_push  -- 3f06 PUSH2 0x3f0e
  xji 0x3f0a 0x3f0e hw
  · xdead
  have hs0 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x3f0f  -- 3f0e JUMPDEST
  xs 0x3f10 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3f0f DUP1
  xs 0x3f11 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3f10 DUP3
  xs 0x3f12 (.reg .sub) ri_sub  -- 3f11 SUB
  xs 0x3f13 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3f12 SWAP1
  xs 0x3f14 (.reg .pop) ri_pop  -- 3f13 POP
  xs 0x3f15 (.reg (.swap 0)) (ri_swap (by rfl))  -- 3f14 SWAP1
  xs 0x3f16 (.reg .pop) ri_pop  -- 3f15 POP
  xs 0x3f19 (.push [0x05, 0x20] (by decide)) ri_push  -- 3f16 PUSH2 0x0520
  xsw 0x3f1a 0x520  -- 3f19 MSTORE
  refine ⟨x0, x1, x2, D0, b1, _, _, hb1, hxp, hD0, hm0, hT, hs0, h, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
