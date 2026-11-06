import Blanc.Lift.HistIdentityCall
import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawX
import Blanc.Lift.Curve3Pool.Walk.AutoStep

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
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork) {a i A F T : B256}
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hV : VW M [(0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F),
      (0x1a0, A), (0x180, ρ), (0x160, i), (0x140, a)])
    (h : XAt sevm post 0x3d9a (St b S M G) L) :
    ∃ (x0 x1 x2 D0 : B256) (b' : Devm) (M' : Mem) (G' : Nat), SloadsOnlyH sevm b b' ∧
      xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get A.toNat 1 = some D0.toNat ∧
      B256.Nofm a D0 ∧ T ≠ 0 ∧ (a * D0 / T).toNat ≤ D0.toNat ∧
      XAt sevm post 0x3f1a (St b' S M' G') L ∧
      VW M' [(0x520, D0 - a * D0 / T), (0x400, D0), (0x360, x2), (0x340, x1), (0x320, x0),
        (0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F), (0x1a0, A),
        (0x180, ρ), (0x160, i), (0x140, a)] := by
  xa 3
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
  xa 2
  xjmp 0x281  -- 3dce JUMP
  obtain ⟨x0, x1, x2, b1, M2, _, hb1, h, hxp, hV1⟩ := xa_vXp hc hcode hfork ha hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
  xsw 0x3dd4 0x3a0  -- 3dd3 MSTORE
  xs 0x3dd7 (.push [0x03, 0xc0] (by decide)) ri_push  -- 3dd4 PUSH2 0x03c0
  xsw 0x3dd8 0x3c0  -- 3dd7 MSTORE
  xs 0x3ddb (.push [0x03, 0xe0] (by decide)) ri_push  -- 3dd8 PUSH2 0x03e0
  xsw 0x3ddc 0x3e0  -- 3ddb MSTORE
  xa 2
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
  xa 2
  xl 0x3e0c 0x3a0  -- 3e0b MLOAD
  xs 0x3e0d (.reg (.dup 2)) (ri_dup (by rfl))  -- 3e0c DUP3
  xsw 0x3e0e 0x320  -- 3e0d MSTORE
  xa 3
  xl 0x3e13 0x3c0  -- 3e12 MLOAD
  xa 3
  xsw 0x3e18 0x340  -- 3e17 MSTORE
  xa 3
  xl 0x3e1d 0x3e0  -- 3e1c MLOAD
  xa 3
  xsw 0x3e22 0x360  -- 3e21 MSTORE
  xa 4
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
  xa 3
  xl 0x3e56 0x320  -- 3e55 MLOAD
  xs 0x3e57 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3e56 DUP3
  xsw 0x3e58 0x440  -- 3e57 MSTORE
  xa 3
  xl 0x3e5d 0x340  -- 3e5c MLOAD
  xa 3
  xsw 0x3e62 0x460  -- 3e61 MSTORE
  xa 3
  xl 0x3e67 0x360  -- 3e66 MLOAD
  xa 3
  xsw 0x3e6c 0x480  -- 3e6b MSTORE
  xa 3
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
  xa 2
  xjmp 0x4c9  -- 3e8d JUMP
  have hcov := (hV.words 0x4a0 A List.mem_cons_self).1
  obtain ⟨D0, M5, _, h, hD0, -, hV1⟩ := xa_vGetD hc hcode hfork hV (by omega) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
  xsw 0x3e93 0x500  -- 3e92 MSTORE
  xa 2
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
  xa 12
  xji 0x3ee1 0x3ee5 hw
  · xdead
  have hm0 := B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xl 0x3ef1 0x280  -- 3ef0 MLOAD
  xa 3
  xji 0x3ef7 0x3efb hw
  · xdead
  have hT := hw
  clear hw
  xa 12
  xji 0x3f0a 0x3f0e hw
  · xdead
  have hs0 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 9
  xsw 0x3f1a 0x520  -- 3f19 MSTORE
  refine ⟨x0, x1, x2, D0, b1, _, _, hb1, hxp, hD0, hm0, hT, hs0, h, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
