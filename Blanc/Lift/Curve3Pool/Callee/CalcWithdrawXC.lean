import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawXB
import Blanc.Lift.ThreeWordFrame
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-! # `_calc_withdraw_one_coin`: the first `get_y_D` and `dy_0` -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {post b : Devm} {ρ : B256} {S : List B256} {M : Mem} {G : Nat}
  {L : List Exec.Frame}

-- SEGMENT: cwC
/-- **From `D1` (`0x3f1a`) to the fee loop's head (`0x405e`)**: `new_y = get_y_D(amp, i, xp,
D1)` inside the save of `[0x140, 0x5c0)` — its actual arguments are `0x5e0…0x680`, i.e. `amp`,
`i`, `xp` and `D1` — then the checked `dy_0 = (xp[i] - new_y) / PRECISION_MUL[i]` at `0x700`
and the loop counter at `0x720`. -/
theorem xa_cw_c (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {a i A F T x0 x1 x2 D0 D1 : B256}
    (hV : VW M [(0x520, D1), (0x400, D0), (0x360, x2), (0x340, x1), (0x320, x0),
      (0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F), (0x1a0, A),
      (0x180, ρ), (0x160, i), (0x140, a)])
    (h : XAt sevm post 0x3f1a (St b S M G) L) :
    ∃ (y : B256) (hi : i.toNat < 3) (M' : Mem) (G' : Nat),
      (∃ (ρ' : B256) (R : List B256) (M0 : Mem) (G0 : Nat),
        XAt sevm post 0x3999 (St b (ρ' :: A :: i :: x0 :: x1 :: x2 :: D1 :: R) M0 G0) L) ∧
      getYDChk A.toNat ⟨i.toNat, hi⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get D1.toNat =
        some y.toNat ∧
      y.toNat ≤ (pickWord3 i.toNat x0 x1 x2).toNat ∧ pickWord3 i.toNat cwP1 cwPm cwPm ≠ 0 ∧
      XAt sevm post 0x405e
        (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M' G') L ∧
      VW M' [(0x720, Bytes.toB256 [0]),
        (0x700, (pickWord3 i.toNat x0 x1 x2 - y) / pickWord3 i.toNat cwP1 cwPm cwPm),
        (0x5a0, y), (0x580, x2), (0x560, x1), (0x540, x0), (0x520, D1), (0x400, D0),
        (0x360, x2), (0x340, x1), (0x320, x0), (0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F), (0x1a0, A),
        (0x180, ρ), (0x160, i), (0x140, a)] := by
  xa 3
  xl 0x3f22 0x320  -- 3f21 MLOAD
  xs 0x3f23 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3f22 DUP3
  xsw 0x3f24 0x540  -- 3f23 MSTORE
  xa 3
  xl 0x3f29 0x340  -- 3f28 MLOAD
  xa 3
  xsw 0x3f2e 0x560  -- 3f2d MSTORE
  xa 3
  xl 0x3f33 0x360  -- 3f32 MLOAD
  xa 3
  xsw 0x3f38 0x580  -- 3f37 MSTORE
  xa 4
  xsw 0x3f41 0x5c0  -- 3f40 MSTORE
  have hF : Words _ [(0x580, x2), (0x560, x1), (0x540, x0), (0x520, D1), (0x400, D0), (0x360, x2), (0x340, x1),
      (0x320, x0), (0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F), (0x1a0, A),
      (0x180, ρ), (0x160, i), (0x140, a)] := hV.words.sub (by
    simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])
  -- the save loop over [0x140, 0x5c0)
  obtain ⟨ws, M1, _, hws, rfl, h, hV1⟩ := xa_saveV (H := 0x3f41)
    (t := ⟨0x05, 0xc0, 0x05, 0xc0, 0x3f, 0x63, 0x3f, 0x41⟩) (lo := 0x140) (n := 36) vsave
    (by decide) hV (by rfl) (by decide) (by decide) (by decide) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0x3f67 (.push [0x01, 0xa0] (by decide)) ri_push  -- 3f64 PUSH2 0x01a0
  xl 0x3f68 0x1a0  -- 3f67 MLOAD
  xs 0x3f6b (.push [0x05, 0xe0] (by decide)) ri_push  -- 3f68 PUSH2 0x05e0
  xsw 0x3f6c 0x5e0  -- 3f6b MSTORE
  xs 0x3f6f (.push [0x01, 0x60] (by decide)) ri_push  -- 3f6c PUSH2 0x0160
  xl 0x3f70 0x160  -- 3f6f MLOAD
  xs 0x3f73 (.push [0x06, 0x00] (by decide)) ri_push  -- 3f70 PUSH2 0x0600
  xsw 0x3f74 0x600  -- 3f73 MSTORE
  xa 3
  xl 0x3f7c 0x320  -- 3f7b MLOAD
  xs 0x3f7d (.reg (.dup 2)) (ri_dup (by rfl))  -- 3f7c DUP3
  xsw 0x3f7e 0x620  -- 3f7d MSTORE
  xa 3
  xl 0x3f83 0x340  -- 3f82 MLOAD
  xa 3
  xsw 0x3f88 0x640  -- 3f87 MSTORE
  xa 3
  xl 0x3f8d 0x360  -- 3f8c MLOAD
  xa 3
  xsw 0x3f92 0x660  -- 3f91 MSTORE
  xa 3
  xl 0x3f98 0x520  -- 3f97 MLOAD
  xs 0x3f9b (.push [0x06, 0x80] (by decide)) ri_push  -- 3f98 PUSH2 0x0680
  xsw 0x3f9c 0x680  -- 3f9b MSTORE
  xs 0x3f9f (.push [0x06, 0x80] (by decide)) ri_push  -- 3f9c PUSH2 0x0680
  xl 0x3fa0 0x680  -- 3f9f MLOAD
  xs 0x3fa3 (.push [0x06, 0x60] (by decide)) ri_push  -- 3fa0 PUSH2 0x0660
  xl 0x3fa4 0x660  -- 3fa3 MLOAD
  xs 0x3fa7 (.push [0x06, 0x40] (by decide)) ri_push  -- 3fa4 PUSH2 0x0640
  xl 0x3fa8 0x640  -- 3fa7 MLOAD
  xs 0x3fab (.push [0x06, 0x20] (by decide)) ri_push  -- 3fa8 PUSH2 0x0620
  xl 0x3fac 0x620  -- 3fab MLOAD
  xs 0x3faf (.push [0x06, 0x00] (by decide)) ri_push  -- 3fac PUSH2 0x0600
  xl 0x3fb0 0x600  -- 3faf MLOAD
  xs 0x3fb3 (.push [0x05, 0xe0] (by decide)) ri_push  -- 3fb0 PUSH2 0x05e0
  xl 0x3fb4 0x5e0  -- 3fb3 MLOAD
  xs 0x3fb6 (.push [0x06] (by decide)) ri_push  -- 3fb4 PUSH1 0x06
  cvpc 0x3fb7  -- 3fb6 PC
  xa 2
  xjmp 0x3999  -- 3fbb JUMP
  have hcall := h
  have hcov := (hV.words 0x680 _ List.mem_cons_self).1
  obtain ⟨y, M2, _, h, hi, hy, hV1⟩ := xa_vGetYD hc hcode hfork hV (by omega) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
  xsw 0x3fc1 0x6e0  -- 3fc0 MSTORE
  xa 2
  xsw 0x3fc8 0x5c0  -- 3fc7 MSTORE
  -- the restore loop over [0x140, 0x5c0)
  obtain ⟨M3, _, h, hV1⟩ := xa_restoreFrameV (H := 0x3fc8)
    (t := ⟨0x05, 0xc0, 0x01, 0x40, 0x3f, 0xeb, 0x3f, 0xc8⟩) (lo := 0x140) (n := 36) vrestore
    (by decide) (by decide) (by decide) hV (by rfl) (by decide) (by decide) hF (by
      intro o v hm
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨34, by decide, rfl⟩
      · exact ⟨33, by decide, rfl⟩
      · exact ⟨32, by decide, rfl⟩
      · exact ⟨31, by decide, rfl⟩
      · exact ⟨22, by decide, rfl⟩
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
  xs 0x3fef (.push [0x06, 0xe0] (by decide)) ri_push  -- 3fec PUSH2 0x06e0
  xl 0x3ff0 0x6e0  -- 3fef MLOAD
  xs 0x3ff3 (.push [0x05, 0xa0] (by decide)) ri_push  -- 3ff0 PUSH2 0x05a0
  xsw 0x3ff4 0x5a0  -- 3ff3 MSTORE
  xa 2
  xl 0x3ffb 0x160  -- 3ffa MLOAD
  xa 4
  xji 0x4003 0x4007 hw
  · xdead
  clear hw
  xa 4
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x400d) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x320) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) sr
  clear sr
  xs 0x4010 (.push [0x05, 0xa0] (by decide)) ri_push  -- 400d PUSH2 0x05a0
  xl 0x4011 0x5a0  -- 4010 MLOAD
  xa 5
  xji 0x4019 0x401d hw
  · xdead
  have hs1 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 10
  xl 0x402c 0x160  -- 402b MLOAD
  xa 4
  xji 0x4034 0x4038 hw
  · xdead
  clear hw
  xa 4
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x403e) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x220) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) sr
  clear sr
  xa 3
  xji 0x4044 0x4048 hw
  · xdead
  have hp := hw
  clear hw
  xa 8
  xsw 0x4053 0x700  -- 4052 MSTORE
  xa 5
  xsw 0x405d 0x720  -- 405c MSTORE
  xs 0x405e (.reg .add) ri_add  -- 405d ADD
  refine ⟨y, hi, _, _, ⟨_, _, _, _, hcall⟩, hy, hs1, hp, h, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
