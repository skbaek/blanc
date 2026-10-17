import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawXB
import Blanc.Lift.ThreeWordFrame

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
      getYDChk A.toNat ⟨i.toNat, hi⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get D1.toNat =
        some y.toNat ∧
      y.toNat ≤ (pickWord3 i.toNat x0 x1 x2).toNat ∧ pickWord3 i.toNat cwP1 cwPm cwPm ≠ 0 ∧
      XAt sevm post 0x405e
        (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M' G') L ∧
      VW M' [(0x720, Bytes.toB256 [0]),
        (0x700, (pickWord3 i.toNat x0 x1 x2 - y) / pickWord3 i.toNat cwP1 cwPm cwPm),
        (0x5a0, y), (0x520, D1), (0x400, D0), (0x360, x2), (0x340, x1), (0x320, x0),
        (0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F), (0x1a0, A),
        (0x180, ρ), (0x160, i), (0x140, a)] := by
  xs 0x3f1d (.push [0x05, 0x40] (by decide)) ri_push  -- 3f1a PUSH2 0x0540
  xs 0x3f20 (.push [0x03, 0x20] (by decide)) ri_push  -- 3f1d PUSH2 0x0320
  xs 0x3f21 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3f20 DUP1
  xl 0x3f22 0x320  -- 3f21 MLOAD
  xs 0x3f23 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3f22 DUP3
  xsw 0x3f24 0x540  -- 3f23 MSTORE
  xs 0x3f25 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3f24 DUP1
  xs 0x3f27 (.push [0x20] (by decide)) ri_push  -- 3f25 PUSH1 0x20
  xs 0x3f28 (.reg .add) ri_add  -- 3f27 ADD
  xl 0x3f29 0x340  -- 3f28 MLOAD
  xs 0x3f2a (.reg (.dup 2)) (ri_dup (by rfl))  -- 3f29 DUP3
  xs 0x3f2c (.push [0x20] (by decide)) ri_push  -- 3f2a PUSH1 0x20
  xs 0x3f2d (.reg .add) ri_add  -- 3f2c ADD
  xsw 0x3f2e 0x560  -- 3f2d MSTORE
  xs 0x3f2f (.reg (.dup 0)) (ri_dup (by rfl))  -- 3f2e DUP1
  xs 0x3f31 (.push [0x40] (by decide)) ri_push  -- 3f2f PUSH1 0x40
  xs 0x3f32 (.reg .add) ri_add  -- 3f31 ADD
  xl 0x3f33 0x360  -- 3f32 MLOAD
  xs 0x3f34 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3f33 DUP3
  xs 0x3f36 (.push [0x40] (by decide)) ri_push  -- 3f34 PUSH1 0x40
  xs 0x3f37 (.reg .add) ri_add  -- 3f36 ADD
  xsw 0x3f38 0x580  -- 3f37 MSTORE
  xs 0x3f39 (.reg .pop) ri_pop  -- 3f38 POP
  xs 0x3f3a (.reg .pop) ri_pop  -- 3f39 POP
  xs 0x3f3d (.push [0x01, 0x40] (by decide)) ri_push  -- 3f3a PUSH2 0x0140
  xs 0x3f40 (.push [0x05, 0xc0] (by decide)) ri_push  -- 3f3d PUSH2 0x05c0
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
  xs 0x3f77 (.push [0x06, 0x20] (by decide)) ri_push  -- 3f74 PUSH2 0x0620
  xs 0x3f7a (.push [0x03, 0x20] (by decide)) ri_push  -- 3f77 PUSH2 0x0320
  xs 0x3f7b (.reg (.dup 0)) (ri_dup (by rfl))  -- 3f7a DUP1
  xl 0x3f7c 0x320  -- 3f7b MLOAD
  xs 0x3f7d (.reg (.dup 2)) (ri_dup (by rfl))  -- 3f7c DUP3
  xsw 0x3f7e 0x620  -- 3f7d MSTORE
  xs 0x3f7f (.reg (.dup 0)) (ri_dup (by rfl))  -- 3f7e DUP1
  xs 0x3f81 (.push [0x20] (by decide)) ri_push  -- 3f7f PUSH1 0x20
  xs 0x3f82 (.reg .add) ri_add  -- 3f81 ADD
  xl 0x3f83 0x340  -- 3f82 MLOAD
  xs 0x3f84 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3f83 DUP3
  xs 0x3f86 (.push [0x20] (by decide)) ri_push  -- 3f84 PUSH1 0x20
  xs 0x3f87 (.reg .add) ri_add  -- 3f86 ADD
  xsw 0x3f88 0x640  -- 3f87 MSTORE
  xs 0x3f89 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3f88 DUP1
  xs 0x3f8b (.push [0x40] (by decide)) ri_push  -- 3f89 PUSH1 0x40
  xs 0x3f8c (.reg .add) ri_add  -- 3f8b ADD
  xl 0x3f8d 0x360  -- 3f8c MLOAD
  xs 0x3f8e (.reg (.dup 2)) (ri_dup (by rfl))  -- 3f8d DUP3
  xs 0x3f90 (.push [0x40] (by decide)) ri_push  -- 3f8e PUSH1 0x40
  xs 0x3f91 (.reg .add) ri_add  -- 3f90 ADD
  xsw 0x3f92 0x660  -- 3f91 MSTORE
  xs 0x3f93 (.reg .pop) ri_pop  -- 3f92 POP
  xs 0x3f94 (.reg .pop) ri_pop  -- 3f93 POP
  xs 0x3f97 (.push [0x05, 0x20] (by decide)) ri_push  -- 3f94 PUSH2 0x0520
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
  xs 0x3fb8 (.reg .add) ri_add  -- 3fb7 ADD
  xs 0x3fbb (.push [0x39, 0x99] (by decide)) ri_push  -- 3fb8 PUSH2 0x3999
  xjmp 0x3999  -- 3fbb JUMP
  have hcov := (hV.words 0x680 _ List.mem_cons_self).1
  obtain ⟨y, M2, _, h, hi, hy, hV1⟩ := xa_vGetYD hc hcode hfork hV (by omega) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xjd 0x3fbd  -- 3fbc JUMPDEST
  xs 0x3fc0 (.push [0x06, 0xe0] (by decide)) ri_push  -- 3fbd PUSH2 0x06e0
  xsw 0x3fc1 0x6e0  -- 3fc0 MSTORE
  xs 0x3fc4 (.push [0x05, 0xa0] (by decide)) ri_push  -- 3fc1 PUSH2 0x05a0
  xs 0x3fc7 (.push [0x05, 0xc0] (by decide)) ri_push  -- 3fc4 PUSH2 0x05c0
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
  xs 0x3ff7 (.push [0x03, 0x20] (by decide)) ri_push  -- 3ff4 PUSH2 0x0320
  xs 0x3ffa (.push [0x01, 0x60] (by decide)) ri_push  -- 3ff7 PUSH2 0x0160
  xl 0x3ffb 0x160  -- 3ffa MLOAD
  xs 0x3ffd (.push [0x03] (by decide)) ri_push  -- 3ffb PUSH1 0x03
  xs 0x3ffe (.reg (.dup 1)) (ri_dup (by rfl))  -- 3ffd DUP2
  xs 0x3fff (.reg .lt) ri_lt  -- 3ffe LT
  xs 0x4002 (.push [0x40, 0x07] (by decide)) ri_push  -- 3fff PUSH2 0x4007
  xji 0x4003 0x4007 hw
  · xdead
  clear hw
  xjd 0x4008  -- 4007 JUMPDEST
  xs 0x400a (.push [0x20] (by decide)) ri_push  -- 4008 PUSH1 0x20
  xs 0x400b (.reg .mul) ri_mul  -- 400a MUL
  xs 0x400c (.reg .add) ri_add  -- 400b ADD
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x400d) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x320) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) sr
  clear sr
  xs 0x4010 (.push [0x05, 0xa0] (by decide)) ri_push  -- 400d PUSH2 0x05a0
  xl 0x4011 0x5a0  -- 4010 MLOAD
  xs 0x4012 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4011 DUP1
  xs 0x4013 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4012 DUP3
  xs 0x4014 (.reg .lt) ri_lt  -- 4013 LT
  xs 0x4015 (.reg .iszero) ri_iszero  -- 4014 ISZERO
  xs 0x4018 (.push [0x40, 0x1d] (by decide)) ri_push  -- 4015 PUSH2 0x401d
  xji 0x4019 0x401d hw
  · xdead
  have hs1 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x401e  -- 401d JUMPDEST
  xs 0x401f (.reg (.dup 0)) (ri_dup (by rfl))  -- 401e DUP1
  xs 0x4020 (.reg (.dup 2)) (ri_dup (by rfl))  -- 401f DUP3
  xs 0x4021 (.reg .sub) ri_sub  -- 4020 SUB
  xs 0x4022 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4021 SWAP1
  xs 0x4023 (.reg .pop) ri_pop  -- 4022 POP
  xs 0x4024 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4023 SWAP1
  xs 0x4025 (.reg .pop) ri_pop  -- 4024 POP
  xs 0x4028 (.push [0x02, 0x20] (by decide)) ri_push  -- 4025 PUSH2 0x0220
  xs 0x402b (.push [0x01, 0x60] (by decide)) ri_push  -- 4028 PUSH2 0x0160
  xl 0x402c 0x160  -- 402b MLOAD
  xs 0x402e (.push [0x03] (by decide)) ri_push  -- 402c PUSH1 0x03
  xs 0x402f (.reg (.dup 1)) (ri_dup (by rfl))  -- 402e DUP2
  xs 0x4030 (.reg .lt) ri_lt  -- 402f LT
  xs 0x4033 (.push [0x40, 0x38] (by decide)) ri_push  -- 4030 PUSH2 0x4038
  xji 0x4034 0x4038 hw
  · xdead
  clear hw
  xjd 0x4039  -- 4038 JUMPDEST
  xs 0x403b (.push [0x20] (by decide)) ri_push  -- 4039 PUSH1 0x20
  xs 0x403c (.reg .mul) ri_mul  -- 403b MUL
  xs 0x403d (.reg .add) ri_add  -- 403c ADD
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x403e) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x220) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) sr
  clear sr
  xs 0x403f (.reg (.dup 0)) (ri_dup (by rfl))  -- 403e DUP1
  xs 0x4040 (.reg (.dup 0)) (ri_dup (by rfl))  -- 403f DUP1
  xs 0x4043 (.push [0x40, 0x48] (by decide)) ri_push  -- 4040 PUSH2 0x4048
  xji 0x4044 0x4048 hw
  · xdead
  have hp := hw
  clear hw
  xjd 0x4049  -- 4048 JUMPDEST
  xs 0x404a (.reg (.dup 2)) (ri_dup (by rfl))  -- 4049 DUP3
  xs 0x404b (.reg .div) ri_div  -- 404a DIV
  xs 0x404c (.reg (.swap 0)) (ri_swap (by rfl))  -- 404b SWAP1
  xs 0x404d (.reg .pop) ri_pop  -- 404c POP
  xs 0x404e (.reg (.swap 0)) (ri_swap (by rfl))  -- 404d SWAP1
  xs 0x404f (.reg .pop) ri_pop  -- 404e POP
  xs 0x4052 (.push [0x07, 0x00] (by decide)) ri_push  -- 404f PUSH2 0x0700
  xsw 0x4053 0x700  -- 4052 MSTORE
  xs 0x4056 (.push [0x07, 0x20] (by decide)) ri_push  -- 4053 PUSH2 0x0720
  xs 0x4058 (.push [0x00] (by decide)) ri_push  -- 4056 PUSH1 0x00
  xs 0x405a (.push [0x03] (by decide)) ri_push  -- 4058 PUSH1 0x03
  xs 0x405b (.reg (.dup 1)) (ri_dup (by rfl))  -- 405a DUP2
  xs 0x405c (.reg (.dup 3)) (ri_dup (by rfl))  -- 405b DUP4
  xsw 0x405d 0x720  -- 405c MSTORE
  xs 0x405e (.reg .add) ri_add  -- 405d ADD
  refine ⟨y, hi, _, _, hy, hs1, hp, h, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
