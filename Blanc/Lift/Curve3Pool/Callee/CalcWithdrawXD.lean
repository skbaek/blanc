import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawXLoop

/-! # `_calc_withdraw_one_coin`: the second `get_y_D`, `dy`, the fee, the return -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- `dy = (xp_reduced[i] - y - 1) / PRECISION_MUL[i]`, as words. -/
abbrev cwDy (i r0 r1 r2 y2 : B256) : B256 :=
  (pickWord3 i.toNat r0 r1 r2 - y2 - Bytes.toB256 [1]) / pickWord3 i.toNat cwP1 cwPm cwPm

section

variable {sevm : Sevm} {post b : Devm} {ρ : B256} {S : List B256} {M : Mem} {G : Nat}
  {L : List Exec.Frame}

-- SEGMENT: cwD
/-- **From the fee loop's exit (`0x41db`) to the return to `ρ`**: `get_y_D(amp, i, xp_reduced,
D1)` inside the save of `[0x140, 0x780)`, the checked `dy = (xp_reduced[i] - y - 1) /
PRECISION_MUL[i]` and `dy_0 - dy`, returned as two words. -/
theorem xa_cw_d (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {a i A F T x0 x1 x2 D0 D1 y dy0 r0 r1 r2 ck : B256} (hi : i.toNat < 3)
    (hV : VW M [(0x720, ck), (0x700, dy0), (0x5a0, y), (0x580, r2), (0x560, r1),
      (0x540, r0), (0x520, D1), (0x400, D0), (0x360, x2), (0x340, x1), (0x320, x0),
      (0x280, T), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x200, F), (0x1a0, A),
      (0x180, ρ), (0x160, i), (0x140, a)])
    (h : XAt sevm post 0x41db
      (St b ((Bytes.toB256 [3] + Bytes.toB256 [0]) :: Bytes.toB256 [7, 32] :: S) M G) L) :
    ∃ (y2 : B256) (M' : Mem) (G' : Nat),
      getYDChk A.toNat ⟨i.toNat, hi⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get D1.toNat =
        some y2.toNat ∧
      y2.toNat ≤ (pickWord3 i.toNat r0 r1 r2).toNat ∧
      (Bytes.toB256 [1]).toNat ≤ (pickWord3 i.toNat r0 r1 r2 - y2).toNat ∧
      pickWord3 i.toNat cwP1 cwPm cwPm ≠ 0 ∧ (cwDy i r0 r1 r2 y2).toNat ≤ dy0.toNat ∧
      XAt sevm post ρ.toNat
        (St b (cwDy i r0 r1 r2 y2 :: (dy0 - cwDy i r0 r1 r2 y2) :: S) M' G') L ∧
      VW M' [] := by
  xjd 0x41dc  -- 41db JUMPDEST
  xs 0x41dd (.reg .pop) ri_pop  -- 41dc POP
  xs 0x41de (.reg .pop) ri_pop  -- 41dd POP
  xs 0x41e1 (.push [0x05, 0x40] (by decide)) ri_push  -- 41de PUSH2 0x0540
  xs 0x41e4 (.push [0x01, 0x60] (by decide)) ri_push  -- 41e1 PUSH2 0x0160
  xl 0x41e5 0x160  -- 41e4 MLOAD
  xs 0x41e7 (.push [0x03] (by decide)) ri_push  -- 41e5 PUSH1 0x03
  xs 0x41e8 (.reg (.dup 1)) (ri_dup (by rfl))  -- 41e7 DUP2
  xs 0x41e9 (.reg .lt) ri_lt  -- 41e8 LT
  xs 0x41ec (.push [0x41, 0xf1] (by decide)) ri_push  -- 41e9 PUSH2 0x41f1
  xji 0x41ed 0x41f1 hw
  · xdead
  clear hw
  xjd 0x41f2  -- 41f1 JUMPDEST
  xs 0x41f4 (.push [0x20] (by decide)) ri_push  -- 41f2 PUSH1 0x20
  xs 0x41f5 (.reg .mul) ri_mul  -- 41f4 MUL
  xs 0x41f6 (.reg .add) ri_add  -- 41f5 ADD
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x41f7) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x540) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) sr
  clear sr
  xs 0x41fa (.push [0x01, 0x40] (by decide)) ri_push  -- 41f7 PUSH2 0x0140
  xs 0x41fd (.push [0x07, 0x80] (by decide)) ri_push  -- 41fa PUSH2 0x0780
  xsw 0x41fe 0x780  -- 41fd MSTORE
  have hF : Words _ [(0x700, dy0), (0x260, cwPm), (0x240, cwPm), (0x220, cwP1), (0x180, ρ), (0x160, i)] := hV.words.sub (by
    simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])
  -- the save loop over [0x140, 0x780)
  obtain ⟨ws, M1, _, hws, rfl, h, hV1⟩ := xa_saveV (H := 0x41fe)
    (t := ⟨0x07, 0x80, 0x07, 0x80, 0x42, 0x20, 0x41, 0xfe⟩) (lo := 0x140) (n := 50) vsave
    (by decide) hV (by rfl) (by decide) (by decide) (by decide) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0x4224 (.push [0x01, 0xa0] (by decide)) ri_push  -- 4221 PUSH2 0x01a0
  xl 0x4225 0x1a0  -- 4224 MLOAD
  xs 0x4228 (.push [0x07, 0xa0] (by decide)) ri_push  -- 4225 PUSH2 0x07a0
  xsw 0x4229 0x7a0  -- 4228 MSTORE
  xs 0x422c (.push [0x01, 0x60] (by decide)) ri_push  -- 4229 PUSH2 0x0160
  xl 0x422d 0x160  -- 422c MLOAD
  xs 0x4230 (.push [0x07, 0xc0] (by decide)) ri_push  -- 422d PUSH2 0x07c0
  xsw 0x4231 0x7c0  -- 4230 MSTORE
  xs 0x4234 (.push [0x07, 0xe0] (by decide)) ri_push  -- 4231 PUSH2 0x07e0
  xs 0x4237 (.push [0x05, 0x40] (by decide)) ri_push  -- 4234 PUSH2 0x0540
  xs 0x4238 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4237 DUP1
  xl 0x4239 0x540  -- 4238 MLOAD
  xs 0x423a (.reg (.dup 2)) (ri_dup (by rfl))  -- 4239 DUP3
  xsw 0x423b 0x7e0  -- 423a MSTORE
  xs 0x423c (.reg (.dup 0)) (ri_dup (by rfl))  -- 423b DUP1
  xs 0x423e (.push [0x20] (by decide)) ri_push  -- 423c PUSH1 0x20
  xs 0x423f (.reg .add) ri_add  -- 423e ADD
  xl 0x4240 0x560  -- 423f MLOAD
  xs 0x4241 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4240 DUP3
  xs 0x4243 (.push [0x20] (by decide)) ri_push  -- 4241 PUSH1 0x20
  xs 0x4244 (.reg .add) ri_add  -- 4243 ADD
  xsw 0x4245 0x800  -- 4244 MSTORE
  xs 0x4246 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4245 DUP1
  xs 0x4248 (.push [0x40] (by decide)) ri_push  -- 4246 PUSH1 0x40
  xs 0x4249 (.reg .add) ri_add  -- 4248 ADD
  xl 0x424a 0x580  -- 4249 MLOAD
  xs 0x424b (.reg (.dup 2)) (ri_dup (by rfl))  -- 424a DUP3
  xs 0x424d (.push [0x40] (by decide)) ri_push  -- 424b PUSH1 0x40
  xs 0x424e (.reg .add) ri_add  -- 424d ADD
  xsw 0x424f 0x820  -- 424e MSTORE
  xs 0x4250 (.reg .pop) ri_pop  -- 424f POP
  xs 0x4251 (.reg .pop) ri_pop  -- 4250 POP
  xs 0x4254 (.push [0x05, 0x20] (by decide)) ri_push  -- 4251 PUSH2 0x0520
  xl 0x4255 0x520  -- 4254 MLOAD
  xs 0x4258 (.push [0x08, 0x40] (by decide)) ri_push  -- 4255 PUSH2 0x0840
  xsw 0x4259 0x840  -- 4258 MSTORE
  xs 0x425c (.push [0x08, 0x40] (by decide)) ri_push  -- 4259 PUSH2 0x0840
  xl 0x425d 0x840  -- 425c MLOAD
  xs 0x4260 (.push [0x08, 0x20] (by decide)) ri_push  -- 425d PUSH2 0x0820
  xl 0x4261 0x820  -- 4260 MLOAD
  xs 0x4264 (.push [0x08, 0x00] (by decide)) ri_push  -- 4261 PUSH2 0x0800
  xl 0x4265 0x800  -- 4264 MLOAD
  xs 0x4268 (.push [0x07, 0xe0] (by decide)) ri_push  -- 4265 PUSH2 0x07e0
  xl 0x4269 0x7e0  -- 4268 MLOAD
  xs 0x426c (.push [0x07, 0xc0] (by decide)) ri_push  -- 4269 PUSH2 0x07c0
  xl 0x426d 0x7c0  -- 426c MLOAD
  xs 0x4270 (.push [0x07, 0xa0] (by decide)) ri_push  -- 426d PUSH2 0x07a0
  xl 0x4271 0x7a0  -- 4270 MLOAD
  xs 0x4273 (.push [0x06] (by decide)) ri_push  -- 4271 PUSH1 0x06
  cvpc 0x4274  -- 4273 PC
  xs 0x4275 (.reg .add) ri_add  -- 4274 ADD
  xs 0x4278 (.push [0x39, 0x99] (by decide)) ri_push  -- 4275 PUSH2 0x3999
  xjmp 0x3999  -- 4278 JUMP
  have hcov := (hV.words 0x840 _ List.mem_cons_self).1
  obtain ⟨y2, M2, _, h, hi', hy2, hV1⟩ := xa_vGetYD hc hcode hfork hV (by omega) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xjd 0x427a  -- 4279 JUMPDEST
  xs 0x427d (.push [0x08, 0xa0] (by decide)) ri_push  -- 427a PUSH2 0x08a0
  xsw 0x427e 0x8a0  -- 427d MSTORE
  xs 0x4281 (.push [0x07, 0x60] (by decide)) ri_push  -- 427e PUSH2 0x0760
  xs 0x4284 (.push [0x07, 0x80] (by decide)) ri_push  -- 4281 PUSH2 0x0780
  xsw 0x4285 0x780  -- 4284 MSTORE
  -- the restore loop over [0x140, 0x780)
  obtain ⟨M3, _, h, hV1⟩ := xa_restoreFrameV (H := 0x4285)
    (t := ⟨0x07, 0x80, 0x01, 0x40, 0x42, 0xa8, 0x42, 0x85⟩) (lo := 0x140) (n := 50) vrestore
    (by decide) (by decide) (by decide) hV (by rfl) (by decide) (by decide) hF (by
      intro o v hm
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨46, by decide, rfl⟩
      · exact ⟨9, by decide, rfl⟩
      · exact ⟨8, by decide, rfl⟩
      · exact ⟨7, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩) h
  simp only [List.cons_append, List.nil_append] at hV1
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0x42ac (.push [0x08, 0xa0] (by decide)) ri_push  -- 42a9 PUSH2 0x08a0
  xl 0x42ad 0x8a0  -- 42ac MLOAD
  xs 0x42ae (.reg (.dup 0)) (ri_dup (by rfl))  -- 42ad DUP1
  xs 0x42af (.reg (.dup 2)) (ri_dup (by rfl))  -- 42ae DUP3
  xs 0x42b0 (.reg .lt) ri_lt  -- 42af LT
  xs 0x42b1 (.reg .iszero) ri_iszero  -- 42b0 ISZERO
  xs 0x42b4 (.push [0x42, 0xb9] (by decide)) ri_push  -- 42b1 PUSH2 0x42b9
  xji 0x42b5 0x42b9 hw
  · xdead
  have hs0 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x42ba  -- 42b9 JUMPDEST
  xs 0x42bb (.reg (.dup 0)) (ri_dup (by rfl))  -- 42ba DUP1
  xs 0x42bc (.reg (.dup 2)) (ri_dup (by rfl))  -- 42bb DUP3
  xs 0x42bd (.reg .sub) ri_sub  -- 42bc SUB
  xs 0x42be (.reg (.swap 0)) (ri_swap (by rfl))  -- 42bd SWAP1
  xs 0x42bf (.reg .pop) ri_pop  -- 42be POP
  xs 0x42c0 (.reg (.swap 0)) (ri_swap (by rfl))  -- 42bf SWAP1
  xs 0x42c1 (.reg .pop) ri_pop  -- 42c0 POP
  xs 0x42c4 (.push [0x07, 0x60] (by decide)) ri_push  -- 42c1 PUSH2 0x0760
  xsw 0x42c5 0x760  -- 42c4 MSTORE
  xs 0x42c8 (.push [0x07, 0x60] (by decide)) ri_push  -- 42c5 PUSH2 0x0760
  xl 0x42c9 0x760  -- 42c8 MLOAD
  xs 0x42cb (.push [0x01] (by decide)) ri_push  -- 42c9 PUSH1 0x01
  xs 0x42cc (.reg (.dup 0)) (ri_dup (by rfl))  -- 42cb DUP1
  xs 0x42cd (.reg (.dup 2)) (ri_dup (by rfl))  -- 42cc DUP3
  xs 0x42ce (.reg .lt) ri_lt  -- 42cd LT
  xs 0x42cf (.reg .iszero) ri_iszero  -- 42ce ISZERO
  xs 0x42d2 (.push [0x42, 0xd7] (by decide)) ri_push  -- 42cf PUSH2 0x42d7
  xji 0x42d3 0x42d7 hw
  · xdead
  have hs1 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x42d8  -- 42d7 JUMPDEST
  xs 0x42d9 (.reg (.dup 0)) (ri_dup (by rfl))  -- 42d8 DUP1
  xs 0x42da (.reg (.dup 2)) (ri_dup (by rfl))  -- 42d9 DUP3
  xs 0x42db (.reg .sub) ri_sub  -- 42da SUB
  xs 0x42dc (.reg (.swap 0)) (ri_swap (by rfl))  -- 42db SWAP1
  xs 0x42dd (.reg .pop) ri_pop  -- 42dc POP
  xs 0x42de (.reg (.swap 0)) (ri_swap (by rfl))  -- 42dd SWAP1
  xs 0x42df (.reg .pop) ri_pop  -- 42de POP
  xs 0x42e2 (.push [0x02, 0x20] (by decide)) ri_push  -- 42df PUSH2 0x0220
  xs 0x42e5 (.push [0x01, 0x60] (by decide)) ri_push  -- 42e2 PUSH2 0x0160
  xl 0x42e6 0x160  -- 42e5 MLOAD
  xs 0x42e8 (.push [0x03] (by decide)) ri_push  -- 42e6 PUSH1 0x03
  xs 0x42e9 (.reg (.dup 1)) (ri_dup (by rfl))  -- 42e8 DUP2
  xs 0x42ea (.reg .lt) ri_lt  -- 42e9 LT
  xs 0x42ed (.push [0x42, 0xf2] (by decide)) ri_push  -- 42ea PUSH2 0x42f2
  xji 0x42ee 0x42f2 hw
  · xdead
  clear hw
  xjd 0x42f3  -- 42f2 JUMPDEST
  xs 0x42f5 (.push [0x20] (by decide)) ri_push  -- 42f3 PUSH1 0x20
  xs 0x42f6 (.reg .mul) ri_mul  -- 42f5 MUL
  xs 0x42f7 (.reg .add) ri_add  -- 42f6 ADD
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x42f8) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x220) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) sr
  clear sr
  xs 0x42f9 (.reg (.dup 0)) (ri_dup (by rfl))  -- 42f8 DUP1
  xs 0x42fa (.reg (.dup 0)) (ri_dup (by rfl))  -- 42f9 DUP1
  xs 0x42fd (.push [0x43, 0x02] (by decide)) ri_push  -- 42fa PUSH2 0x4302
  xji 0x42fe 0x4302 hw
  · xdead
  have hp := hw
  clear hw
  xjd 0x4303  -- 4302 JUMPDEST
  xs 0x4304 (.reg (.dup 2)) (ri_dup (by rfl))  -- 4303 DUP3
  xs 0x4305 (.reg .div) ri_div  -- 4304 DIV
  xs 0x4306 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4305 SWAP1
  xs 0x4307 (.reg .pop) ri_pop  -- 4306 POP
  xs 0x4308 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4307 SWAP1
  xs 0x4309 (.reg .pop) ri_pop  -- 4308 POP
  xs 0x430c (.push [0x07, 0x60] (by decide)) ri_push  -- 4309 PUSH2 0x0760
  xsw 0x430d 0x760  -- 430c MSTORE
  xs 0x4310 (.push [0x08, 0xc0] (by decide)) ri_push  -- 430d PUSH2 0x08c0
  xs 0x4311 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4310 DUP1
  xs 0x4312 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4311 DUP1
  xs 0x4313 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4312 DUP1
  xs 0x4316 (.push [0x07, 0x60] (by decide)) ri_push  -- 4313 PUSH2 0x0760
  xl 0x4317 0x760  -- 4316 MLOAD
  xs 0x4318 (.reg (.dup 1)) (ri_dup (by rfl))  -- 4317 DUP2
  xsw 0x4319 0x8c0  -- 4318 MSTORE
  xs 0x431a (.reg .pop) ri_pop  -- 4319 POP
  xs 0x431b (.reg .pop) ri_pop  -- 431a POP
  xs 0x431d (.push [0x20] (by decide)) ri_push  -- 431b PUSH1 0x20
  xs 0x431e (.reg (.dup 1)) (ri_dup (by rfl))  -- 431d DUP2
  xs 0x431f (.reg .add) ri_add  -- 431e ADD
  xs 0x4320 (.reg (.swap 0)) (ri_swap (by rfl))  -- 431f SWAP1
  xs 0x4321 (.reg .pop) ri_pop  -- 4320 POP
  xs 0x4322 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4321 DUP1
  xs 0x4323 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4322 DUP1
  xs 0x4326 (.push [0x07, 0x00] (by decide)) ri_push  -- 4323 PUSH2 0x0700
  xl 0x4327 0x700  -- 4326 MLOAD
  xs 0x432a (.push [0x07, 0x60] (by decide)) ri_push  -- 4327 PUSH2 0x0760
  xl 0x432b 0x760  -- 432a MLOAD
  xs 0x432c (.reg (.dup 0)) (ri_dup (by rfl))  -- 432b DUP1
  xs 0x432d (.reg (.dup 2)) (ri_dup (by rfl))  -- 432c DUP3
  xs 0x432e (.reg .lt) ri_lt  -- 432d LT
  xs 0x432f (.reg .iszero) ri_iszero  -- 432e ISZERO
  xs 0x4332 (.push [0x43, 0x37] (by decide)) ri_push  -- 432f PUSH2 0x4337
  xji 0x4333 0x4337 hw
  · xdead
  have hs2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xjd 0x4338  -- 4337 JUMPDEST
  xs 0x4339 (.reg (.dup 0)) (ri_dup (by rfl))  -- 4338 DUP1
  xs 0x433a (.reg (.dup 2)) (ri_dup (by rfl))  -- 4339 DUP3
  xs 0x433b (.reg .sub) ri_sub  -- 433a SUB
  xs 0x433c (.reg (.swap 0)) (ri_swap (by rfl))  -- 433b SWAP1
  xs 0x433d (.reg .pop) ri_pop  -- 433c POP
  xs 0x433e (.reg (.swap 0)) (ri_swap (by rfl))  -- 433d SWAP1
  xs 0x433f (.reg .pop) ri_pop  -- 433e POP
  xs 0x4340 (.reg (.dup 1)) (ri_dup (by rfl))  -- 433f DUP2
  xsw 0x4341 0x8e0  -- 4340 MSTORE
  xs 0x4342 (.reg .pop) ri_pop  -- 4341 POP
  xs 0x4343 (.reg .pop) ri_pop  -- 4342 POP
  xs 0x4345 (.push [0x40] (by decide)) ri_push  -- 4343 PUSH1 0x40
  xs 0x4346 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4345 SWAP1
  xs 0x4347 (.reg .pop) ri_pop  -- 4346 POP
  xs 0x4348 (.reg (.swap 0)) (ri_swap (by rfl))  -- 4347 SWAP1
  xs 0x4349 (.reg .pop) ri_pop  -- 4348 POP
  xs 0x434b (.push [0xc0] (by decide)) ri_push  -- 4349 PUSH1 0xc0
  xsw 0x434c 0xc0  -- 434b MSTORE
  xs 0x434e (.push [0xc0] (by decide)) ri_push  -- 434c PUSH1 0xc0
  xl 0x434f 0xc0  -- 434e MLOAD
  xs 0x4352 (.push [0x09, 0x00] (by decide)) ri_push  -- 434f PUSH2 0x0900
  xsw 0x4353 0x900  -- 4352 MSTORE
  -- the return loop, unrolled
  xjd 0x4354  -- 4353 JUMPDEST
  xs 0x4356 (.push [0x00] (by decide)) ri_push  -- 4354 PUSH1 0x00
  xs 0x4359 (.push [0x09, 0x00] (by decide)) ri_push  -- 4356 PUSH2 0x0900
  xl 0x435a 0x900  -- 4359 MLOAD
  xs 0x435b (.reg .gt) ri_gt  -- 435a GT
  xs 0x435c (.reg .iszero) ri_iszero  -- 435b ISZERO
  xs 0x435d (.reg .iszero) ri_iszero  -- 435c ISZERO
  xs 0x4360 (.push [0x43, 0x65] (by decide)) ri_push  -- 435d PUSH2 0x4365
  xji 0x4361 0x4365 hw
  · exact absurd hw (by decide)
  xjd 0x4366  -- 4365 JUMPDEST
  xs 0x4368 (.push [0x20] (by decide)) ri_push  -- 4366 PUSH1 0x20
  xs 0x436b (.push [0x09, 0x00] (by decide)) ri_push  -- 4368 PUSH2 0x0900
  xl 0x436c 0x900  -- 436b MLOAD
  xs 0x436d (.reg .sub) ri_sub  -- 436c SUB
  xs 0x4370 (.push [0x08, 0xc0] (by decide)) ri_push  -- 436d PUSH2 0x08c0
  xs 0x4371 (.reg .add) ri_add  -- 4370 ADD
  xl 0x4372 0x8e0  -- 4371 MLOAD
  xs 0x4374 (.push [0x20] (by decide)) ri_push  -- 4372 PUSH1 0x20
  xs 0x4377 (.push [0x09, 0x00] (by decide)) ri_push  -- 4374 PUSH2 0x0900
  xl 0x4378 0x900  -- 4377 MLOAD
  xs 0x4379 (.reg .sub) ri_sub  -- 4378 SUB
  xs 0x437c (.push [0x09, 0x00] (by decide)) ri_push  -- 4379 PUSH2 0x0900
  xsw 0x437d 0x900  -- 437c MSTORE
  xs 0x4380 (.push [0x43, 0x53] (by decide)) ri_push  -- 437d PUSH2 0x4353
  xjmp 0x4353  -- 4380 JUMP
  xjd 0x4354  -- 4353 JUMPDEST
  xs 0x4356 (.push [0x00] (by decide)) ri_push  -- 4354 PUSH1 0x00
  xs 0x4359 (.push [0x09, 0x00] (by decide)) ri_push  -- 4356 PUSH2 0x0900
  xl 0x435a 0x900  -- 4359 MLOAD
  xs 0x435b (.reg .gt) ri_gt  -- 435a GT
  xs 0x435c (.reg .iszero) ri_iszero  -- 435b ISZERO
  xs 0x435d (.reg .iszero) ri_iszero  -- 435c ISZERO
  xs 0x4360 (.push [0x43, 0x65] (by decide)) ri_push  -- 435d PUSH2 0x4365
  xji 0x4361 0x4365 hw
  · exact absurd hw (by decide)
  xjd 0x4366  -- 4365 JUMPDEST
  xs 0x4368 (.push [0x20] (by decide)) ri_push  -- 4366 PUSH1 0x20
  xs 0x436b (.push [0x09, 0x00] (by decide)) ri_push  -- 4368 PUSH2 0x0900
  xl 0x436c 0x900  -- 436b MLOAD
  xs 0x436d (.reg .sub) ri_sub  -- 436c SUB
  xs 0x4370 (.push [0x08, 0xc0] (by decide)) ri_push  -- 436d PUSH2 0x08c0
  xs 0x4371 (.reg .add) ri_add  -- 4370 ADD
  xl 0x4372 0x8c0  -- 4371 MLOAD
  xs 0x4374 (.push [0x20] (by decide)) ri_push  -- 4372 PUSH1 0x20
  xs 0x4377 (.push [0x09, 0x00] (by decide)) ri_push  -- 4374 PUSH2 0x0900
  xl 0x4378 0x900  -- 4377 MLOAD
  xs 0x4379 (.reg .sub) ri_sub  -- 4378 SUB
  xs 0x437c (.push [0x09, 0x00] (by decide)) ri_push  -- 4379 PUSH2 0x0900
  xsw 0x437d 0x900  -- 437c MSTORE
  xs 0x4380 (.push [0x43, 0x53] (by decide)) ri_push  -- 437d PUSH2 0x4353
  xjmp 0x4353  -- 4380 JUMP
  xjd 0x4354  -- 4353 JUMPDEST
  xs 0x4356 (.push [0x00] (by decide)) ri_push  -- 4354 PUSH1 0x00
  xs 0x4359 (.push [0x09, 0x00] (by decide)) ri_push  -- 4356 PUSH2 0x0900
  xl 0x435a 0x900  -- 4359 MLOAD
  xs 0x435b (.reg .gt) ri_gt  -- 435a GT
  xs 0x435c (.reg .iszero) ri_iszero  -- 435b ISZERO
  xs 0x435d (.reg .iszero) ri_iszero  -- 435c ISZERO
  xs 0x4360 (.push [0x43, 0x65] (by decide)) ri_push  -- 435d PUSH2 0x4365
  xji 0x4361 0x4365 hw
  swap
  · exact absurd hw (by decide)
  xs 0x4364 (.push [0x43, 0x81] (by decide)) ri_push  -- 4361 PUSH2 0x4381
  xjmp 0x4381  -- 4364 JUMP
  xjd 0x4382  -- 4381 JUMPDEST
  xs 0x4385 (.push [0x01, 0x80] (by decide)) ri_push  -- 4382 PUSH2 0x0180
  xl 0x4386 0x180  -- 4385 MLOAD
  replace h := xa_jumpAt (pc' := ρ.toNat) (atJ hcode (by kernel_rfl)) rfl h
  obtain ⟨_, h⟩ := h
  exact ⟨y2, _, _, hy2, hs0, hs1, hp, hs2, h, hV.sub (List.nil_subset _)⟩

end

end Blanc.Lift.Curve3Pool
