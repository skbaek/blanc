import Blanc.Lift.HistIdentityCall
import Blanc.Lift.Curve3Pool.Callee.CalcWithdrawXLoop
import Blanc.Lift.Curve3Pool.Walk.AutoStep

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
    (hcode : sevm.code = code) (hfork : HistFork sevm.benvStat.fork)
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
  xa 5
  xl 0x41e5 0x160  -- 41e4 MLOAD
  xa 4
  xji 0x41ed 0x41f1 hw
  · xdead
  clear hw
  xa 4
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x41f7) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x540) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) sr
  clear sr
  xa 2
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
  xa 3
  xl 0x4239 0x540  -- 4238 MLOAD
  xs 0x423a (.reg (.dup 2)) (ri_dup (by rfl))  -- 4239 DUP3
  xsw 0x423b 0x7e0  -- 423a MSTORE
  xa 3
  xl 0x4240 0x560  -- 423f MLOAD
  xa 3
  xsw 0x4245 0x800  -- 4244 MSTORE
  xa 3
  xl 0x424a 0x580  -- 4249 MLOAD
  xa 3
  xsw 0x424f 0x820  -- 424e MSTORE
  xa 3
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
  xa 2
  xjmp 0x3999  -- 4278 JUMP
  have hcov := (hV.words 0x840 _ List.mem_cons_self).1
  obtain ⟨y2, M2, _, h, hi', hy2, hV1⟩ := xa_vGetYD hc hcode hfork hV (by omega) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
  xsw 0x427e 0x8a0  -- 427d MSTORE
  xa 2
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
  xa 5
  xji 0x42b5 0x42b9 hw
  · xdead
  have hs0 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 9
  xsw 0x42c5 0x760  -- 42c4 MSTORE
  xs 0x42c8 (.push [0x07, 0x60] (by decide)) ri_push  -- 42c5 PUSH2 0x0760
  xl 0x42c9 0x760  -- 42c8 MLOAD
  xa 6
  xji 0x42d3 0x42d7 hw
  · xdead
  have hs1 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 10
  xl 0x42e6 0x160  -- 42e5 MLOAD
  xa 4
  xji 0x42ee 0x42f2 hw
  · xdead
  clear hw
  xa 4
  replace h := xa_nextAt (n := .reg .mload) (pc' := 0x42f8) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, sr, h⟩ := h
  obtain ⟨_, rfl⟩ := ri_mloadWord3 (base := 0x220) hV.words hV.al
    (wlook_mem (by rfl)) (wlook_mem (by rfl)) (wlook_mem (by rfl)) hi
    (by rw [word3_indexAddr hi (by decide)]; rfl) sr
  clear sr
  xa 3
  xji 0x42fe 0x4302 hw
  · xdead
  have hp := hw
  clear hw
  xa 8
  xsw 0x430d 0x760  -- 430c MSTORE
  xa 5
  xl 0x4317 0x760  -- 4316 MLOAD
  xs 0x4318 (.reg (.dup 1)) (ri_dup (by rfl))  -- 4317 DUP2
  xsw 0x4319 0x8c0  -- 4318 MSTORE
  xa 10
  xl 0x4327 0x700  -- 4326 MLOAD
  xs 0x432a (.push [0x07, 0x60] (by decide)) ri_push  -- 4327 PUSH2 0x0760
  xl 0x432b 0x760  -- 432a MLOAD
  xa 5
  xji 0x4333 0x4337 hw
  · xdead
  have hs2 := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw)
  clear hw
  xa 9
  xsw 0x4341 0x8e0  -- 4340 MSTORE
  xa 8
  xsw 0x434c 0xc0  -- 434b MSTORE
  xs 0x434e (.push [0xc0] (by decide)) ri_push  -- 434c PUSH1 0xc0
  xl 0x434f 0xc0  -- 434e MLOAD
  xs 0x4352 (.push [0x09, 0x00] (by decide)) ri_push  -- 434f PUSH2 0x0900
  xsw 0x4353 0x900  -- 4352 MSTORE
  -- the return loop, unrolled
  xa 3
  xl 0x435a 0x900  -- 4359 MLOAD
  xa 4
  xji 0x4361 0x4365 hw
  · exact absurd hw (by decide)
  xa 3
  xl 0x436c 0x900  -- 436b MLOAD
  xa 3
  xl 0x4372 0x8e0  -- 4371 MLOAD
  xa 2
  xl 0x4378 0x900  -- 4377 MLOAD
  xa 2
  xsw 0x437d 0x900  -- 437c MSTORE
  xs 0x4380 (.push [0x43, 0x53] (by decide)) ri_push  -- 437d PUSH2 0x4353
  xjmp 0x4353  -- 4380 JUMP
  xa 3
  xl 0x435a 0x900  -- 4359 MLOAD
  xa 4
  xji 0x4361 0x4365 hw
  · exact absurd hw (by decide)
  xa 3
  xl 0x436c 0x900  -- 436b MLOAD
  xa 3
  xl 0x4372 0x8c0  -- 4371 MLOAD
  xa 2
  xl 0x4378 0x900  -- 4377 MLOAD
  xa 2
  xsw 0x437d 0x900  -- 437c MSTORE
  xs 0x4380 (.push [0x43, 0x53] (by decide)) ri_push  -- 437d PUSH2 0x4353
  xjmp 0x4353  -- 4380 JUMP
  xa 3
  xl 0x435a 0x900  -- 4359 MLOAD
  xa 4
  xji 0x4361 0x4365 hw
  swap
  · exact absurd hw (by decide)
  xs 0x4364 (.push [0x43, 0x81] (by decide)) ri_push  -- 4361 PUSH2 0x4381
  xjmp 0x4381  -- 4364 JUMP
  xa 2
  xl 0x4386 0x180  -- 4385 MLOAD
  replace h := xa_jumpAt (pc' := ρ.toNat) (atJ hcode (by kernel_rfl)) rfl h
  obtain ⟨_, h⟩ := h
  exact ⟨y2, _, _, hy2, hs0, hs1, hp, hs2, h, hV.sub (List.nil_subset _)⟩

end

end Blanc.Lift.Curve3Pool
