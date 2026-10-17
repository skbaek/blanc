import Blanc.Lift.Curve3Pool.Walk.ViewsCtaLoop

/-! # `calc_token_amount`: `D1 = get_D_mem(new_balances, amp)` inside the frame save -/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}

-- SEGMENT: ctaD1
/-- **From the frame save (`0xcdc`) to `D1` at `0x340`**: the save of `[0x140, 0x360)`,
`get_D_mem(new_balances, amp)`, the restore; `D0` kept at `0x200`. -/
theorem xa_cta_d1 (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {M : Mem} {D0 amp v0 v1 v2 : B256}
    (hV : VW M [(0x360, Bytes.toB256 [1, 64]), (0x200, D0), (0x140, v0), (0x160, v1),
      (0x180, v2), (0x1a0, amp)])
    (h : XAt sevm post 0xcdc (St b [] M G) L) :
    ∃ D1 M' G', getDMem ⟨v0.toNat, v1.toNat, v2.toNat⟩ amp.toNat = some D1.toNat ∧
      XAt sevm post 0xd77 (St b [] M' G') L ∧ VW M' [(0x340, D1), (0x200, D0)] := by
  have hF : Words M [(0x200, D0)] := hV.words.sub (by
    simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])
  -- the save loop over [0x140, 0x360)
  obtain ⟨ws, M1, _, hws, rfl, h, hV1⟩ := xa_saveV (H := 0xcdc)
    (t := ⟨0x03, 0x60, 0x03, 0x60, 0x0c, 0xfe, 0x0c, 0xdc⟩) (lo := 0x140) (n := 17) vsave
    (by decide) hV (by rfl) (by decide) (by decide) (by decide) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0xd02 (.push [0x03, 0x80] (by decide)) ri_push  -- cff PUSH2 0x0380
  xs 0xd05 (.push [0x01, 0x40] (by decide)) ri_push  -- d02 PUSH2 0x0140
  xs 0xd06 (.reg (.dup 0)) (ri_dup (by rfl))  -- d05 DUP1
  xl 0xd07 0x140  -- d06 MLOAD
  xs 0xd08 (.reg (.dup 2)) (ri_dup (by rfl))  -- d07 DUP3
  xsw 0xd09 0x380  -- d08 MSTORE
  xs 0xd0a (.reg (.dup 0)) (ri_dup (by rfl))  -- d09 DUP1
  xs 0xd0c (.push [0x20] (by decide)) ri_push  -- d0a PUSH1 0x20
  xs 0xd0d (.reg .add) ri_add  -- d0c ADD
  xl 0xd0e 0x160  -- d0d MLOAD
  xs 0xd0f (.reg (.dup 2)) (ri_dup (by rfl))  -- d0e DUP3
  xs 0xd11 (.push [0x20] (by decide)) ri_push  -- d0f PUSH1 0x20
  xs 0xd12 (.reg .add) ri_add  -- d11 ADD
  xsw 0xd13 0x3a0  -- d12 MSTORE
  xs 0xd14 (.reg (.dup 0)) (ri_dup (by rfl))  -- d13 DUP1
  xs 0xd16 (.push [0x40] (by decide)) ri_push  -- d14 PUSH1 0x40
  xs 0xd17 (.reg .add) ri_add  -- d16 ADD
  xl 0xd18 0x180  -- d17 MLOAD
  xs 0xd19 (.reg (.dup 2)) (ri_dup (by rfl))  -- d18 DUP3
  xs 0xd1b (.push [0x40] (by decide)) ri_push  -- d19 PUSH1 0x40
  xs 0xd1c (.reg .add) ri_add  -- d1b ADD
  xsw 0xd1d 0x3c0  -- d1c MSTORE
  xs 0xd1e (.reg .pop) ri_pop  -- d1d POP
  xs 0xd1f (.reg .pop) ri_pop  -- d1e POP
  xs 0xd22 (.push [0x01, 0xa0] (by decide)) ri_push  -- d1f PUSH2 0x01a0
  xl 0xd23 0x1a0  -- d22 MLOAD
  xs 0xd26 (.push [0x03, 0xe0] (by decide)) ri_push  -- d23 PUSH2 0x03e0
  xsw 0xd27 0x3e0  -- d26 MSTORE
  xs 0xd2a (.push [0x03, 0xe0] (by decide)) ri_push  -- d27 PUSH2 0x03e0
  xl 0xd2b 0x3e0  -- d2a MLOAD
  xs 0xd2e (.push [0x03, 0xc0] (by decide)) ri_push  -- d2b PUSH2 0x03c0
  xl 0xd2f 0x3c0  -- d2e MLOAD
  xs 0xd32 (.push [0x03, 0xa0] (by decide)) ri_push  -- d2f PUSH2 0x03a0
  xl 0xd33 0x3a0  -- d32 MLOAD
  xs 0xd36 (.push [0x03, 0x80] (by decide)) ri_push  -- d33 PUSH2 0x0380
  xl 0xd37 0x380  -- d36 MLOAD
  xs 0xd39 (.push [0x06] (by decide)) ri_push  -- d37 PUSH1 0x06
  cvpc 0xd3a  -- d39 PC
  xs 0xd3b (.reg .add) ri_add  -- d3a ADD
  xs 0xd3e (.push [0x07, 0xb7] (by decide)) ri_push  -- d3b PUSH2 0x07b7
  xjmp 0x7b7  -- d3e JUMP
  obtain ⟨D1, M3, _, h, hD1, hV1⟩ := xa_vGetDMem hc hcode hfork hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xjd 0xd40  -- d3f JUMPDEST
  xs 0xd43 (.push [0x04, 0x40] (by decide)) ri_push  -- d40 PUSH2 0x0440
  xsw 0xd44 0x440  -- d43 MSTORE
  xs 0xd47 (.push [0x03, 0x40] (by decide)) ri_push  -- d44 PUSH2 0x0340
  xs 0xd4a (.push [0x03, 0x60] (by decide)) ri_push  -- d47 PUSH2 0x0360
  xsw 0xd4b 0x360  -- d4a MSTORE
  -- the restore loop over [0x140, 0x360)
  rw [← List.append_nil (frameWords _ _ _).reverse] at h
  obtain ⟨M4, _, h, hV1⟩ := xa_restoreFrameV (H := 0xd4b)
    (t := ⟨0x03, 0x60, 0x01, 0x40, 0x0d, 0x6e, 0x0d, 0x4b⟩) (lo := 0x140) (n := 17) vrestore
    (by decide) (by decide) (by decide) hV (by rfl) (by decide) (by decide) hF (by
      intro o v hm
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      obtain ⟨rfl, -⟩ := hm
      exact ⟨6, by decide, rfl⟩) h
  rw [List.singleton_append] at hV1
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0xd72 (.push [0x04, 0x40] (by decide)) ri_push  -- d6f PUSH2 0x0440
  xl 0xd73 0x440  -- d72 MLOAD
  xs 0xd76 (.push [0x03, 0x40] (by decide)) ri_push  -- d73 PUSH2 0x0340
  xsw 0xd77 0x340  -- d76 MSTORE
  refine ⟨D1, _, _, hD1, h, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
