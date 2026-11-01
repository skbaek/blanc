import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceFront
import Blanc.Lift.Curve3Pool.Walk.AutoStep

/-!
# `remove_liquidity_imbalance` on the word carrier, part 2: `D0` and `new_balances`

`xa_rli_d0` (`0x31b7` → `0x32ba`): the frame save of `[0x140, 0x360)`, `D0 = get_D_mem(old,
amp)` (crossed with `xa_vGetDMem`), the restore, `D0` at `0x340`, and the unrolled loop
`new_balances[i] -= amounts[i]` (checked) over the counter at `0x460`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}

-- SEGMENT: rliD0
/-- **`D0` and `new_balances`** (`0x31b7` → `0x32ba`). -/
theorem xa_rli_d0 (hc : Cert.CheckedM code cert mems true)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    {M : Mem} {T F AF A o0 o1 o2 : B256}
    (hV : VW M [(0x360, Bytes.toB256 [1, 64]), (0x140, T), (0x1e0, F), (0x200, AF), (0x220, A),
      (0x280, o0), (0x2a0, o1), (0x2c0, o2), (0x2e0, o0), (0x300, o1), (0x320, o2)])
    (h : XAt sevm post 0x31b7 (St b [] M G) L) :
    ∃ (D0 : B256) (M' : Mem) (G' : Nat),
      getDMem ⟨o0.toNat, o1.toNat, o2.toNat⟩ A.toNat = some D0.toNat ∧
      ¬ o0 < Sevm.dataWord sevm (Bytes.toB256 [4]) ∧
      ¬ o1 < Sevm.dataWord sevm (Bytes.toB256 [0x24]) ∧
      ¬ o2 < Sevm.dataWord sevm (Bytes.toB256 [0x44]) ∧
      XAt sevm post 0x32ba (St b [] M' G') L ∧
      VW M' [(0x340, D0), (0x140, T), (0x1e0, F), (0x200, AF), (0x220, A), (0x280, o0),
        (0x2a0, o1), (0x2c0, o2), (0x2e0, o0 - Sevm.dataWord sevm (Bytes.toB256 [4])),
        (0x300, o1 - Sevm.dataWord sevm (Bytes.toB256 [0x24])),
        (0x320, o2 - Sevm.dataWord sevm (Bytes.toB256 [0x44]))] := by
  have hF : Words M [(0x140, T), (0x1e0, F), (0x200, AF), (0x220, A), (0x280, o0), (0x2a0, o1), (0x2c0, o2),
      (0x2e0, o0), (0x300, o1), (0x320, o2)] := hV.words.sub (by
    simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self])
  -- the save loop over [0x140, 0x360)
  obtain ⟨ws, M1, _, hws, rfl, h, hV1⟩ := xa_saveV (H := 0x31b7)
    (t := ⟨0x03, 0x60, 0x03, 0x60, 0x31, 0xd9, 0x31, 0xb7⟩) (lo := 0x140) (n := 17) vsave
    (by decide) hV (by rfl) (by decide) (by decide) (by decide) h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 3
  xl 0x31e2 0x280  -- 31e1 MLOAD
  xs 0x31e3 (.reg (.dup 2)) (ri_dup (by rfl))  -- 31e2 DUP3
  xsw 0x31e4 0x380  -- 31e3 MSTORE
  xa 3
  xl 0x31e9 0x2a0  -- 31e8 MLOAD
  xa 3
  xsw 0x31ee 0x3a0  -- 31ed MSTORE
  xa 3
  xl 0x31f3 0x2c0  -- 31f2 MLOAD
  xa 3
  xsw 0x31f8 0x3c0  -- 31f7 MSTORE
  xa 3
  xl 0x31fe 0x220  -- 31fd MLOAD
  xs 0x3201 (.push [0x03, 0xe0] (by decide)) ri_push  -- 31fe PUSH2 0x03e0
  xsw 0x3202 0x3e0  -- 3201 MSTORE
  xs 0x3205 (.push [0x03, 0xe0] (by decide)) ri_push  -- 3202 PUSH2 0x03e0
  xl 0x3206 0x3e0  -- 3205 MLOAD
  xs 0x3209 (.push [0x03, 0xc0] (by decide)) ri_push  -- 3206 PUSH2 0x03c0
  xl 0x320a 0x3c0  -- 3209 MLOAD
  xs 0x320d (.push [0x03, 0xa0] (by decide)) ri_push  -- 320a PUSH2 0x03a0
  xl 0x320e 0x3a0  -- 320d MLOAD
  xs 0x3211 (.push [0x03, 0x80] (by decide)) ri_push  -- 320e PUSH2 0x0380
  xl 0x3212 0x380  -- 3211 MLOAD
  xs 0x3214 (.push [0x06] (by decide)) ri_push  -- 3212 PUSH1 0x06
  cvpc 0x3215  -- 3214 PC
  xa 2
  xjmp 0x7b7  -- 3219 JUMP
  obtain ⟨D0, M3, _, h, hD0, hV1⟩ := xa_vGetDMem hc hcode hfork hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xa 2
  xsw 0x321f 0x440  -- 321e MSTORE
  xa 2
  xsw 0x3226 0x360  -- 3225 MSTORE
  -- the restore loop over [0x140, 0x360)
  rw [← List.append_nil (frameWords _ _ _).reverse] at h
  obtain ⟨M4, _, h, hV1⟩ := xa_restoreFrameV (H := 0x3226)
    (t := ⟨0x03, 0x60, 0x01, 0x40, 0x32, 0x49, 0x32, 0x26⟩) (lo := 0x140) (n := 17) vrestore
    (by decide) (by decide) (by decide) hV (by rfl) (by decide) (by decide) hF (by
      intro o v hm
      refine ⟨(o - 0x140) / 32, ?_, ?_⟩ <;>
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm <;>
      rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide) h
  simp only [List.cons_append, List.nil_append] at hV1
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xs 0x324d (.push [0x04, 0x40] (by decide)) ri_push  -- 324a PUSH2 0x0440
  xl 0x324e 0x440  -- 324d MLOAD
  xs 0x3251 (.push [0x03, 0x40] (by decide)) ri_push  -- 324e PUSH2 0x0340
  xsw 0x3252 0x340  -- 3251 MSTORE
  xa 5
  xsw 0x325c 0x460  -- 325b MSTORE
  xs 0x325d (.reg .add) ri_add  -- 325c ADD
  -- iteration 0
  xa 3
  xl 0x3265 0x460  -- 3264 MLOAD
  xa 4
  xji 0x326d 0x3271 hw
  · xdead
  clear hw
  xa 5
  xl 0x3278 0x2e0  -- 3277 MLOAD
  xa 2
  xl 0x327e 0x460  -- 327d MLOAD
  xa 4
  xji 0x3286 0x328a hw
  · xdead
  clear hw
  xa 10
  xji 0x3298 0x329c hw
  · xdead
  have hs0 := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xsw 0x32a6 0x2e0  -- 32a5 MSTORE
  xa 3
  xl 0x32aa 0x460  -- 32a9 MLOAD
  xa 4
  xsw 0x32b0 0x460  -- 32af MSTORE
  xa 4
  xji 0x32b7 0x325d hw
  · exact absurd hw (by decide)
  clear hw
  -- iteration 1
  xa 3
  xl 0x3265 0x460  -- 3264 MLOAD
  xa 4
  xji 0x326d 0x3271 hw
  · xdead
  clear hw
  xa 5
  xl 0x3278 0x300  -- 3277 MLOAD
  xa 2
  xl 0x327e 0x460  -- 327d MLOAD
  xa 4
  xji 0x3286 0x328a hw
  · xdead
  clear hw
  xa 10
  xji 0x3298 0x329c hw
  · xdead
  have hs1 := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xsw 0x32a6 0x300  -- 32a5 MSTORE
  xa 3
  xl 0x32aa 0x460  -- 32a9 MLOAD
  xa 4
  xsw 0x32b0 0x460  -- 32af MSTORE
  xa 4
  xji 0x32b7 0x325d hw
  · exact absurd hw (by decide)
  clear hw
  -- iteration 2
  xa 3
  xl 0x3265 0x460  -- 3264 MLOAD
  xa 4
  xji 0x326d 0x3271 hw
  · xdead
  clear hw
  xa 5
  xl 0x3278 0x320  -- 3277 MLOAD
  xa 2
  xl 0x327e 0x460  -- 327d MLOAD
  xa 4
  xji 0x3286 0x328a hw
  · xdead
  clear hw
  xa 10
  xji 0x3298 0x329c hw
  · xdead
  have hs2 := B256.not_lt_of_ltCheck_eq_zero (B256.eq_of_eqCheck_ne_zero hw)
  clear hw
  xa 9
  xsw 0x32a6 0x320  -- 32a5 MSTORE
  xa 3
  xl 0x32aa 0x460  -- 32a9 MLOAD
  xa 4
  xsw 0x32b0 0x460  -- 32af MSTORE
  xa 4
  xji 0x32b7 0x325d hw
  rotate_left
  · exact absurd hw (by decide)
  clear hw
  xa 3
  simp only [show Bytes.toB256 [32] * Bytes.toB256 [0] + Bytes.toB256 [4] = Bytes.toB256 [4] from by
      decide,
    show Bytes.toB256 [32] * (Bytes.toB256 [1] + Bytes.toB256 [0]) + Bytes.toB256 [4] =
      Bytes.toB256 [0x24] from by decide,
    show Bytes.toB256 [32] * (Bytes.toB256 [1] + (Bytes.toB256 [1] + Bytes.toB256 [0])) +
      Bytes.toB256 [4] = Bytes.toB256 [0x44] from by decide] at hs0 hs1 hs2 hV
  refine ⟨D0, _, _, hD0, hs0, hs1, hs2, h, hV.sub ?_⟩
  simp only [List.cons_subset, List.mem_cons, true_or, or_true, List.nil_subset, and_self]

end

end Blanc.Lift.Curve3Pool
