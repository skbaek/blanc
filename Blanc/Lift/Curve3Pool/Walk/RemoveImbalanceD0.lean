import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceFront

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
  xs 0x31dd (.push [0x03, 0x80] (by decide)) ri_push  -- 31da PUSH2 0x0380
  xs 0x31e0 (.push [0x02, 0x80] (by decide)) ri_push  -- 31dd PUSH2 0x0280
  xs 0x31e1 (.reg (.dup 0)) (ri_dup (by rfl))  -- 31e0 DUP1
  xl 0x31e2 0x280  -- 31e1 MLOAD
  xs 0x31e3 (.reg (.dup 2)) (ri_dup (by rfl))  -- 31e2 DUP3
  xsw 0x31e4 0x380  -- 31e3 MSTORE
  xs 0x31e5 (.reg (.dup 0)) (ri_dup (by rfl))  -- 31e4 DUP1
  xs 0x31e7 (.push [0x20] (by decide)) ri_push  -- 31e5 PUSH1 0x20
  xs 0x31e8 (.reg .add) ri_add  -- 31e7 ADD
  xl 0x31e9 0x2a0  -- 31e8 MLOAD
  xs 0x31ea (.reg (.dup 2)) (ri_dup (by rfl))  -- 31e9 DUP3
  xs 0x31ec (.push [0x20] (by decide)) ri_push  -- 31ea PUSH1 0x20
  xs 0x31ed (.reg .add) ri_add  -- 31ec ADD
  xsw 0x31ee 0x3a0  -- 31ed MSTORE
  xs 0x31ef (.reg (.dup 0)) (ri_dup (by rfl))  -- 31ee DUP1
  xs 0x31f1 (.push [0x40] (by decide)) ri_push  -- 31ef PUSH1 0x40
  xs 0x31f2 (.reg .add) ri_add  -- 31f1 ADD
  xl 0x31f3 0x2c0  -- 31f2 MLOAD
  xs 0x31f4 (.reg (.dup 2)) (ri_dup (by rfl))  -- 31f3 DUP3
  xs 0x31f6 (.push [0x40] (by decide)) ri_push  -- 31f4 PUSH1 0x40
  xs 0x31f7 (.reg .add) ri_add  -- 31f6 ADD
  xsw 0x31f8 0x3c0  -- 31f7 MSTORE
  xs 0x31f9 (.reg .pop) ri_pop  -- 31f8 POP
  xs 0x31fa (.reg .pop) ri_pop  -- 31f9 POP
  xs 0x31fd (.push [0x02, 0x20] (by decide)) ri_push  -- 31fa PUSH2 0x0220
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
  xs 0x3216 (.reg .add) ri_add  -- 3215 ADD
  xs 0x3219 (.push [0x07, 0xb7] (by decide)) ri_push  -- 3216 PUSH2 0x07b7
  xjmp 0x7b7  -- 3219 JUMP
  obtain ⟨D0, M3, _, h, hD0, hV1⟩ := xa_vGetDMem hc hcode hfork hV h
  clear hV
  have hV := hV1
  clear hV1
  vnorm
  xjd 0x321b  -- 321a JUMPDEST
  xs 0x321e (.push [0x04, 0x40] (by decide)) ri_push  -- 321b PUSH2 0x0440
  xsw 0x321f 0x440  -- 321e MSTORE
  xs 0x3222 (.push [0x03, 0x40] (by decide)) ri_push  -- 321f PUSH2 0x0340
  xs 0x3225 (.push [0x03, 0x60] (by decide)) ri_push  -- 3222 PUSH2 0x0360
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
  xs 0x3255 (.push [0x04, 0x60] (by decide)) ri_push  -- 3252 PUSH2 0x0460
  xs 0x3257 (.push [0x00] (by decide)) ri_push  -- 3255 PUSH1 0x00
  xs 0x3259 (.push [0x03] (by decide)) ri_push  -- 3257 PUSH1 0x03
  xs 0x325a (.reg (.dup 1)) (ri_dup (by rfl))  -- 3259 DUP2
  xs 0x325b (.reg (.dup 3)) (ri_dup (by rfl))  -- 325a DUP4
  xsw 0x325c 0x460  -- 325b MSTORE
  xs 0x325d (.reg .add) ri_add  -- 325c ADD
  -- iteration 0
  xjd 0x325e  -- 325d JUMPDEST
  xs 0x3261 (.push [0x02, 0xe0] (by decide)) ri_push  -- 325e PUSH2 0x02e0
  xs 0x3264 (.push [0x04, 0x60] (by decide)) ri_push  -- 3261 PUSH2 0x0460
  xl 0x3265 0x460  -- 3264 MLOAD
  xs 0x3267 (.push [0x03] (by decide)) ri_push  -- 3265 PUSH1 0x03
  xs 0x3268 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3267 DUP2
  xs 0x3269 (.reg .lt) ri_lt  -- 3268 LT
  xs 0x326c (.push [0x32, 0x71] (by decide)) ri_push  -- 3269 PUSH2 0x3271
  xji 0x326d 0x3271 hw
  · xdead
  clear hw
  xjd 0x3272  -- 3271 JUMPDEST
  xs 0x3274 (.push [0x20] (by decide)) ri_push  -- 3272 PUSH1 0x20
  xs 0x3275 (.reg .mul) ri_mul  -- 3274 MUL
  xs 0x3276 (.reg .add) ri_add  -- 3275 ADD
  xs 0x3277 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3276 DUP1
  xl 0x3278 0x2e0  -- 3277 MLOAD
  xs 0x327a (.push [0x04] (by decide)) ri_push  -- 3278 PUSH1 0x04
  xs 0x327d (.push [0x04, 0x60] (by decide)) ri_push  -- 327a PUSH2 0x0460
  xl 0x327e 0x460  -- 327d MLOAD
  xs 0x3280 (.push [0x03] (by decide)) ri_push  -- 327e PUSH1 0x03
  xs 0x3281 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3280 DUP2
  xs 0x3282 (.reg .lt) ri_lt  -- 3281 LT
  xs 0x3285 (.push [0x32, 0x8a] (by decide)) ri_push  -- 3282 PUSH2 0x328a
  xji 0x3286 0x328a hw
  · xdead
  clear hw
  xjd 0x328b  -- 328a JUMPDEST
  xs 0x328d (.push [0x20] (by decide)) ri_push  -- 328b PUSH1 0x20
  xs 0x328e (.reg .mul) ri_mul  -- 328d MUL
  xs 0x328f (.reg .add) ri_add  -- 328e ADD
  xs 0x3290 (.reg .calldataload) ri_calldataload  -- 328f CALLDATALOAD
  xs 0x3291 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3290 DUP1
  xs 0x3292 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3291 DUP3
  xs 0x3293 (.reg .lt) ri_lt  -- 3292 LT
  xs 0x3294 (.reg .iszero) ri_iszero  -- 3293 ISZERO
  xs 0x3297 (.push [0x32, 0x9c] (by decide)) ri_push  -- 3294 PUSH2 0x329c
  xji 0x3298 0x329c hw
  · xdead
  have hs0 := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x329d  -- 329c JUMPDEST
  xs 0x329e (.reg (.dup 0)) (ri_dup (by rfl))  -- 329d DUP1
  xs 0x329f (.reg (.dup 2)) (ri_dup (by rfl))  -- 329e DUP3
  xs 0x32a0 (.reg .sub) ri_sub  -- 329f SUB
  xs 0x32a1 (.reg (.swap 0)) (ri_swap (by rfl))  -- 32a0 SWAP1
  xs 0x32a2 (.reg .pop) ri_pop  -- 32a1 POP
  xs 0x32a3 (.reg (.swap 0)) (ri_swap (by rfl))  -- 32a2 SWAP1
  xs 0x32a4 (.reg .pop) ri_pop  -- 32a3 POP
  xs 0x32a5 (.reg (.dup 1)) (ri_dup (by rfl))  -- 32a4 DUP2
  xsw 0x32a6 0x2e0  -- 32a5 MSTORE
  xs 0x32a7 (.reg .pop) ri_pop  -- 32a6 POP
  xjd 0x32a8  -- 32a7 JUMPDEST
  xs 0x32a9 (.reg (.dup 1)) (ri_dup (by rfl))  -- 32a8 DUP2
  xl 0x32aa 0x460  -- 32a9 MLOAD
  xs 0x32ac (.push [0x01] (by decide)) ri_push  -- 32aa PUSH1 0x01
  xs 0x32ad (.reg .add) ri_add  -- 32ac ADD
  xs 0x32ae (.reg (.dup 0)) (ri_dup (by rfl))  -- 32ad DUP1
  xs 0x32af (.reg (.dup 3)) (ri_dup (by rfl))  -- 32ae DUP4
  xsw 0x32b0 0x460  -- 32af MSTORE
  xs 0x32b1 (.reg (.dup 1)) (ri_dup (by rfl))  -- 32b0 DUP2
  xs 0x32b2 (.reg .eq) ri_eq  -- 32b1 EQ
  xs 0x32b3 (.reg .iszero) ri_iszero  -- 32b2 ISZERO
  xs 0x32b6 (.push [0x32, 0x5d] (by decide)) ri_push  -- 32b3 PUSH2 0x325d
  xji 0x32b7 0x325d hw
  · exact absurd hw (by decide)
  clear hw
  -- iteration 1
  xjd 0x325e  -- 325d JUMPDEST
  xs 0x3261 (.push [0x02, 0xe0] (by decide)) ri_push  -- 325e PUSH2 0x02e0
  xs 0x3264 (.push [0x04, 0x60] (by decide)) ri_push  -- 3261 PUSH2 0x0460
  xl 0x3265 0x460  -- 3264 MLOAD
  xs 0x3267 (.push [0x03] (by decide)) ri_push  -- 3265 PUSH1 0x03
  xs 0x3268 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3267 DUP2
  xs 0x3269 (.reg .lt) ri_lt  -- 3268 LT
  xs 0x326c (.push [0x32, 0x71] (by decide)) ri_push  -- 3269 PUSH2 0x3271
  xji 0x326d 0x3271 hw
  · xdead
  clear hw
  xjd 0x3272  -- 3271 JUMPDEST
  xs 0x3274 (.push [0x20] (by decide)) ri_push  -- 3272 PUSH1 0x20
  xs 0x3275 (.reg .mul) ri_mul  -- 3274 MUL
  xs 0x3276 (.reg .add) ri_add  -- 3275 ADD
  xs 0x3277 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3276 DUP1
  xl 0x3278 0x300  -- 3277 MLOAD
  xs 0x327a (.push [0x04] (by decide)) ri_push  -- 3278 PUSH1 0x04
  xs 0x327d (.push [0x04, 0x60] (by decide)) ri_push  -- 327a PUSH2 0x0460
  xl 0x327e 0x460  -- 327d MLOAD
  xs 0x3280 (.push [0x03] (by decide)) ri_push  -- 327e PUSH1 0x03
  xs 0x3281 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3280 DUP2
  xs 0x3282 (.reg .lt) ri_lt  -- 3281 LT
  xs 0x3285 (.push [0x32, 0x8a] (by decide)) ri_push  -- 3282 PUSH2 0x328a
  xji 0x3286 0x328a hw
  · xdead
  clear hw
  xjd 0x328b  -- 328a JUMPDEST
  xs 0x328d (.push [0x20] (by decide)) ri_push  -- 328b PUSH1 0x20
  xs 0x328e (.reg .mul) ri_mul  -- 328d MUL
  xs 0x328f (.reg .add) ri_add  -- 328e ADD
  xs 0x3290 (.reg .calldataload) ri_calldataload  -- 328f CALLDATALOAD
  xs 0x3291 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3290 DUP1
  xs 0x3292 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3291 DUP3
  xs 0x3293 (.reg .lt) ri_lt  -- 3292 LT
  xs 0x3294 (.reg .iszero) ri_iszero  -- 3293 ISZERO
  xs 0x3297 (.push [0x32, 0x9c] (by decide)) ri_push  -- 3294 PUSH2 0x329c
  xji 0x3298 0x329c hw
  · xdead
  have hs1 := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x329d  -- 329c JUMPDEST
  xs 0x329e (.reg (.dup 0)) (ri_dup (by rfl))  -- 329d DUP1
  xs 0x329f (.reg (.dup 2)) (ri_dup (by rfl))  -- 329e DUP3
  xs 0x32a0 (.reg .sub) ri_sub  -- 329f SUB
  xs 0x32a1 (.reg (.swap 0)) (ri_swap (by rfl))  -- 32a0 SWAP1
  xs 0x32a2 (.reg .pop) ri_pop  -- 32a1 POP
  xs 0x32a3 (.reg (.swap 0)) (ri_swap (by rfl))  -- 32a2 SWAP1
  xs 0x32a4 (.reg .pop) ri_pop  -- 32a3 POP
  xs 0x32a5 (.reg (.dup 1)) (ri_dup (by rfl))  -- 32a4 DUP2
  xsw 0x32a6 0x300  -- 32a5 MSTORE
  xs 0x32a7 (.reg .pop) ri_pop  -- 32a6 POP
  xjd 0x32a8  -- 32a7 JUMPDEST
  xs 0x32a9 (.reg (.dup 1)) (ri_dup (by rfl))  -- 32a8 DUP2
  xl 0x32aa 0x460  -- 32a9 MLOAD
  xs 0x32ac (.push [0x01] (by decide)) ri_push  -- 32aa PUSH1 0x01
  xs 0x32ad (.reg .add) ri_add  -- 32ac ADD
  xs 0x32ae (.reg (.dup 0)) (ri_dup (by rfl))  -- 32ad DUP1
  xs 0x32af (.reg (.dup 3)) (ri_dup (by rfl))  -- 32ae DUP4
  xsw 0x32b0 0x460  -- 32af MSTORE
  xs 0x32b1 (.reg (.dup 1)) (ri_dup (by rfl))  -- 32b0 DUP2
  xs 0x32b2 (.reg .eq) ri_eq  -- 32b1 EQ
  xs 0x32b3 (.reg .iszero) ri_iszero  -- 32b2 ISZERO
  xs 0x32b6 (.push [0x32, 0x5d] (by decide)) ri_push  -- 32b3 PUSH2 0x325d
  xji 0x32b7 0x325d hw
  · exact absurd hw (by decide)
  clear hw
  -- iteration 2
  xjd 0x325e  -- 325d JUMPDEST
  xs 0x3261 (.push [0x02, 0xe0] (by decide)) ri_push  -- 325e PUSH2 0x02e0
  xs 0x3264 (.push [0x04, 0x60] (by decide)) ri_push  -- 3261 PUSH2 0x0460
  xl 0x3265 0x460  -- 3264 MLOAD
  xs 0x3267 (.push [0x03] (by decide)) ri_push  -- 3265 PUSH1 0x03
  xs 0x3268 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3267 DUP2
  xs 0x3269 (.reg .lt) ri_lt  -- 3268 LT
  xs 0x326c (.push [0x32, 0x71] (by decide)) ri_push  -- 3269 PUSH2 0x3271
  xji 0x326d 0x3271 hw
  · xdead
  clear hw
  xjd 0x3272  -- 3271 JUMPDEST
  xs 0x3274 (.push [0x20] (by decide)) ri_push  -- 3272 PUSH1 0x20
  xs 0x3275 (.reg .mul) ri_mul  -- 3274 MUL
  xs 0x3276 (.reg .add) ri_add  -- 3275 ADD
  xs 0x3277 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3276 DUP1
  xl 0x3278 0x320  -- 3277 MLOAD
  xs 0x327a (.push [0x04] (by decide)) ri_push  -- 3278 PUSH1 0x04
  xs 0x327d (.push [0x04, 0x60] (by decide)) ri_push  -- 327a PUSH2 0x0460
  xl 0x327e 0x460  -- 327d MLOAD
  xs 0x3280 (.push [0x03] (by decide)) ri_push  -- 327e PUSH1 0x03
  xs 0x3281 (.reg (.dup 1)) (ri_dup (by rfl))  -- 3280 DUP2
  xs 0x3282 (.reg .lt) ri_lt  -- 3281 LT
  xs 0x3285 (.push [0x32, 0x8a] (by decide)) ri_push  -- 3282 PUSH2 0x328a
  xji 0x3286 0x328a hw
  · xdead
  clear hw
  xjd 0x328b  -- 328a JUMPDEST
  xs 0x328d (.push [0x20] (by decide)) ri_push  -- 328b PUSH1 0x20
  xs 0x328e (.reg .mul) ri_mul  -- 328d MUL
  xs 0x328f (.reg .add) ri_add  -- 328e ADD
  xs 0x3290 (.reg .calldataload) ri_calldataload  -- 328f CALLDATALOAD
  xs 0x3291 (.reg (.dup 0)) (ri_dup (by rfl))  -- 3290 DUP1
  xs 0x3292 (.reg (.dup 2)) (ri_dup (by rfl))  -- 3291 DUP3
  xs 0x3293 (.reg .lt) ri_lt  -- 3292 LT
  xs 0x3294 (.reg .iszero) ri_iszero  -- 3293 ISZERO
  xs 0x3297 (.push [0x32, 0x9c] (by decide)) ri_push  -- 3294 PUSH2 0x329c
  xji 0x3298 0x329c hw
  · xdead
  have hs2 := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
  clear hw
  xjd 0x329d  -- 329c JUMPDEST
  xs 0x329e (.reg (.dup 0)) (ri_dup (by rfl))  -- 329d DUP1
  xs 0x329f (.reg (.dup 2)) (ri_dup (by rfl))  -- 329e DUP3
  xs 0x32a0 (.reg .sub) ri_sub  -- 329f SUB
  xs 0x32a1 (.reg (.swap 0)) (ri_swap (by rfl))  -- 32a0 SWAP1
  xs 0x32a2 (.reg .pop) ri_pop  -- 32a1 POP
  xs 0x32a3 (.reg (.swap 0)) (ri_swap (by rfl))  -- 32a2 SWAP1
  xs 0x32a4 (.reg .pop) ri_pop  -- 32a3 POP
  xs 0x32a5 (.reg (.dup 1)) (ri_dup (by rfl))  -- 32a4 DUP2
  xsw 0x32a6 0x320  -- 32a5 MSTORE
  xs 0x32a7 (.reg .pop) ri_pop  -- 32a6 POP
  xjd 0x32a8  -- 32a7 JUMPDEST
  xs 0x32a9 (.reg (.dup 1)) (ri_dup (by rfl))  -- 32a8 DUP2
  xl 0x32aa 0x460  -- 32a9 MLOAD
  xs 0x32ac (.push [0x01] (by decide)) ri_push  -- 32aa PUSH1 0x01
  xs 0x32ad (.reg .add) ri_add  -- 32ac ADD
  xs 0x32ae (.reg (.dup 0)) (ri_dup (by rfl))  -- 32ad DUP1
  xs 0x32af (.reg (.dup 3)) (ri_dup (by rfl))  -- 32ae DUP4
  xsw 0x32b0 0x460  -- 32af MSTORE
  xs 0x32b1 (.reg (.dup 1)) (ri_dup (by rfl))  -- 32b0 DUP2
  xs 0x32b2 (.reg .eq) ri_eq  -- 32b1 EQ
  xs 0x32b3 (.reg .iszero) ri_iszero  -- 32b2 ISZERO
  xs 0x32b6 (.push [0x32, 0x5d] (by decide)) ri_push  -- 32b3 PUSH2 0x325d
  xji 0x32b7 0x325d hw
  rotate_left
  · exact absurd hw (by decide)
  clear hw
  xjd 0x32b8  -- 32b7 JUMPDEST
  xs 0x32b9 (.reg .pop) ri_pop  -- 32b8 POP
  xs 0x32ba (.reg .pop) ri_pop  -- 32b9 POP
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
