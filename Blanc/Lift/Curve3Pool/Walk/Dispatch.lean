import Blanc.Lift.Curve3Pool.Walk.Kit
import Blanc.Lift.Curve3Pool.Decode

/-!
# The prologue and dispatcher, on the actual derivation

From the frame's start (pc `0`, empty stack and memory) the runtime checks `CALLDATASIZE ≥ 4`,
runs the Vyper prologue (`mstore(0x1c, calldataload(0))` and the five clamp constants), and tests
the selector arm by arm, jumping over the internal-function blocks between arms
(`PUSH1 0; ISZERO; PUSH2 t; JUMPI`, always taken).

`xa_dispatch_removeLiquidity`: with the `remove_liquidity` selector, the frame reaches
`0x2c68` (the arm's body, past its test) with empty stack, the prologue's memory image, and the
same remaining children (the dispatcher spawns nothing).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The prologue's image over empty memory, with the calldata's first word `w`. -/
abbrev proImg (w : B256) : Bytes := vyImg [] w

/-- **The dispatcher hands `remove_liquidity` its body** (past the arm's own test), with the
prologue's memory image and the frame's remaining children unchanged. -/
theorem xa_dispatch_removeLiquidity {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidity)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ M G', Mem.Reads M (vyImg [] (Sevm.dataWord sevm 0)) ∧ Mem.Wf M ∧
      XAt sevm post 0x2c68 (St b [] M G') L := by
  have hR : Mem.Reads Mem.empty [] := Mem.reads_empty
  have hW : Mem.Wf Mem.empty := Mem.wf_empty
  generalize Mem.empty = M at h hR hW
  xs 0x2 (.push [0x04] (by decide)) ri_push  -- 0000 PUSH1 0x04
  xs 0x3 (.reg .calldatasize) ri_calldatasize  -- 0002 CALLDATASIZE
  xs 0x4 (.reg .lt) ri_lt  -- 0003 LT
  xs 0x5 (.reg .iszero) ri_iszero  -- 0004 ISZERO
  xs 0x8 (.push [0x00, 0x0d] (by decide)) ri_push  -- 0005 PUSH2 0x000d
  xji 0x9 0xd hw  -- taken
  · exact absurd (eqCheck_eq_zero hw) (by
      rw [ltCheck_eq_zero_of_le (by rw [B256.toNat_toB256_of_lt hcd]; exact hlen)]; decide)
  xjd 0xe
  xs 0x10 (.push [0x00] (by decide)) ri_push  -- 000e PUSH1 0x00
  xs 0x11 (.reg .calldataload) ri_calldataload  -- 0010 CALLDATALOAD
  xs 0x13 (.push [0x1c] (by decide)) ri_push  -- 0011 PUSH1 0x1c
  xm 0x14 (.reg .mstore) ri_mstore_img  -- 0013 MSTORE
  xs 0x2a (.push [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 0014 PUSH21 0x010000000000000000000000000000000000000000
  xs 0x2c (.push [0x20] (by decide)) ri_push  -- 002a PUSH1 0x20
  xm 0x2d (.reg .mstore) ri_mstore_img  -- 002c MSTORE
  xs 0x3e (.push [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) ri_push  -- 002d PUSH16 0x7fffffffffffffffffffffffffffffff
  xs 0x40 (.push [0x40] (by decide)) ri_push  -- 003e PUSH1 0x40
  xm 0x41 (.reg .mstore) ri_mstore_img  -- 0040 MSTORE
  xs 0x62 (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 0041 PUSH32 0xffffffffffffffffffffffffffffffff80000000000000000000000000000000
  xs 0x64 (.push [0x60] (by decide)) ri_push  -- 0062 PUSH1 0x60
  xm 0x65 (.reg .mstore) ri_mstore_img  -- 0064 MSTORE
  xs 0x7b (.push [0x01, 0x2a, 0x05, 0xf1, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfd, 0xab, 0xf4, 0x1c, 0x00] (by decide)) ri_push  -- 0065 PUSH21 0x012a05f1fffffffffffffffffffffffffdabf41c00
  xs 0x7d (.push [0x80] (by decide)) ri_push  -- 007b PUSH1 0x80
  xm 0x7e (.reg .mstore) ri_mstore_img  -- 007d MSTORE
  xs 0x9f (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xd5, 0xfa, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 007e PUSH32 0xfffffffffffffffffffffffed5fa0e0000000000000000000000000000000000
  xs 0xa1 (.push [0xa0] (by decide)) ri_push  -- 009f PUSH1 0xa0
  xm 0xa2 (.reg .mstore) ri_mstore_img  -- 00a1 MSTORE
  replace hR : Mem.Reads M (vyImg [] (Sevm.dataWord sevm 0)) := hR
  have hsw : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD (Bytes.toB256 [0]).toNat 32 0) =
      0xecb586a5 := by
    rw [show (Bytes.toB256 [0]).toNat = 0 from rfl, vyImg_selector]; exact hsel
  xs 0xa4 (.push [0x00] (by decide)) ri_push  -- 00a2 PUSH1 0x00
  xs 0xa5 (.reg .iszero) ri_iszero  -- 00a4 ISZERO
  xs 0xa8 (.push [0x02, 0x44] (by decide)) ri_push  -- 00a5 PUSH2 0x0244
  xji 0xa9 0x244 hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x245
  xs 0x24a (.push [0xf4, 0x46, 0xc1, 0xd0] (by decide)) ri_push  -- 0245 PUSH4 0xf446c1d0
  xs 0x24c (.push [0x00] (by decide)) ri_push  -- 024a PUSH1 0x00
  xm 0x24d (.reg .mload) ri_mload_img  -- 024c MLOAD
  xs 0x24e (.reg .eq) ri_eq  -- 024d EQ
  xs 0x24f (.reg .iszero) ri_iszero  -- 024e ISZERO
  xs 0x252 (.push [0x02, 0x79] (by decide)) ri_push  -- 024f PUSH2 0x0279
  xji 0x253 0x279 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x27a
  xs 0x27c (.push [0x00] (by decide)) ri_push  -- 027a PUSH1 0x00
  xs 0x27d (.reg .iszero) ri_iszero  -- 027c ISZERO
  xs 0x280 (.push [0x03, 0x99] (by decide)) ri_push  -- 027d PUSH2 0x0399
  xji 0x281 0x399 hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x39a
  xs 0x39c (.push [0x00] (by decide)) ri_push  -- 039a PUSH1 0x00
  xs 0x39d (.reg .iszero) ri_iszero  -- 039c ISZERO
  xs 0x3a0 (.push [0x04, 0xc1] (by decide)) ri_push  -- 039d PUSH2 0x04c1
  xji 0x3a1 0x4c1 hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x4c2
  xs 0x4c4 (.push [0x00] (by decide)) ri_push  -- 04c2 PUSH1 0x00
  xs 0x4c5 (.reg .iszero) ri_iszero  -- 04c4 ISZERO
  xs 0x4c8 (.push [0x07, 0xaf] (by decide)) ri_push  -- 04c5 PUSH2 0x07af
  xji 0x4c9 0x7af hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x7b0
  xs 0x7b2 (.push [0x00] (by decide)) ri_push  -- 07b0 PUSH1 0x00
  xs 0x7b3 (.reg .iszero) ri_iszero  -- 07b2 ISZERO
  xs 0x7b6 (.push [0x09, 0x0d] (by decide)) ri_push  -- 07b3 PUSH2 0x090d
  xji 0x7b7 0x90d hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x90e
  xs 0x913 (.push [0xbb, 0x7b, 0x8b, 0x80] (by decide)) ri_push  -- 090e PUSH4 0xbb7b8b80
  xs 0x915 (.push [0x00] (by decide)) ri_push  -- 0913 PUSH1 0x00
  xm 0x916 (.reg .mload) ri_mload_img  -- 0915 MLOAD
  xs 0x917 (.reg .eq) ri_eq  -- 0916 EQ
  xs 0x918 (.reg .iszero) ri_iszero  -- 0917 ISZERO
  xs 0x91b (.push [0x0a, 0xf8] (by decide)) ri_push  -- 0918 PUSH2 0x0af8
  xji 0x91c 0xaf8 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0xaf9
  xs 0xafe (.push [0x38, 0x83, 0xe1, 0x19] (by decide)) ri_push  -- 0af9 PUSH4 0x3883e119
  xs 0xb00 (.push [0x00] (by decide)) ri_push  -- 0afe PUSH1 0x00
  xm 0xb01 (.reg .mload) ri_mload_img  -- 0b00 MLOAD
  xs 0xb02 (.reg .eq) ri_eq  -- 0b01 EQ
  xs 0xb03 (.reg .iszero) ri_iszero  -- 0b02 ISZERO
  xs 0xb06 (.push [0x0e, 0x46] (by decide)) ri_push  -- 0b03 PUSH2 0x0e46
  xji 0xb07 0xe46 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0xe47
  xs 0xe4c (.push [0x45, 0x15, 0xce, 0xf3] (by decide)) ri_push  -- 0e47 PUSH4 0x4515cef3
  xs 0xe4e (.push [0x00] (by decide)) ri_push  -- 0e4c PUSH1 0x00
  xm 0xe4f (.reg .mload) ri_mload_img  -- 0e4e MLOAD
  xs 0xe50 (.reg .eq) ri_eq  -- 0e4f EQ
  xs 0xe51 (.reg .iszero) ri_iszero  -- 0e50 ISZERO
  xs 0xe54 (.push [0x18, 0x9c] (by decide)) ri_push  -- 0e51 PUSH2 0x189c
  xji 0xe55 0x189c hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x189d
  xs 0x189f (.push [0x00] (by decide)) ri_push  -- 189d PUSH1 0x00
  xs 0x18a0 (.reg .iszero) ri_iszero  -- 189f ISZERO
  xs 0x18a3 (.push [0x1d, 0x13] (by decide)) ri_push  -- 18a0 PUSH2 0x1d13
  xji 0x18a4 0x1d13 hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x1d14
  xs 0x1d19 (.push [0x5e, 0x0d, 0x44, 0x3f] (by decide)) ri_push  -- 1d14 PUSH4 0x5e0d443f
  xs 0x1d1b (.push [0x00] (by decide)) ri_push  -- 1d19 PUSH1 0x00
  xm 0x1d1c (.reg .mload) ri_mload_img  -- 1d1b MLOAD
  xs 0x1d1d (.reg .eq) ri_eq  -- 1d1c EQ
  xs 0x1d1e (.reg .iszero) ri_iszero  -- 1d1d ISZERO
  xs 0x1d21 (.push [0x20, 0x45] (by decide)) ri_push  -- 1d1e PUSH2 0x2045
  xji 0x1d22 0x2045 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x2046
  xs 0x204b (.push [0x07, 0x21, 0x1e, 0xf7] (by decide)) ri_push  -- 2046 PUSH4 0x07211ef7
  xs 0x204d (.push [0x00] (by decide)) ri_push  -- 204b PUSH1 0x00
  xm 0x204e (.reg .mload) ri_mload_img  -- 204d MLOAD
  xs 0x204f (.reg .eq) ri_eq  -- 204e EQ
  xs 0x2050 (.reg .iszero) ri_iszero  -- 204f ISZERO
  xs 0x2053 (.push [0x23, 0x0a] (by decide)) ri_push  -- 2050 PUSH2 0x230a
  xji 0x2054 0x230a hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x230b
  xs 0x2310 (.push [0x3d, 0xf0, 0x21, 0x24] (by decide)) ri_push  -- 230b PUSH4 0x3df02124
  xs 0x2312 (.push [0x00] (by decide)) ri_push  -- 2310 PUSH1 0x00
  xm 0x2313 (.reg .mload) ri_mload_img  -- 2312 MLOAD
  xs 0x2314 (.reg .eq) ri_eq  -- 2313 EQ
  xs 0x2315 (.reg .iszero) ri_iszero  -- 2314 ISZERO
  xs 0x2318 (.push [0x2c, 0x59] (by decide)) ri_push  -- 2315 PUSH2 0x2c59
  xji 0x2319 0x2c59 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x2c5a
  xs 0x2c5f (.push [0xec, 0xb5, 0x86, 0xa5] (by decide)) ri_push  -- 2c5a PUSH4 0xecb586a5
  xs 0x2c61 (.push [0x00] (by decide)) ri_push  -- 2c5f PUSH1 0x00
  xm 0x2c62 (.reg .mload) ri_mload_img  -- 2c61 MLOAD
  xs 0x2c63 (.reg .eq) ri_eq  -- 2c62 EQ
  xs 0x2c64 (.reg .iszero) ri_iszero  -- 2c63 ISZERO
  xs 0x2c67 (.push [0x30, 0x40] (by decide)) ri_push  -- 2c64 PUSH2 0x3040
  xji 0x2c68 0x3040 hw  -- fall
  · exact ⟨M, _, hR, hW, h⟩
  · exact absurd (by rw [hsw]; decide) (isNe_jump hw)

end Blanc.Lift.Curve3Pool
