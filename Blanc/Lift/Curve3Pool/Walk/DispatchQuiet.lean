import Blanc.Lift.Curve3Pool.Walk.Dispatch
import Blanc.Lift.Curve3Pool.Decode

/-!
# Dispatcher walks to the quiet admin/getter arms

`dq_prologue` walks the shared prefix (frame entry through the Vyper prologue
to the first selector test at `0x245`); `dq_skip_*` steps over one
non-matching selector test (taking the target arm's
`Sevm.selector sevm ≠ lit` hypothesis); `dq_pass_*` steps over the
always-taken internal skips; `dq_to_3040`/`dq_to_499b` package the common
prefixes; `dq_arm_*` fall through one arm's test into its body with the exact
`quietSt` state (`St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G'`).
Pc layout follows `Dispatch.lean` and the `t_*_c0` chain in `Cert.lean`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The prologue's memory word at offset `0` is the frame's selector. -/
theorem dq_memword {sevm : Sevm} :
    Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD (Bytes.toB256 [0]).toNat 32 0) =
      Sevm.selector sevm := by
  rw [show (Bytes.toB256 [0]).toNat = 0 from rfl, vyImg_selector]
  rfl

/-- The shared prefix: frame entry through the prologue to the first test. -/
theorem dq_prologue {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x245 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
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
  xs 0x14 (.reg .mstore) ri_mstore  -- 0013 MSTORE
  xs 0x2a (.push [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 0014 PUSH21 0x010000000000000000000000000000000000000000
  xs 0x2c (.push [0x20] (by decide)) ri_push  -- 002a PUSH1 0x20
  xs 0x2d (.reg .mstore) ri_mstore  -- 002c MSTORE
  xs 0x3e (.push [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) ri_push  -- 002d PUSH16 0x7fffffffffffffffffffffffffffffff
  xs 0x40 (.push [0x40] (by decide)) ri_push  -- 003e PUSH1 0x40
  xs 0x41 (.reg .mstore) ri_mstore  -- 0040 MSTORE
  xs 0x62 (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 0041 PUSH32 0xffffffffffffffffffffffffffffffff80000000000000000000000000000000
  xs 0x64 (.push [0x60] (by decide)) ri_push  -- 0062 PUSH1 0x60
  xs 0x65 (.reg .mstore) ri_mstore  -- 0064 MSTORE
  xs 0x7b (.push [0x01, 0x2a, 0x05, 0xf1, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfd, 0xab, 0xf4, 0x1c, 0x00] (by decide)) ri_push  -- 0065 PUSH21 0x012a05f1fffffffffffffffffffffffffdabf41c00
  xs 0x7d (.push [0x80] (by decide)) ri_push  -- 007b PUSH1 0x80
  xs 0x7e (.reg .mstore) ri_mstore  -- 007d MSTORE
  xs 0x9f (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xd5, 0xfa, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push  -- 007e PUSH32 0xfffffffffffffffffffffffed5fa0e0000000000000000000000000000000000
  xs 0xa1 (.push [0xa0] (by decide)) ri_push  -- 009f PUSH1 0xa0
  xs 0xa2 (.reg .mstore) ri_mstore  -- 00a1 MSTORE
  replace h : XAt sevm post 0xa2 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) _) L := h
  xs 0xa4 (.push [0x00] (by decide)) ri_push  -- 00a2 PUSH1 0x00
  xs 0xa5 (.reg .iszero) ri_iszero  -- 00a4 ISZERO
  xs 0xa8 (.push [0x02, 0x44] (by decide)) ri_push  -- 00a5 PUSH2 0x0244
  xji 0xa9 0x244 hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x245
  exact ⟨_, h⟩

/-- Skip the `0xf446c1d0` test: `0x245` to `0x27a`. -/
theorem dq_skip_f446c1d0 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x245 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0xf446c1d0) :
    ∃ G', XAt sevm post 0x27a (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x24a (.push [0xf4, 0x46, 0xc1, 0xd0] (by decide)) ri_push
  xs 0x24c (.push [0x00] (by decide)) ri_push
  xs 0x24d (.reg .mload) ri_mload_vy0
  xs 0x24e (.reg .eq) ri_eq
  xs 0x24f (.reg .iszero) ri_iszero
  xs 0x252 (.push [0x02, 0x79] (by decide)) ri_push
  xji 0x253 0x279 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x27a
  exact ⟨_, h⟩

/-- The always-taken skip: `0x27a` to `0x39a`. -/
theorem dq_pass_0279 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x27a (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x39a (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x27c (.push [0x00] (by decide)) ri_push
  xs 0x27d (.reg .iszero) ri_iszero
  xs 0x280 (.push [0x03, 0x99] (by decide)) ri_push
  xji 0x281 0x399 hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x39a
  exact ⟨_, h⟩

/-- The always-taken skip: `0x39a` to `0x4c2`. -/
theorem dq_pass_0399 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x39a (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4c2 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x39c (.push [0x00] (by decide)) ri_push
  xs 0x39d (.reg .iszero) ri_iszero
  xs 0x3a0 (.push [0x04, 0xc1] (by decide)) ri_push
  xji 0x3a1 0x4c1 hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x4c2
  exact ⟨_, h⟩

/-- The always-taken skip: `0x4c2` to `0x7b0`. -/
theorem dq_pass_04c1 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x4c2 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x7b0 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4c4 (.push [0x00] (by decide)) ri_push  -- 04c2 PUSH1 0x00
  xs 0x4c5 (.reg .iszero) ri_iszero
  xs 0x4c8 (.push [0x07, 0xaf] (by decide)) ri_push
  xji 0x4c9 0x7af hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x7b0
  exact ⟨_, h⟩

/-- The always-taken skip: `0x7b0` to `0x90e`. -/
theorem dq_pass_07af {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x7b0 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x90e (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x7b2 (.push [0x00] (by decide)) ri_push
  xs 0x7b3 (.reg .iszero) ri_iszero
  xs 0x7b6 (.push [0x09, 0x0d] (by decide)) ri_push
  xji 0x7b7 0x90d hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x90e
  exact ⟨_, h⟩

/-- Skip the `0xbb7b8b80` test: `0x90e` to `0xaf9`. -/
theorem dq_skip_bb7b8b80 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x90e (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0xbb7b8b80) :
    ∃ G', XAt sevm post 0xaf9 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x913 (.push [0xbb, 0x7b, 0x8b, 0x80] (by decide)) ri_push
  xs 0x915 (.push [0x00] (by decide)) ri_push
  xs 0x916 (.reg .mload) ri_mload_vy0
  xs 0x917 (.reg .eq) ri_eq
  xs 0x918 (.reg .iszero) ri_iszero
  xs 0x91b (.push [0x0a, 0xf8] (by decide)) ri_push
  xji 0x91c 0xaf8 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0xaf9
  exact ⟨_, h⟩

/-- Skip the `0x3883e119` test: `0xaf9` to `0xe47`. -/
theorem dq_skip_3883e119 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0xaf9 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x3883e119) :
    ∃ G', XAt sevm post 0xe47 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0xafe (.push [0x38, 0x83, 0xe1, 0x19] (by decide)) ri_push
  xs 0xb00 (.push [0x00] (by decide)) ri_push
  xs 0xb01 (.reg .mload) ri_mload_vy0
  xs 0xb02 (.reg .eq) ri_eq
  xs 0xb03 (.reg .iszero) ri_iszero
  xs 0xb06 (.push [0x0e, 0x46] (by decide)) ri_push
  xji 0xb07 0xe46 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0xe47
  exact ⟨_, h⟩

/-- Skip the `0x4515cef3` test: `0xe47` to `0x189d`. -/
theorem dq_skip_4515cef3 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0xe47 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x4515cef3) :
    ∃ G', XAt sevm post 0x189d (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0xe4c (.push [0x45, 0x15, 0xce, 0xf3] (by decide)) ri_push
  xs 0xe4e (.push [0x00] (by decide)) ri_push
  xs 0xe4f (.reg .mload) ri_mload_vy0
  xs 0xe50 (.reg .eq) ri_eq
  xs 0xe51 (.reg .iszero) ri_iszero
  xs 0xe54 (.push [0x18, 0x9c] (by decide)) ri_push
  xji 0xe55 0x189c hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x189d
  exact ⟨_, h⟩

/-- The always-taken skip: `0x189d` to `0x1d14`. -/
theorem dq_pass_189c {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x189d (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x1d14 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x189f (.push [0x00] (by decide)) ri_push
  xs 0x18a0 (.reg .iszero) ri_iszero
  xs 0x18a3 (.push [0x1d, 0x13] (by decide)) ri_push
  xji 0x18a4 0x1d13 hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x1d14
  exact ⟨_, h⟩

/-- Skip the `0x5e0d443f` test: `0x1d14` to `0x2046`. -/
theorem dq_skip_5e0d443f {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x1d14 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x5e0d443f) :
    ∃ G', XAt sevm post 0x2046 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x1d19 (.push [0x5e, 0x0d, 0x44, 0x3f] (by decide)) ri_push
  xs 0x1d1b (.push [0x00] (by decide)) ri_push
  xs 0x1d1c (.reg .mload) ri_mload_vy0
  xs 0x1d1d (.reg .eq) ri_eq
  xs 0x1d1e (.reg .iszero) ri_iszero
  xs 0x1d21 (.push [0x20, 0x45] (by decide)) ri_push
  xji 0x1d22 0x2045 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x2046
  exact ⟨_, h⟩

/-- Skip the `0x07211ef7` test: `0x2046` to `0x230b`. -/
theorem dq_skip_07211ef7 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x2046 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x07211ef7) :
    ∃ G', XAt sevm post 0x230b (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x204b (.push [0x07, 0x21, 0x1e, 0xf7] (by decide)) ri_push
  xs 0x204d (.push [0x00] (by decide)) ri_push
  xs 0x204e (.reg .mload) ri_mload_vy0
  xs 0x204f (.reg .eq) ri_eq
  xs 0x2050 (.reg .iszero) ri_iszero
  xs 0x2053 (.push [0x23, 0x0a] (by decide)) ri_push
  xji 0x2054 0x230a hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x230b
  exact ⟨_, h⟩

/-- Skip the `0x3df02124` test: `0x230b` to `0x2c5a`. -/
theorem dq_skip_3df02124 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x230b (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x3df02124) :
    ∃ G', XAt sevm post 0x2c5a (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x2310 (.push [0x3d, 0xf0, 0x21, 0x24] (by decide)) ri_push
  xs 0x2312 (.push [0x00] (by decide)) ri_push
  xs 0x2313 (.reg .mload) ri_mload_vy0
  xs 0x2314 (.reg .eq) ri_eq
  xs 0x2315 (.reg .iszero) ri_iszero
  xs 0x2318 (.push [0x2c, 0x59] (by decide)) ri_push
  xji 0x2319 0x2c59 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x2c5a
  exact ⟨_, h⟩

/-- Skip the `0xecb586a5` test: `0x2c5a` to `0x3041`. -/
theorem dq_skip_ecb586a5 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x2c5a (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0xecb586a5) :
    ∃ G', XAt sevm post 0x3041 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x2c5f (.push [0xec, 0xb5, 0x86, 0xa5] (by decide)) ri_push
  xs 0x2c61 (.push [0x00] (by decide)) ri_push
  xs 0x2c62 (.reg .mload) ri_mload_vy0
  xs 0x2c63 (.reg .eq) ri_eq
  xs 0x2c64 (.reg .iszero) ri_iszero
  xs 0x2c67 (.push [0x30, 0x40] (by decide)) ri_push
  xji 0x2c68 0x3040 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x3041
  exact ⟨_, h⟩

/-- The common prefix through `remove_liquidity`'s test: entry to `0x3041`. -/
theorem dq_to_3040 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L)
    (hne1 : Sevm.selector sevm ≠ 0xf446c1d0) (hne2 : Sevm.selector sevm ≠ 0xbb7b8b80)
    (hne3 : Sevm.selector sevm ≠ 0x3883e119) (hne4 : Sevm.selector sevm ≠ 0x4515cef3)
    (hne5 : Sevm.selector sevm ≠ 0x5e0d443f) (hne6 : Sevm.selector sevm ≠ 0x07211ef7)
    (hne7 : Sevm.selector sevm ≠ 0x3df02124) (hne8 : Sevm.selector sevm ≠ 0xecb586a5) :
    ∃ G', XAt sevm post 0x3041 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  obtain ⟨G1, h⟩ := dq_prologue hcode hlen hcd h
  obtain ⟨G2, h⟩ := dq_skip_f446c1d0 hcode h hne1
  obtain ⟨G3, h⟩ := dq_pass_0279 hcode h
  obtain ⟨G4, h⟩ := dq_pass_0399 hcode h
  obtain ⟨G5, h⟩ := dq_pass_04c1 hcode h
  obtain ⟨G6, h⟩ := dq_pass_07af hcode h
  obtain ⟨G7, h⟩ := dq_skip_bb7b8b80 hcode h hne2
  obtain ⟨G8, h⟩ := dq_skip_3883e119 hcode h hne3
  obtain ⟨G9, h⟩ := dq_skip_4515cef3 hcode h hne4
  obtain ⟨G10, h⟩ := dq_pass_189c hcode h
  obtain ⟨G11, h⟩ := dq_skip_5e0d443f hcode h hne5
  obtain ⟨G12, h⟩ := dq_skip_07211ef7 hcode h hne6
  obtain ⟨G13, h⟩ := dq_skip_3df02124 hcode h hne7
  obtain ⟨G14, h⟩ := dq_skip_ecb586a5 hcode h hne8
  exact ⟨_, h⟩

/-- Skip the `0x9fdaea0c` test: `0x3041` to `0x3992`. -/
theorem dq_skip_9fdaea0c {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x3041 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x9fdaea0c) :
    ∃ G', XAt sevm post 0x3992 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x3046 (.push [0x9f, 0xda, 0xea, 0x0c] (by decide)) ri_push
  xs 0x3048 (.push [0x00] (by decide)) ri_push
  xs 0x3049 (.reg .mload) ri_mload_vy0
  xs 0x304a (.reg .eq) ri_eq
  xs 0x304b (.reg .iszero) ri_iszero
  xs 0x304e (.push [0x39, 0x91] (by decide)) ri_push
  xji 0x304f 0x3991 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x3992
  exact ⟨_, h⟩

/-- The always-taken skip: `0x3992` to `0x3cc3`. -/
theorem dq_pass_3991 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x3992 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x3cc3 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x3994 (.push [0x00] (by decide)) ri_push
  xs 0x3995 (.reg .iszero) ri_iszero
  xs 0x3998 (.push [0x3c, 0xc2] (by decide)) ri_push
  xji 0x3999 0x3cc2 hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x3cc3
  exact ⟨_, h⟩

/-- The always-taken skip: `0x3cc3` to `0x438a`. -/
theorem dq_pass_3cc2 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x3cc3 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x438a (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x3cc5 (.push [0x00] (by decide)) ri_push
  xs 0x3cc6 (.reg .iszero) ri_iszero
  xs 0x3cc9 (.push [0x43, 0x89] (by decide)) ri_push
  xji 0x3cca 0x4389 hw  -- taken
  · exact absurd hw (by decide)
  xjd 0x438a
  exact ⟨_, h⟩

/-- Skip the `0xcc2b27d7` test: `0x438a` to `0x43fe`. -/
theorem dq_skip_cc2b27d7 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x438a (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0xcc2b27d7) :
    ∃ G', XAt sevm post 0x43fe (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x438f (.push [0xcc, 0x2b, 0x27, 0xd7] (by decide)) ri_push
  xs 0x4391 (.push [0x00] (by decide)) ri_push
  xs 0x4392 (.reg .mload) ri_mload_vy0
  xs 0x4393 (.reg .eq) ri_eq
  xs 0x4394 (.reg .iszero) ri_iszero
  xs 0x4397 (.push [0x43, 0xfd] (by decide)) ri_push
  xji 0x4398 0x43fd hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x43fe
  exact ⟨_, h⟩

/-- Skip the `0x1a4d01d2` test: `0x43fe` to `0x4769`. -/
theorem dq_skip_1a4d01d2 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x43fe (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x1a4d01d2) :
    ∃ G', XAt sevm post 0x4769 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4403 (.push [0x1a, 0x4d, 0x01, 0xd2] (by decide)) ri_push
  xs 0x4405 (.push [0x00] (by decide)) ri_push
  xs 0x4406 (.reg .mload) ri_mload_vy0
  xs 0x4407 (.reg .eq) ri_eq
  xs 0x4408 (.reg .iszero) ri_iszero
  xs 0x440b (.push [0x47, 0x68] (by decide)) ri_push
  xji 0x440c 0x4768 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x4769
  exact ⟨_, h⟩

/-- Skip the `0x3c157e64` test: `0x4769` to `0x490c`. -/
theorem dq_skip_3c157e64 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x4769 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x3c157e64) :
    ∃ G', XAt sevm post 0x490c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x476e (.push [0x3c, 0x15, 0x7e, 0x64] (by decide)) ri_push
  xs 0x4770 (.push [0x00] (by decide)) ri_push
  xs 0x4771 (.reg .mload) ri_mload_vy0
  xs 0x4772 (.reg .eq) ri_eq
  xs 0x4773 (.reg .iszero) ri_iszero
  xs 0x4776 (.push [0x49, 0x0b] (by decide)) ri_push
  xji 0x4777 0x490b hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x490c
  exact ⟨_, h⟩

/-- Skip the `0x551a6588` test: `0x490c` to `0x499c`. -/
theorem dq_skip_551a6588 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x490c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x551a6588) :
    ∃ G', XAt sevm post 0x499c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4911 (.push [0x55, 0x1a, 0x65, 0x88] (by decide)) ri_push
  xs 0x4913 (.push [0x00] (by decide)) ri_push
  xs 0x4914 (.reg .mload) ri_mload_vy0
  xs 0x4915 (.reg .eq) ri_eq
  xs 0x4916 (.reg .iszero) ri_iszero
  xs 0x4919 (.push [0x49, 0x9b] (by decide)) ri_push
  xji 0x491a 0x499b hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x499c
  exact ⟨_, h⟩

/-- The middle prefix: `0x3041` to `0x499c`. -/
theorem dq_to_499b {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x3041 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne1 : Sevm.selector sevm ≠ 0x9fdaea0c) (hne2 : Sevm.selector sevm ≠ 0xcc2b27d7)
    (hne3 : Sevm.selector sevm ≠ 0x1a4d01d2) (hne4 : Sevm.selector sevm ≠ 0x3c157e64)
    (hne5 : Sevm.selector sevm ≠ 0x551a6588) :
    ∃ G', XAt sevm post 0x499c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  obtain ⟨G1, h⟩ := dq_skip_9fdaea0c hcode h hne1
  obtain ⟨G2, h⟩ := dq_pass_3991 hcode h
  obtain ⟨G3, h⟩ := dq_pass_3cc2 hcode h
  obtain ⟨G4, h⟩ := dq_skip_cc2b27d7 hcode h hne2
  obtain ⟨G5, h⟩ := dq_skip_1a4d01d2 hcode h hne3
  obtain ⟨G6, h⟩ := dq_skip_3c157e64 hcode h hne4
  obtain ⟨G7, h⟩ := dq_skip_551a6588 hcode h hne5
  exact ⟨_, h⟩

/-- Skip the `commit_new_fee` test: `0x499c` to `0x4a65`. -/
theorem dq_skip_5b5a1467 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x499c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x5b5a1467) :
    ∃ G', XAt sevm post 0x4a65 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x49a1 (.push [0x5b, 0x5a, 0x14, 0x67] (by decide)) ri_push
  xs 0x49a3 (.push [0x00] (by decide)) ri_push
  xs 0x49a4 (.reg .mload) ri_mload_vy0
  xs 0x49a5 (.reg .eq) ri_eq
  xs 0x49a6 (.reg .iszero) ri_iszero
  xs 0x49a9 (.push [0x4a, 0x64] (by decide)) ri_push
  xji 0x49aa 0x4a64 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x4a65
  exact ⟨_, h⟩

/-- Skip the `apply_new_fee` test: `0x4a65` to `0x4b04`. -/
theorem dq_skip_4f12fe97 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x4a65 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x4f12fe97) :
    ∃ G', XAt sevm post 0x4b04 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4a6a (.push [0x4f, 0x12, 0xfe, 0x97] (by decide)) ri_push
  xs 0x4a6c (.push [0x00] (by decide)) ri_push
  xs 0x4a6d (.reg .mload) ri_mload_vy0
  xs 0x4a6e (.reg .eq) ri_eq
  xs 0x4a6f (.reg .iszero) ri_iszero
  xs 0x4a72 (.push [0x4b, 0x03] (by decide)) ri_push
  xji 0x4a73 0x4b03 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x4b04
  exact ⟨_, h⟩

/-- Skip the `revert_new_parameters` test: `0x4b04` to `0x4b32`. -/
theorem dq_skip_226840fb {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x4b04 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x226840fb) :
    ∃ G', XAt sevm post 0x4b32 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4b09 (.push [0x22, 0x68, 0x40, 0xfb] (by decide)) ri_push
  xs 0x4b0b (.push [0x00] (by decide)) ri_push
  xs 0x4b0c (.reg .mload) ri_mload_vy0
  xs 0x4b0d (.reg .eq) ri_eq
  xs 0x4b0e (.reg .iszero) ri_iszero
  xs 0x4b11 (.push [0x4b, 0x31] (by decide)) ri_push
  xji 0x4b12 0x4b31 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x4b32
  exact ⟨_, h⟩

/-- Skip the `commit_transfer_ownership` test: `0x4b32` to `0x4bd3`. -/
theorem dq_skip_6b441a40 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x4b32 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x6b441a40) :
    ∃ G', XAt sevm post 0x4bd3 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4b37 (.push [0x6b, 0x44, 0x1a, 0x40] (by decide)) ri_push
  xs 0x4b39 (.push [0x00] (by decide)) ri_push
  xs 0x4b3a (.reg .mload) ri_mload_vy0
  xs 0x4b3b (.reg .eq) ri_eq
  xs 0x4b3c (.reg .iszero) ri_iszero
  xs 0x4b3f (.push [0x4b, 0xd2] (by decide)) ri_push
  xji 0x4b40 0x4bd2 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x4bd3
  exact ⟨_, h⟩

/-- Skip the `apply_transfer_ownership` test: `0x4bd3` to `0x4c57`. -/
theorem dq_skip_6a1c05ae {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x4bd3 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x6a1c05ae) :
    ∃ G', XAt sevm post 0x4c57 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4bd8 (.push [0x6a, 0x1c, 0x05, 0xae] (by decide)) ri_push
  xs 0x4bda (.push [0x00] (by decide)) ri_push
  xs 0x4bdb (.reg .mload) ri_mload_vy0
  xs 0x4bdc (.reg .eq) ri_eq
  xs 0x4bdd (.reg .iszero) ri_iszero
  xs 0x4be0 (.push [0x4c, 0x56] (by decide)) ri_push
  xji 0x4be1 0x4c56 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x4c57
  exact ⟨_, h⟩

/-- Skip the `revert_transfer_ownership` test: `0x4c57` to `0x4c85`. -/
theorem dq_skip_86fbf193 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x4c57 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x86fbf193) :
    ∃ G', XAt sevm post 0x4c85 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4c5c (.push [0x86, 0xfb, 0xf1, 0x93] (by decide)) ri_push
  xs 0x4c5e (.push [0x00] (by decide)) ri_push
  xs 0x4c5f (.reg .mload) ri_mload_vy0
  xs 0x4c60 (.reg .eq) ri_eq
  xs 0x4c61 (.reg .iszero) ri_iszero
  xs 0x4c64 (.push [0x4c, 0x84] (by decide)) ri_push
  xji 0x4c65 0x4c84 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x4c85
  exact ⟨_, h⟩

/-- Fall into `commit_new_fee`'s body at `0x49aa`. -/
theorem dq_arm_commitNewFee {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selCommitNewFee)
    (h : XAt sevm post 0x499c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x49aa (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x49a1 (.push [0x5b, 0x5a, 0x14, 0x67] (by decide)) ri_push
  xs 0x49a3 (.push [0x00] (by decide)) ri_push
  xs 0x49a4 (.reg .mload) ri_mload_vy0
  xs 0x49a5 (.reg .eq) ri_eq
  xs 0x49a6 (.reg .iszero) ri_iszero
  xs 0x49a9 (.push [0x4a, 0x64] (by decide)) ri_push
  xji 0x49aa 0x4a64 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Fall into `apply_new_fee`'s body at `0x4a73`. -/
theorem dq_arm_applyNewFee {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selApplyNewFee)
    (h : XAt sevm post 0x4a65 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4a73 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4a6a (.push [0x4f, 0x12, 0xfe, 0x97] (by decide)) ri_push
  xs 0x4a6c (.push [0x00] (by decide)) ri_push
  xs 0x4a6d (.reg .mload) ri_mload_vy0
  xs 0x4a6e (.reg .eq) ri_eq
  xs 0x4a6f (.reg .iszero) ri_iszero
  xs 0x4a72 (.push [0x4b, 0x03] (by decide)) ri_push
  xji 0x4a73 0x4b03 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Fall into `revert_new_parameters`'s body at `0x4b12`. -/
theorem dq_arm_revertNewParameters {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selRevertNewParameters)
    (h : XAt sevm post 0x4b04 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4b12 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4b09 (.push [0x22, 0x68, 0x40, 0xfb] (by decide)) ri_push
  xs 0x4b0b (.push [0x00] (by decide)) ri_push
  xs 0x4b0c (.reg .mload) ri_mload_vy0
  xs 0x4b0d (.reg .eq) ri_eq
  xs 0x4b0e (.reg .iszero) ri_iszero
  xs 0x4b11 (.push [0x4b, 0x31] (by decide)) ri_push
  xji 0x4b12 0x4b31 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Fall into `commit_transfer_ownership`'s body at `0x4b40`. -/
theorem dq_arm_commitTransferOwnership {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selCommitTransferOwnership)
    (h : XAt sevm post 0x4b32 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4b40 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4b37 (.push [0x6b, 0x44, 0x1a, 0x40] (by decide)) ri_push
  xs 0x4b39 (.push [0x00] (by decide)) ri_push
  xs 0x4b3a (.reg .mload) ri_mload_vy0
  xs 0x4b3b (.reg .eq) ri_eq
  xs 0x4b3c (.reg .iszero) ri_iszero
  xs 0x4b3f (.push [0x4b, 0xd2] (by decide)) ri_push
  xji 0x4b40 0x4bd2 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Fall into `apply_transfer_ownership`'s body at `0x4be1`. -/
theorem dq_arm_applyTransferOwnership {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selApplyTransferOwnership)
    (h : XAt sevm post 0x4bd3 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4be1 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4bd8 (.push [0x6a, 0x1c, 0x05, 0xae] (by decide)) ri_push
  xs 0x4bda (.push [0x00] (by decide)) ri_push
  xs 0x4bdb (.reg .mload) ri_mload_vy0
  xs 0x4bdc (.reg .eq) ri_eq
  xs 0x4bdd (.reg .iszero) ri_iszero
  xs 0x4be0 (.push [0x4c, 0x56] (by decide)) ri_push
  xji 0x4be1 0x4c56 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Fall into `revert_transfer_ownership`'s body at `0x4c65`. -/
theorem dq_arm_revertTransferOwnership {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selRevertTransferOwnership)
    (h : XAt sevm post 0x4c57 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4c65 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4c5c (.push [0x86, 0xfb, 0xf1, 0x93] (by decide)) ri_push
  xs 0x4c5e (.push [0x00] (by decide)) ri_push
  xs 0x4c5f (.reg .mload) ri_mload_vy0
  xs 0x4c60 (.reg .eq) ri_eq
  xs 0x4c61 (.reg .iszero) ri_iszero
  xs 0x4c64 (.push [0x4c, 0x84] (by decide)) ri_push
  xji 0x4c65 0x4c84 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Skip the `0xe2e7d264` test: `0x4c85` to `0x4d2c`. -/
theorem dq_skip_e2e7d264 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x4c85 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0xe2e7d264) :
    ∃ G', XAt sevm post 0x4d2c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4c8a (.push [0xe2, 0xe7, 0xd2, 0x64] (by decide)) ri_push
  xs 0x4c8c (.push [0x00] (by decide)) ri_push
  xs 0x4c8d (.reg .mload) ri_mload_vy0
  xs 0x4c8e (.reg .eq) ri_eq
  xs 0x4c8f (.reg .iszero) ri_iszero
  xs 0x4c92 (.push [0x4d, 0x2b] (by decide)) ri_push
  xji 0x4c93 0x4d2b hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x4d2c
  exact ⟨_, h⟩

/-- Skip the `0x30c54085` test: `0x4d2c` to `0x4f52`. -/
theorem dq_skip_30c54085 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x4d2c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x30c54085) :
    ∃ G', XAt sevm post 0x4f52 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4d31 (.push [0x30, 0xc5, 0x40, 0x85] (by decide)) ri_push
  xs 0x4d33 (.push [0x00] (by decide)) ri_push
  xs 0x4d34 (.reg .mload) ri_mload_vy0
  xs 0x4d35 (.reg .eq) ri_eq
  xs 0x4d36 (.reg .iszero) ri_iszero
  xs 0x4d39 (.push [0x4f, 0x51] (by decide)) ri_push
  xji 0x4d3a 0x4f51 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x4f52
  exact ⟨_, h⟩

/-- Skip the `0x524c3901` test: `0x4f52` to `0x500b`. -/
theorem dq_skip_524c3901 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x4f52 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x524c3901) :
    ∃ G', XAt sevm post 0x500b (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x4f57 (.push [0x52, 0x4c, 0x39, 0x01] (by decide)) ri_push
  xs 0x4f59 (.push [0x00] (by decide)) ri_push
  xs 0x4f5a (.reg .mload) ri_mload_vy0
  xs 0x4f5b (.reg .eq) ri_eq
  xs 0x4f5c (.reg .iszero) ri_iszero
  xs 0x4f5f (.push [0x50, 0x0a] (by decide)) ri_push
  xji 0x4f60 0x500a hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x500b
  exact ⟨_, h⟩

/-- Fall into `kill_me`'s body at `0x5019`. -/
theorem dq_arm_killMe {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selKillMe)
    (h : XAt sevm post 0x500b (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x5019 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x5010 (.push [0xe3, 0x69, 0x88, 0x53] (by decide)) ri_push
  xs 0x5012 (.push [0x00] (by decide)) ri_push
  xs 0x5013 (.reg .mload) ri_mload_vy0
  xs 0x5014 (.reg .eq) ri_eq
  xs 0x5015 (.reg .iszero) ri_iszero
  xs 0x5018 (.push [0x50, 0x46] (by decide)) ri_push
  xji 0x5019 0x5046 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Fall into `unkill_me`'s body at `0x5055`. -/
theorem dq_arm_unkillMe {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selUnkillMe)
    (h : XAt sevm post 0x5047 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x5055 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x504c (.push [0x30, 0x46, 0xf9, 0x72] (by decide)) ri_push
  xs 0x504e (.push [0x00] (by decide)) ri_push
  xs 0x504f (.reg .mload) ri_mload_vy0
  xs 0x5050 (.reg .eq) ri_eq
  xs 0x5051 (.reg .iszero) ri_iszero
  xs 0x5054 (.push [0x50, 0x74] (by decide)) ri_push
  xji 0x5055 0x5074 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Skip the `kill_me` test: `0x500b` to `0x5047`. -/
theorem dq_skip_e3698853 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x500b (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0xe3698853) :
    ∃ G', XAt sevm post 0x5047 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x5010 (.push [0xe3, 0x69, 0x88, 0x53] (by decide)) ri_push
  xs 0x5012 (.push [0x00] (by decide)) ri_push
  xs 0x5013 (.reg .mload) ri_mload_vy0
  xs 0x5014 (.reg .eq) ri_eq
  xs 0x5015 (.reg .iszero) ri_iszero
  xs 0x5018 (.push [0x50, 0x46] (by decide)) ri_push
  xji 0x5019 0x5046 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x5047
  exact ⟨_, h⟩

/-- Skip the `unkill_me` test: `0x5047` to `0x5075`. -/
theorem dq_skip_3046f972 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x5047 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x3046f972) :
    ∃ G', XAt sevm post 0x5075 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x504c (.push [0x30, 0x46, 0xf9, 0x72] (by decide)) ri_push
  xs 0x504e (.push [0x00] (by decide)) ri_push
  xs 0x504f (.reg .mload) ri_mload_vy0
  xs 0x5050 (.reg .eq) ri_eq
  xs 0x5051 (.reg .iszero) ri_iszero
  xs 0x5054 (.push [0x50, 0x74] (by decide)) ri_push
  xji 0x5055 0x5074 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x5075
  exact ⟨_, h⟩

/-- Fall into `coins`'s body at `0x5083`. -/
theorem dq_arm_coins {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selCoins)
    (h : XAt sevm post 0x5075 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x5083 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x507a (.push [0xc6, 0x61, 0x06, 0x57] (by decide)) ri_push
  xs 0x507c (.push [0x00] (by decide)) ri_push
  xs 0x507d (.reg .mload) ri_mload_vy0
  xs 0x507e (.reg .eq) ri_eq
  xs 0x507f (.reg .iszero) ri_iszero
  xs 0x5082 (.push [0x50, 0xb4] (by decide)) ri_push
  xji 0x5083 0x50b4 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Fall into `balances`'s body at `0x50c3`. -/
theorem dq_arm_balances {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selBalances)
    (h : XAt sevm post 0x50b5 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x50c3 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x50ba (.push [0x49, 0x03, 0xb0, 0xd1] (by decide)) ri_push
  xs 0x50bc (.push [0x00] (by decide)) ri_push
  xs 0x50bd (.reg .mload) ri_mload_vy0
  xs 0x50be (.reg .eq) ri_eq
  xs 0x50bf (.reg .iszero) ri_iszero
  xs 0x50c2 (.push [0x50, 0xf4] (by decide)) ri_push
  xji 0x50c3 0x50f4 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Skip the `coins` test: `0x5075` to `0x50b5`. -/
theorem dq_skip_c6610657 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x5075 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0xc6610657) :
    ∃ G', XAt sevm post 0x50b5 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x507a (.push [0xc6, 0x61, 0x06, 0x57] (by decide)) ri_push
  xs 0x507c (.push [0x00] (by decide)) ri_push
  xs 0x507d (.reg .mload) ri_mload_vy0
  xs 0x507e (.reg .eq) ri_eq
  xs 0x507f (.reg .iszero) ri_iszero
  xs 0x5082 (.push [0x50, 0xb4] (by decide)) ri_push
  xji 0x5083 0x50b4 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x50b5
  exact ⟨_, h⟩

/-- Skip the `balances` test: `0x50b5` to `0x50f5`. -/
theorem dq_skip_4903b0d1 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x50b5 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x4903b0d1) :
    ∃ G', XAt sevm post 0x50f5 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x50ba (.push [0x49, 0x03, 0xb0, 0xd1] (by decide)) ri_push
  xs 0x50bc (.push [0x00] (by decide)) ri_push
  xs 0x50bd (.reg .mload) ri_mload_vy0
  xs 0x50be (.reg .eq) ri_eq
  xs 0x50bf (.reg .iszero) ri_iszero
  xs 0x50c2 (.push [0x50, 0xf4] (by decide)) ri_push
  xji 0x50c3 0x50f4 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x50f5
  exact ⟨_, h⟩

/-- Fall into `fee`'s body at `0x5103`. -/
theorem dq_arm_fee {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selFee)
    (h : XAt sevm post 0x50f5 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x5103 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x50fa (.push [0xdd, 0xca, 0x3f, 0x43] (by decide)) ri_push
  xs 0x50fc (.push [0x00] (by decide)) ri_push
  xs 0x50fd (.reg .mload) ri_mload_vy0
  xs 0x50fe (.reg .eq) ri_eq
  xs 0x50ff (.reg .iszero) ri_iszero
  xs 0x5102 (.push [0x51, 0x1b] (by decide)) ri_push
  xji 0x5103 0x511b hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Fall into `admin_fee`'s body at `0x512a`. -/
theorem dq_arm_adminFee {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selAdminFee)
    (h : XAt sevm post 0x511c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x512a (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x5121 (.push [0xfe, 0xe3, 0xf7, 0xf9] (by decide)) ri_push
  xs 0x5123 (.push [0x00] (by decide)) ri_push
  xs 0x5124 (.reg .mload) ri_mload_vy0
  xs 0x5125 (.reg .eq) ri_eq
  xs 0x5126 (.reg .iszero) ri_iszero
  xs 0x5129 (.push [0x51, 0x42] (by decide)) ri_push
  xji 0x512a 0x5142 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Fall into `owner`'s body at `0x5151`. -/
theorem dq_arm_owner {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selOwner)
    (h : XAt sevm post 0x5143 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x5151 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x5148 (.push [0x8d, 0xa5, 0xcb, 0x5b] (by decide)) ri_push
  xs 0x514a (.push [0x00] (by decide)) ri_push
  xs 0x514b (.reg .mload) ri_mload_vy0
  xs 0x514c (.reg .eq) ri_eq
  xs 0x514d (.reg .iszero) ri_iszero
  xs 0x5150 (.push [0x51, 0x69] (by decide)) ri_push
  xji 0x5151 0x5169 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Skip the `fee` test: `0x50f5` to `0x511c`. -/
theorem dq_skip_ddca3f43 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x50f5 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0xddca3f43) :
    ∃ G', XAt sevm post 0x511c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x50fa (.push [0xdd, 0xca, 0x3f, 0x43] (by decide)) ri_push
  xs 0x50fc (.push [0x00] (by decide)) ri_push
  xs 0x50fd (.reg .mload) ri_mload_vy0
  xs 0x50fe (.reg .eq) ri_eq
  xs 0x50ff (.reg .iszero) ri_iszero
  xs 0x5102 (.push [0x51, 0x1b] (by decide)) ri_push
  xji 0x5103 0x511b hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x511c
  exact ⟨_, h⟩

/-- Skip the `admin_fee` test: `0x511c` to `0x5143`. -/
theorem dq_skip_fee3f7f9 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x511c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0xfee3f7f9) :
    ∃ G', XAt sevm post 0x5143 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x5121 (.push [0xfe, 0xe3, 0xf7, 0xf9] (by decide)) ri_push
  xs 0x5123 (.push [0x00] (by decide)) ri_push
  xs 0x5124 (.reg .mload) ri_mload_vy0
  xs 0x5125 (.reg .eq) ri_eq
  xs 0x5126 (.reg .iszero) ri_iszero
  xs 0x5129 (.push [0x51, 0x42] (by decide)) ri_push
  xji 0x512a 0x5142 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x5143
  exact ⟨_, h⟩

/-- Skip the `owner` test: `0x5143` to `0x516a`. -/
theorem dq_skip_8da5cb5b {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x5143 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x8da5cb5b) :
    ∃ G', XAt sevm post 0x516a (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x5148 (.push [0x8d, 0xa5, 0xcb, 0x5b] (by decide)) ri_push
  xs 0x514a (.push [0x00] (by decide)) ri_push
  xs 0x514b (.reg .mload) ri_mload_vy0
  xs 0x514c (.reg .eq) ri_eq
  xs 0x514d (.reg .iszero) ri_iszero
  xs 0x5150 (.push [0x51, 0x69] (by decide)) ri_push
  xji 0x5151 0x5169 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x516a
  exact ⟨_, h⟩

/-- Fall into `initial_A`'s body at `0x5178`. -/
theorem dq_arm_initialA {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selInitialA)
    (h : XAt sevm post 0x516a (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x5178 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x516f (.push [0x54, 0x09, 0x49, 0x1a] (by decide)) ri_push
  xs 0x5171 (.push [0x00] (by decide)) ri_push
  xs 0x5172 (.reg .mload) ri_mload_vy0
  xs 0x5173 (.reg .eq) ri_eq
  xs 0x5174 (.reg .iszero) ri_iszero
  xs 0x5177 (.push [0x51, 0x90] (by decide)) ri_push
  xji 0x5178 0x5190 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Fall into `future_A`'s body at `0x519f`. -/
theorem dq_arm_futureA {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selFutureA)
    (h : XAt sevm post 0x5191 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x519f (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x5196 (.push [0xb4, 0xb5, 0x77, 0xad] (by decide)) ri_push
  xs 0x5198 (.push [0x00] (by decide)) ri_push
  xs 0x5199 (.reg .mload) ri_mload_vy0
  xs 0x519a (.reg .eq) ri_eq
  xs 0x519b (.reg .iszero) ri_iszero
  xs 0x519e (.push [0x51, 0xb7] (by decide)) ri_push
  xji 0x519f 0x51b7 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Fall into `initial_A_time`'s body at `0x51c6`. -/
theorem dq_arm_initialATime {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selInitialATime)
    (h : XAt sevm post 0x51b8 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x51c6 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x51bd (.push [0x20, 0x81, 0x06, 0x6c] (by decide)) ri_push
  xs 0x51bf (.push [0x00] (by decide)) ri_push
  xs 0x51c0 (.reg .mload) ri_mload_vy0
  xs 0x51c1 (.reg .eq) ri_eq
  xs 0x51c2 (.reg .iszero) ri_iszero
  xs 0x51c5 (.push [0x51, 0xde] (by decide)) ri_push
  xji 0x51c6 0x51de hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Skip the `initial_A` test: `0x516a` to `0x5191`. -/
theorem dq_skip_5409491a {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x516a (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x5409491a) :
    ∃ G', XAt sevm post 0x5191 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x516f (.push [0x54, 0x09, 0x49, 0x1a] (by decide)) ri_push
  xs 0x5171 (.push [0x00] (by decide)) ri_push
  xs 0x5172 (.reg .mload) ri_mload_vy0
  xs 0x5173 (.reg .eq) ri_eq
  xs 0x5174 (.reg .iszero) ri_iszero
  xs 0x5177 (.push [0x51, 0x90] (by decide)) ri_push
  xji 0x5178 0x5190 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x5191
  exact ⟨_, h⟩

/-- Skip the `future_A` test: `0x5191` to `0x51b8`. -/
theorem dq_skip_b4b577ad {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x5191 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0xb4b577ad) :
    ∃ G', XAt sevm post 0x51b8 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x5196 (.push [0xb4, 0xb5, 0x77, 0xad] (by decide)) ri_push
  xs 0x5198 (.push [0x00] (by decide)) ri_push
  xs 0x5199 (.reg .mload) ri_mload_vy0
  xs 0x519a (.reg .eq) ri_eq
  xs 0x519b (.reg .iszero) ri_iszero
  xs 0x519e (.push [0x51, 0xb7] (by decide)) ri_push
  xji 0x519f 0x51b7 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x51b8
  exact ⟨_, h⟩

/-- Skip the `initial_A_time` test: `0x51b8` to `0x51df`. -/
theorem dq_skip_2081066c {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x51b8 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x2081066c) :
    ∃ G', XAt sevm post 0x51df (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x51bd (.push [0x20, 0x81, 0x06, 0x6c] (by decide)) ri_push
  xs 0x51bf (.push [0x00] (by decide)) ri_push
  xs 0x51c0 (.reg .mload) ri_mload_vy0
  xs 0x51c1 (.reg .eq) ri_eq
  xs 0x51c2 (.reg .iszero) ri_iszero
  xs 0x51c5 (.push [0x51, 0xde] (by decide)) ri_push
  xji 0x51c6 0x51de hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x51df
  exact ⟨_, h⟩

/-- Fall into `future_A_time`'s body at `0x51ed`. -/
theorem dq_arm_futureATime {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selFutureATime)
    (h : XAt sevm post 0x51df (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x51ed (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x51e4 (.push [0x14, 0x05, 0x22, 0x88] (by decide)) ri_push
  xs 0x51e6 (.push [0x00] (by decide)) ri_push
  xs 0x51e7 (.reg .mload) ri_mload_vy0
  xs 0x51e8 (.reg .eq) ri_eq
  xs 0x51e9 (.reg .iszero) ri_iszero
  xs 0x51ec (.push [0x52, 0x05] (by decide)) ri_push
  xji 0x51ed 0x5205 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Fall into `admin_actions_deadline`'s body at `0x5214`. -/
theorem dq_arm_adminActionsDeadline {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selAdminActionsDeadline)
    (h : XAt sevm post 0x5206 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x5214 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x520b (.push [0x40, 0x5e, 0x28, 0xf8] (by decide)) ri_push
  xs 0x520d (.push [0x00] (by decide)) ri_push
  xs 0x520e (.reg .mload) ri_mload_vy0
  xs 0x520f (.reg .eq) ri_eq
  xs 0x5210 (.reg .iszero) ri_iszero
  xs 0x5213 (.push [0x52, 0x2c] (by decide)) ri_push
  xji 0x5214 0x522c hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Fall into `transfer_ownership_deadline`'s body at `0x523b`. -/
theorem dq_arm_transferOwnershipDeadline {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selTransferOwnershipDeadline)
    (h : XAt sevm post 0x522d (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x523b (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x5232 (.push [0xe0, 0xa0, 0xb5, 0x86] (by decide)) ri_push
  xs 0x5234 (.push [0x00] (by decide)) ri_push
  xs 0x5235 (.reg .mload) ri_mload_vy0
  xs 0x5236 (.reg .eq) ri_eq
  xs 0x5237 (.reg .iszero) ri_iszero
  xs 0x523a (.push [0x52, 0x53] (by decide)) ri_push
  xji 0x523b 0x5253 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Skip the `future_A_time` test: `0x51df` to `0x5206`. -/
theorem dq_skip_14052288 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x51df (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x14052288) :
    ∃ G', XAt sevm post 0x5206 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x51e4 (.push [0x14, 0x05, 0x22, 0x88] (by decide)) ri_push
  xs 0x51e6 (.push [0x00] (by decide)) ri_push
  xs 0x51e7 (.reg .mload) ri_mload_vy0
  xs 0x51e8 (.reg .eq) ri_eq
  xs 0x51e9 (.reg .iszero) ri_iszero
  xs 0x51ec (.push [0x52, 0x05] (by decide)) ri_push
  xji 0x51ed 0x5205 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x5206
  exact ⟨_, h⟩

/-- Skip the `admin_actions_deadline` test: `0x5206` to `0x522d`. -/
theorem dq_skip_405e28f8 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x5206 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x405e28f8) :
    ∃ G', XAt sevm post 0x522d (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x520b (.push [0x40, 0x5e, 0x28, 0xf8] (by decide)) ri_push
  xs 0x520d (.push [0x00] (by decide)) ri_push
  xs 0x520e (.reg .mload) ri_mload_vy0
  xs 0x520f (.reg .eq) ri_eq
  xs 0x5210 (.reg .iszero) ri_iszero
  xs 0x5213 (.push [0x52, 0x2c] (by decide)) ri_push
  xji 0x5214 0x522c hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x522d
  exact ⟨_, h⟩

/-- Skip the `transfer_ownership_deadline` test: `0x522d` to `0x5254`. -/
theorem dq_skip_e0a0b586 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x522d (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0xe0a0b586) :
    ∃ G', XAt sevm post 0x5254 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x5232 (.push [0xe0, 0xa0, 0xb5, 0x86] (by decide)) ri_push
  xs 0x5234 (.push [0x00] (by decide)) ri_push
  xs 0x5235 (.reg .mload) ri_mload_vy0
  xs 0x5236 (.reg .eq) ri_eq
  xs 0x5237 (.reg .iszero) ri_iszero
  xs 0x523a (.push [0x52, 0x53] (by decide)) ri_push
  xji 0x523b 0x5253 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x5254
  exact ⟨_, h⟩

/-- Fall into `future_fee`'s body at `0x5262`. -/
theorem dq_arm_futureFee {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selFutureFee)
    (h : XAt sevm post 0x5254 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x5262 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x5259 (.push [0x58, 0x68, 0x0d, 0x0b] (by decide)) ri_push
  xs 0x525b (.push [0x00] (by decide)) ri_push
  xs 0x525c (.reg .mload) ri_mload_vy0
  xs 0x525d (.reg .eq) ri_eq
  xs 0x525e (.reg .iszero) ri_iszero
  xs 0x5261 (.push [0x52, 0x7a] (by decide)) ri_push
  xji 0x5262 0x527a hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Fall into `future_admin_fee`'s body at `0x5289`. -/
theorem dq_arm_futureAdminFee {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selFutureAdminFee)
    (h : XAt sevm post 0x527b (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x5289 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x5280 (.push [0xe3, 0x82, 0x44, 0x62] (by decide)) ri_push
  xs 0x5282 (.push [0x00] (by decide)) ri_push
  xs 0x5283 (.reg .mload) ri_mload_vy0
  xs 0x5284 (.reg .eq) ri_eq
  xs 0x5285 (.reg .iszero) ri_iszero
  xs 0x5288 (.push [0x52, 0xa1] (by decide)) ri_push
  xji 0x5289 0x52a1 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Fall into `future_owner`'s body at `0x52b0`. -/
theorem dq_arm_futureOwner {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selFutureOwner)
    (h : XAt sevm post 0x52a2 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x52b0 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x52a7 (.push [0x1e, 0xc0, 0xcd, 0xc1] (by decide)) ri_push
  xs 0x52a9 (.push [0x00] (by decide)) ri_push
  xs 0x52aa (.reg .mload) ri_mload_vy0
  xs 0x52ab (.reg .eq) ri_eq
  xs 0x52ac (.reg .iszero) ri_iszero
  xs 0x52af (.push [0x52, 0xc8] (by decide)) ri_push
  xji 0x52b0 0x52c8 hw  -- fall
  · exact ⟨_, h⟩
  · exact absurd (by rw [dq_memword, hsel]; decide) (isNe_jump hw)

/-- Skip the `future_fee` test: `0x5254` to `0x527b`. -/
theorem dq_skip_58680d0b {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x5254 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0x58680d0b) :
    ∃ G', XAt sevm post 0x527b (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x5259 (.push [0x58, 0x68, 0x0d, 0x0b] (by decide)) ri_push
  xs 0x525b (.push [0x00] (by decide)) ri_push
  xs 0x525c (.reg .mload) ri_mload_vy0
  xs 0x525d (.reg .eq) ri_eq
  xs 0x525e (.reg .iszero) ri_iszero
  xs 0x5261 (.push [0x52, 0x7a] (by decide)) ri_push
  xji 0x5262 0x527a hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x527b
  exact ⟨_, h⟩

/-- Skip the `future_admin_fee` test: `0x527b` to `0x52a2`. -/
theorem dq_skip_e3824462 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code)
    (h : XAt sevm post 0x527b (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L)
    (hne : Sevm.selector sevm ≠ 0xe3824462) :
    ∃ G', XAt sevm post 0x52a2 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x5280 (.push [0xe3, 0x82, 0x44, 0x62] (by decide)) ri_push
  xs 0x5282 (.push [0x00] (by decide)) ri_push
  xs 0x5283 (.reg .mload) ri_mload_vy0
  xs 0x5284 (.reg .eq) ri_eq
  xs 0x5285 (.reg .iszero) ri_iszero
  xs 0x5288 (.push [0x52, 0xa1] (by decide)) ri_push
  xji 0x5289 0x52a1 hw  -- taken
  · exact absurd (isNe_fall hw) (by rw [dq_memword]; exact hne)
  xjd 0x52a2
  exact ⟨_, h⟩

end Blanc.Lift.Curve3Pool
