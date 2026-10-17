import Blanc.Lift.Curve3Pool.Walk.Dispatch

/-!
# The dispatcher, arm by arm, on the actual derivation

`Dispatch.lean` walks the dispatcher to `remove_liquidity` in one piece. The views and the ramp
entries need it to other arms, so here it is cut at its arms: `xa_vd_head` (pc `0` to the first
arm, `0x245`, with the prologue's exact memory), one lemma per arm test (`xa_vd_arm_*`: the hit
falls into the body, a miss lands past the next arm's `JUMPDEST`) and per internal-function skip
(`xa_vd_skip_*`). Every state between arms is `St b [] (vdMem sevm) G` with the frame's remaining
children unchanged (the dispatcher spawns nothing).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The dispatcher's memory: the prologue's image over empty memory. -/
abbrev vdMem (sevm : Sevm) : Mem := vyMem Mem.empty (Sevm.dataWord sevm 0)

/-- The arm test read the selector. -/
theorem vd_sel {sevm : Sevm} {x : B256}
    (h : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD (Bytes.toB256 [0]).toNat 32 0) =
      x) : Sevm.selector sevm = x := by
  rw [show (Bytes.toB256 [0]).toNat = 0 from rfl, vyImg_selector] at h
  exact h

/-- An arm test's two outcomes: the hit at `hit`, the miss at `miss`. -/
def VdArm (sevm : Sevm) (post b : Devm) (L : List Exec.Frame) (sel : B256) (hit miss : Nat) :
    Prop :=
  (Sevm.selector sevm = sel ∧ ∃ G', XAt sevm post hit (St b [] (vdMem sevm) G') L) ∨
    (Sevm.selector sevm ≠ sel ∧ ∃ G', XAt sevm post miss (St b [] (vdMem sevm) G') L)

theorem VdArm.hit {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {sel : B256} {hit miss : Nat}
    (h : VdArm sevm post b L sel hit miss) (hs : Sevm.selector sevm = sel) :
    ∃ G', XAt sevm post hit (St b [] (vdMem sevm) G') L := by
  rcases h with ⟨_, h⟩ | ⟨hn, _⟩
  · exact h
  · exact absurd hs hn

theorem VdArm.miss {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {sel : B256}
    {hit miss : Nat} (h : VdArm sevm post b L sel hit miss) (hs : Sevm.selector sevm ≠ sel) :
    ∃ G', XAt sevm post miss (St b [] (vdMem sevm) G') L := by
  rcases h with ⟨he, _⟩ | ⟨_, h⟩
  · exact absurd he hs
  · exact h

section

variable {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}

/-- **From the frame's start to the first arm** (`0x245`), with the prologue's exact memory. -/
theorem xa_vd_head (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x245 (St b [] (vdMem sevm) G') L := by

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

/-- Arm test at `0x245` (`selA`). -/
theorem xa_vd_arm_0245 (hcode : sevm.code = code)
    (h : XAt sevm post 0x245 (St b [] (vdMem sevm) G) L) :
    VdArm sevm post b L selA 0x253 0x27a := by
  xs 0x24a (.push [0xf4, 0x46, 0xc1, 0xd0] (by decide)) ri_push
  xs 0x24c (.push [0x00] (by decide)) ri_push
  xs 0x24d (.reg .mload) ri_mload_vy0
  xs 0x24e (.reg .eq) ri_eq
  xs 0x24f (.reg .iszero) ri_iszero
  xs 0x252 (.push [0x02, 0x79] (by decide)) ri_push
  xji 0x253 0x279 hw
  · exact .inl ⟨(vd_sel (isNe_fall hw)).trans (by decide), _, h⟩
  · xjd 0x27a
    exact .inr ⟨fun e => isNe_jump hw (((vd_sel rfl).symm.trans e).trans (by decide)), _, h⟩

/-- Arm test at `0x90e` (`selGetVirtualPrice`). -/
theorem xa_vd_arm_090e (hcode : sevm.code = code)
    (h : XAt sevm post 0x90e (St b [] (vdMem sevm) G) L) :
    VdArm sevm post b L selGetVirtualPrice 0x91c 0xaf9 := by
  xs 0x913 (.push [0xbb, 0x7b, 0x8b, 0x80] (by decide)) ri_push
  xs 0x915 (.push [0x00] (by decide)) ri_push
  xs 0x916 (.reg .mload) ri_mload_vy0
  xs 0x917 (.reg .eq) ri_eq
  xs 0x918 (.reg .iszero) ri_iszero
  xs 0x91b (.push [0x0a, 0xf8] (by decide)) ri_push
  xji 0x91c 0xaf8 hw
  · exact .inl ⟨(vd_sel (isNe_fall hw)).trans (by decide), _, h⟩
  · xjd 0xaf9
    exact .inr ⟨fun e => isNe_jump hw (((vd_sel rfl).symm.trans e).trans (by decide)), _, h⟩

/-- Arm test at `0xaf9` (`selCalcTokenAmount`). -/
theorem xa_vd_arm_0af9 (hcode : sevm.code = code)
    (h : XAt sevm post 0xaf9 (St b [] (vdMem sevm) G) L) :
    VdArm sevm post b L selCalcTokenAmount 0xb07 0xe47 := by
  xs 0xafe (.push [0x38, 0x83, 0xe1, 0x19] (by decide)) ri_push
  xs 0xb00 (.push [0x00] (by decide)) ri_push
  xs 0xb01 (.reg .mload) ri_mload_vy0
  xs 0xb02 (.reg .eq) ri_eq
  xs 0xb03 (.reg .iszero) ri_iszero
  xs 0xb06 (.push [0x0e, 0x46] (by decide)) ri_push
  xji 0xb07 0xe46 hw
  · exact .inl ⟨(vd_sel (isNe_fall hw)).trans (by decide), _, h⟩
  · xjd 0xe47
    exact .inr ⟨fun e => isNe_jump hw (((vd_sel rfl).symm.trans e).trans (by decide)), _, h⟩

/-- Arm test at `0xe47` (`selAddLiquidity`). -/
theorem xa_vd_arm_0e47 (hcode : sevm.code = code)
    (h : XAt sevm post 0xe47 (St b [] (vdMem sevm) G) L) :
    VdArm sevm post b L selAddLiquidity 0xe55 0x189d := by
  xs 0xe4c (.push [0x45, 0x15, 0xce, 0xf3] (by decide)) ri_push
  xs 0xe4e (.push [0x00] (by decide)) ri_push
  xs 0xe4f (.reg .mload) ri_mload_vy0
  xs 0xe50 (.reg .eq) ri_eq
  xs 0xe51 (.reg .iszero) ri_iszero
  xs 0xe54 (.push [0x18, 0x9c] (by decide)) ri_push
  xji 0xe55 0x189c hw
  · exact .inl ⟨(vd_sel (isNe_fall hw)).trans (by decide), _, h⟩
  · xjd 0x189d
    exact .inr ⟨fun e => isNe_jump hw (((vd_sel rfl).symm.trans e).trans (by decide)), _, h⟩

/-- Arm test at `0x1d14` (`selGetDy`). -/
theorem xa_vd_arm_1d14 (hcode : sevm.code = code)
    (h : XAt sevm post 0x1d14 (St b [] (vdMem sevm) G) L) :
    VdArm sevm post b L selGetDy 0x1d22 0x2046 := by
  xs 0x1d19 (.push [0x5e, 0x0d, 0x44, 0x3f] (by decide)) ri_push
  xs 0x1d1b (.push [0x00] (by decide)) ri_push
  xs 0x1d1c (.reg .mload) ri_mload_vy0
  xs 0x1d1d (.reg .eq) ri_eq
  xs 0x1d1e (.reg .iszero) ri_iszero
  xs 0x1d21 (.push [0x20, 0x45] (by decide)) ri_push
  xji 0x1d22 0x2045 hw
  · exact .inl ⟨(vd_sel (isNe_fall hw)).trans (by decide), _, h⟩
  · xjd 0x2046
    exact .inr ⟨fun e => isNe_jump hw (((vd_sel rfl).symm.trans e).trans (by decide)), _, h⟩

/-- Arm test at `0x2046` (`selGetDyUnderlying`). -/
theorem xa_vd_arm_2046 (hcode : sevm.code = code)
    (h : XAt sevm post 0x2046 (St b [] (vdMem sevm) G) L) :
    VdArm sevm post b L selGetDyUnderlying 0x2054 0x230b := by
  xs 0x204b (.push [0x07, 0x21, 0x1e, 0xf7] (by decide)) ri_push
  xs 0x204d (.push [0x00] (by decide)) ri_push
  xs 0x204e (.reg .mload) ri_mload_vy0
  xs 0x204f (.reg .eq) ri_eq
  xs 0x2050 (.reg .iszero) ri_iszero
  xs 0x2053 (.push [0x23, 0x0a] (by decide)) ri_push
  xji 0x2054 0x230a hw
  · exact .inl ⟨(vd_sel (isNe_fall hw)).trans (by decide), _, h⟩
  · xjd 0x230b
    exact .inr ⟨fun e => isNe_jump hw (((vd_sel rfl).symm.trans e).trans (by decide)), _, h⟩

/-- Arm test at `0x230b` (`selExchange`). -/
theorem xa_vd_arm_230b (hcode : sevm.code = code)
    (h : XAt sevm post 0x230b (St b [] (vdMem sevm) G) L) :
    VdArm sevm post b L selExchange 0x2319 0x2c5a := by
  xs 0x2310 (.push [0x3d, 0xf0, 0x21, 0x24] (by decide)) ri_push
  xs 0x2312 (.push [0x00] (by decide)) ri_push
  xs 0x2313 (.reg .mload) ri_mload_vy0
  xs 0x2314 (.reg .eq) ri_eq
  xs 0x2315 (.reg .iszero) ri_iszero
  xs 0x2318 (.push [0x2c, 0x59] (by decide)) ri_push
  xji 0x2319 0x2c59 hw
  · exact .inl ⟨(vd_sel (isNe_fall hw)).trans (by decide), _, h⟩
  · xjd 0x2c5a
    exact .inr ⟨fun e => isNe_jump hw (((vd_sel rfl).symm.trans e).trans (by decide)), _, h⟩

/-- Arm test at `0x2c5a` (`selRemoveLiquidity`). -/
theorem xa_vd_arm_2c5a (hcode : sevm.code = code)
    (h : XAt sevm post 0x2c5a (St b [] (vdMem sevm) G) L) :
    VdArm sevm post b L selRemoveLiquidity 0x2c68 0x3041 := by
  xs 0x2c5f (.push [0xec, 0xb5, 0x86, 0xa5] (by decide)) ri_push
  xs 0x2c61 (.push [0x00] (by decide)) ri_push
  xs 0x2c62 (.reg .mload) ri_mload_vy0
  xs 0x2c63 (.reg .eq) ri_eq
  xs 0x2c64 (.reg .iszero) ri_iszero
  xs 0x2c67 (.push [0x30, 0x40] (by decide)) ri_push
  xji 0x2c68 0x3040 hw
  · exact .inl ⟨(vd_sel (isNe_fall hw)).trans (by decide), _, h⟩
  · xjd 0x3041
    exact .inr ⟨fun e => isNe_jump hw (((vd_sel rfl).symm.trans e).trans (by decide)), _, h⟩

/-- Arm test at `0x3041` (`selRemoveLiquidityImbalance`). -/
theorem xa_vd_arm_3041 (hcode : sevm.code = code)
    (h : XAt sevm post 0x3041 (St b [] (vdMem sevm) G) L) :
    VdArm sevm post b L selRemoveLiquidityImbalance 0x304f 0x3992 := by
  xs 0x3046 (.push [0x9f, 0xda, 0xea, 0x0c] (by decide)) ri_push
  xs 0x3048 (.push [0x00] (by decide)) ri_push
  xs 0x3049 (.reg .mload) ri_mload_vy0
  xs 0x304a (.reg .eq) ri_eq
  xs 0x304b (.reg .iszero) ri_iszero
  xs 0x304e (.push [0x39, 0x91] (by decide)) ri_push
  xji 0x304f 0x3991 hw
  · exact .inl ⟨(vd_sel (isNe_fall hw)).trans (by decide), _, h⟩
  · xjd 0x3992
    exact .inr ⟨fun e => isNe_jump hw (((vd_sel rfl).symm.trans e).trans (by decide)), _, h⟩

/-- Arm test at `0x438a` (`selCalcWithdrawOneCoin`). -/
theorem xa_vd_arm_438a (hcode : sevm.code = code)
    (h : XAt sevm post 0x438a (St b [] (vdMem sevm) G) L) :
    VdArm sevm post b L selCalcWithdrawOneCoin 0x4398 0x43fe := by
  xs 0x438f (.push [0xcc, 0x2b, 0x27, 0xd7] (by decide)) ri_push
  xs 0x4391 (.push [0x00] (by decide)) ri_push
  xs 0x4392 (.reg .mload) ri_mload_vy0
  xs 0x4393 (.reg .eq) ri_eq
  xs 0x4394 (.reg .iszero) ri_iszero
  xs 0x4397 (.push [0x43, 0xfd] (by decide)) ri_push
  xji 0x4398 0x43fd hw
  · exact .inl ⟨(vd_sel (isNe_fall hw)).trans (by decide), _, h⟩
  · xjd 0x43fe
    exact .inr ⟨fun e => isNe_jump hw (((vd_sel rfl).symm.trans e).trans (by decide)), _, h⟩

/-- Arm test at `0x43fe` (`selRemoveLiquidityOneCoin`). -/
theorem xa_vd_arm_43fe (hcode : sevm.code = code)
    (h : XAt sevm post 0x43fe (St b [] (vdMem sevm) G) L) :
    VdArm sevm post b L selRemoveLiquidityOneCoin 0x440c 0x4769 := by
  xs 0x4403 (.push [0x1a, 0x4d, 0x01, 0xd2] (by decide)) ri_push
  xs 0x4405 (.push [0x00] (by decide)) ri_push
  xs 0x4406 (.reg .mload) ri_mload_vy0
  xs 0x4407 (.reg .eq) ri_eq
  xs 0x4408 (.reg .iszero) ri_iszero
  xs 0x440b (.push [0x47, 0x68] (by decide)) ri_push
  xji 0x440c 0x4768 hw
  · exact .inl ⟨(vd_sel (isNe_fall hw)).trans (by decide), _, h⟩
  · xjd 0x4769
    exact .inr ⟨fun e => isNe_jump hw (((vd_sel rfl).symm.trans e).trans (by decide)), _, h⟩

/-- Arm test at `0x4769` (`selRampA`). -/
theorem xa_vd_arm_4769 (hcode : sevm.code = code)
    (h : XAt sevm post 0x4769 (St b [] (vdMem sevm) G) L) :
    VdArm sevm post b L selRampA 0x4777 0x490c := by
  xs 0x476e (.push [0x3c, 0x15, 0x7e, 0x64] (by decide)) ri_push
  xs 0x4770 (.push [0x00] (by decide)) ri_push
  xs 0x4771 (.reg .mload) ri_mload_vy0
  xs 0x4772 (.reg .eq) ri_eq
  xs 0x4773 (.reg .iszero) ri_iszero
  xs 0x4776 (.push [0x49, 0x0b] (by decide)) ri_push
  xji 0x4777 0x490b hw
  · exact .inl ⟨(vd_sel (isNe_fall hw)).trans (by decide), _, h⟩
  · xjd 0x490c
    exact .inr ⟨fun e => isNe_jump hw (((vd_sel rfl).symm.trans e).trans (by decide)), _, h⟩

/-- Arm test at `0x490c` (`selStopRampA`). -/
theorem xa_vd_arm_490c (hcode : sevm.code = code)
    (h : XAt sevm post 0x490c (St b [] (vdMem sevm) G) L) :
    VdArm sevm post b L selStopRampA 0x491a 0x499c := by
  xs 0x4911 (.push [0x55, 0x1a, 0x65, 0x88] (by decide)) ri_push
  xs 0x4913 (.push [0x00] (by decide)) ri_push
  xs 0x4914 (.reg .mload) ri_mload_vy0
  xs 0x4915 (.reg .eq) ri_eq
  xs 0x4916 (.reg .iszero) ri_iszero
  xs 0x4919 (.push [0x49, 0x9b] (by decide)) ri_push
  xji 0x491a 0x499b hw
  · exact .inl ⟨(vd_sel (isNe_fall hw)).trans (by decide), _, h⟩
  · xjd 0x499c
    exact .inr ⟨fun e => isNe_jump hw (((vd_sel rfl).symm.trans e).trans (by decide)), _, h⟩

/-- Skip over an internal function: `0x27a` to `0x39a`. -/
theorem xa_vd_skip_027a (hcode : sevm.code = code)
    (h : XAt sevm post 0x27a (St b [] (vdMem sevm) G) L) :
    ∃ G', XAt sevm post 0x39a (St b [] (vdMem sevm) G') L := by
  xs 0x27c (.push [0x00] (by decide)) ri_push
  xs 0x27d (.reg .iszero) ri_iszero
  xs 0x280 (.push [0x03, 0x99] (by decide)) ri_push
  xji 0x281 0x399 hw
  · exact absurd hw (by decide)
  xjd 0x39a
  exact ⟨_, h⟩

/-- Skip over an internal function: `0x39a` to `0x4c2`. -/
theorem xa_vd_skip_039a (hcode : sevm.code = code)
    (h : XAt sevm post 0x39a (St b [] (vdMem sevm) G) L) :
    ∃ G', XAt sevm post 0x4c2 (St b [] (vdMem sevm) G') L := by
  xs 0x39c (.push [0x00] (by decide)) ri_push
  xs 0x39d (.reg .iszero) ri_iszero
  xs 0x3a0 (.push [0x04, 0xc1] (by decide)) ri_push
  xji 0x3a1 0x4c1 hw
  · exact absurd hw (by decide)
  xjd 0x4c2
  exact ⟨_, h⟩

/-- Skip over an internal function: `0x4c2` to `0x7b0`. -/
theorem xa_vd_skip_04c2 (hcode : sevm.code = code)
    (h : XAt sevm post 0x4c2 (St b [] (vdMem sevm) G) L) :
    ∃ G', XAt sevm post 0x7b0 (St b [] (vdMem sevm) G') L := by
  xs 0x4c4 (.push [0x00] (by decide)) ri_push
  xs 0x4c5 (.reg .iszero) ri_iszero
  xs 0x4c8 (.push [0x07, 0xaf] (by decide)) ri_push
  xji 0x4c9 0x7af hw
  · exact absurd hw (by decide)
  xjd 0x7b0
  exact ⟨_, h⟩

/-- Skip over an internal function: `0x7b0` to `0x90e`. -/
theorem xa_vd_skip_07b0 (hcode : sevm.code = code)
    (h : XAt sevm post 0x7b0 (St b [] (vdMem sevm) G) L) :
    ∃ G', XAt sevm post 0x90e (St b [] (vdMem sevm) G') L := by
  xs 0x7b2 (.push [0x00] (by decide)) ri_push
  xs 0x7b3 (.reg .iszero) ri_iszero
  xs 0x7b6 (.push [0x09, 0x0d] (by decide)) ri_push
  xji 0x7b7 0x90d hw
  · exact absurd hw (by decide)
  xjd 0x90e
  exact ⟨_, h⟩

/-- Skip over an internal function: `0x189d` to `0x1d14`. -/
theorem xa_vd_skip_189d (hcode : sevm.code = code)
    (h : XAt sevm post 0x189d (St b [] (vdMem sevm) G) L) :
    ∃ G', XAt sevm post 0x1d14 (St b [] (vdMem sevm) G') L := by
  xs 0x189f (.push [0x00] (by decide)) ri_push
  xs 0x18a0 (.reg .iszero) ri_iszero
  xs 0x18a3 (.push [0x1d, 0x13] (by decide)) ri_push
  xji 0x18a4 0x1d13 hw
  · exact absurd hw (by decide)
  xjd 0x1d14
  exact ⟨_, h⟩

/-- Skip over an internal function: `0x3992` to `0x3cc3`. -/
theorem xa_vd_skip_3992 (hcode : sevm.code = code)
    (h : XAt sevm post 0x3992 (St b [] (vdMem sevm) G) L) :
    ∃ G', XAt sevm post 0x3cc3 (St b [] (vdMem sevm) G') L := by
  xs 0x3994 (.push [0x00] (by decide)) ri_push
  xs 0x3995 (.reg .iszero) ri_iszero
  xs 0x3998 (.push [0x3c, 0xc2] (by decide)) ri_push
  xji 0x3999 0x3cc2 hw
  · exact absurd hw (by decide)
  xjd 0x3cc3
  exact ⟨_, h⟩

/-- Skip over an internal function: `0x3cc3` to `0x438a`. -/
theorem xa_vd_skip_3cc3 (hcode : sevm.code = code)
    (h : XAt sevm post 0x3cc3 (St b [] (vdMem sevm) G) L) :
    ∃ G', XAt sevm post 0x438a (St b [] (vdMem sevm) G') L := by
  xs 0x3cc5 (.push [0x00] (by decide)) ri_push
  xs 0x3cc6 (.reg .iszero) ri_iszero
  xs 0x3cc9 (.push [0x43, 0x89] (by decide)) ri_push
  xji 0x3cca 0x4389 hw
  · exact absurd hw (by decide)
  xjd 0x438a
  exact ⟨_, h⟩

/-- **The dispatcher hands `A` its body** (`0x253`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_A (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selA) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x253 (St b [] (vdMem sevm) G') L := by
  obtain ⟨_, h⟩ := xa_vd_head hcode hlen hcd h
  exact (xa_vd_arm_0245 hcode h).hit hsel

/-- **The dispatcher hands `getVirtualPrice` its body** (`0x91c`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_getVirtualPrice (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selGetVirtualPrice) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x91c (St b [] (vdMem sevm) G') L := by
  obtain ⟨_, h⟩ := xa_vd_head hcode hlen hcd h
  obtain ⟨_, h⟩ := (xa_vd_arm_0245 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_027a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_039a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_04c2 hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_07b0 hcode h
  exact (xa_vd_arm_090e hcode h).hit hsel

/-- **The dispatcher hands `calcTokenAmount` its body** (`0xb07`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_calcTokenAmount (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selCalcTokenAmount) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0xb07 (St b [] (vdMem sevm) G') L := by
  obtain ⟨_, h⟩ := xa_vd_head hcode hlen hcd h
  obtain ⟨_, h⟩ := (xa_vd_arm_0245 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_027a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_039a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_04c2 hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_07b0 hcode h
  obtain ⟨_, h⟩ := (xa_vd_arm_090e hcode h).miss (by rw [hsel]; decide)
  exact (xa_vd_arm_0af9 hcode h).hit hsel

/-- **The dispatcher hands `getDy` its body** (`0x1d22`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_getDy (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selGetDy) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x1d22 (St b [] (vdMem sevm) G') L := by
  obtain ⟨_, h⟩ := xa_vd_head hcode hlen hcd h
  obtain ⟨_, h⟩ := (xa_vd_arm_0245 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_027a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_039a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_04c2 hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_07b0 hcode h
  obtain ⟨_, h⟩ := (xa_vd_arm_090e hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_0af9 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_0e47 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_189d hcode h
  exact (xa_vd_arm_1d14 hcode h).hit hsel

/-- **The dispatcher hands `getDyUnderlying` its body** (`0x2054`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_getDyUnderlying (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selGetDyUnderlying) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x2054 (St b [] (vdMem sevm) G') L := by
  obtain ⟨_, h⟩ := xa_vd_head hcode hlen hcd h
  obtain ⟨_, h⟩ := (xa_vd_arm_0245 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_027a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_039a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_04c2 hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_07b0 hcode h
  obtain ⟨_, h⟩ := (xa_vd_arm_090e hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_0af9 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_0e47 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_189d hcode h
  obtain ⟨_, h⟩ := (xa_vd_arm_1d14 hcode h).miss (by rw [hsel]; decide)
  exact (xa_vd_arm_2046 hcode h).hit hsel

/-- **The dispatcher hands `calcWithdrawOneCoin` its body** (`0x4398`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_calcWithdrawOneCoin (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selCalcWithdrawOneCoin) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x4398 (St b [] (vdMem sevm) G') L := by
  obtain ⟨_, h⟩ := xa_vd_head hcode hlen hcd h
  obtain ⟨_, h⟩ := (xa_vd_arm_0245 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_027a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_039a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_04c2 hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_07b0 hcode h
  obtain ⟨_, h⟩ := (xa_vd_arm_090e hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_0af9 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_0e47 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_189d hcode h
  obtain ⟨_, h⟩ := (xa_vd_arm_1d14 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_2046 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_230b hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_2c5a hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_3041 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_3992 hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_3cc3 hcode h
  exact (xa_vd_arm_438a hcode h).hit hsel

/-- **The dispatcher hands `rampA` its body** (`0x4777`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_rampA (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRampA) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x4777 (St b [] (vdMem sevm) G') L := by
  obtain ⟨_, h⟩ := xa_vd_head hcode hlen hcd h
  obtain ⟨_, h⟩ := (xa_vd_arm_0245 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_027a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_039a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_04c2 hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_07b0 hcode h
  obtain ⟨_, h⟩ := (xa_vd_arm_090e hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_0af9 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_0e47 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_189d hcode h
  obtain ⟨_, h⟩ := (xa_vd_arm_1d14 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_2046 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_230b hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_2c5a hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_3041 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_3992 hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_3cc3 hcode h
  obtain ⟨_, h⟩ := (xa_vd_arm_438a hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_43fe hcode h).miss (by rw [hsel]; decide)
  exact (xa_vd_arm_4769 hcode h).hit hsel

/-- **The dispatcher hands `stopRampA` its body** (`0x491a`), with the prologue's exact memory
and the frame's remaining children unchanged. -/
theorem xa_vd_stopRampA (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selStopRampA) (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x491a (St b [] (vdMem sevm) G') L := by
  obtain ⟨_, h⟩ := xa_vd_head hcode hlen hcd h
  obtain ⟨_, h⟩ := (xa_vd_arm_0245 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_027a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_039a hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_04c2 hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_07b0 hcode h
  obtain ⟨_, h⟩ := (xa_vd_arm_090e hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_0af9 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_0e47 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_189d hcode h
  obtain ⟨_, h⟩ := (xa_vd_arm_1d14 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_2046 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_230b hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_2c5a hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_3041 hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := xa_vd_skip_3992 hcode h
  obtain ⟨_, h⟩ := xa_vd_skip_3cc3 hcode h
  obtain ⟨_, h⟩ := (xa_vd_arm_438a hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_43fe hcode h).miss (by rw [hsel]; decide)
  obtain ⟨_, h⟩ := (xa_vd_arm_4769 hcode h).miss (by rw [hsel]; decide)
  exact (xa_vd_arm_490c hcode h).hit hsel

end

end Blanc.Lift.Curve3Pool
