import Blanc.Lift.Curve3Pool.Walk.Dispatch
import Blanc.Lift.Curve3Pool.Walk.AdminBalances
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityLoop
import Blanc.Lift.Curve3Pool.Spec

/-!
# `admin_balances`, on the actual derivation

From the frame's entry with the `admin_balances` selector the dispatcher reaches the arm's
body (`0x4c93`, past its test at `0x4c85`): the non-payable guard, the `balanceOf(self)`
staging at `0x140`/`0x160`, the `i < 3` check, the `coins[i]` load at `keccak(0) + i`, one
`STATICCALL` with the output window `0x1c0`, the flag and `RETURNDATASIZE > 31` asserts, the
second `i < 3` check, the `balances[i]` load at `keccak(1) + i`, the coverage assert, and the
difference returned.

`xa_adminBalances` is the frame theorem: a successful frame found no value, spawned exactly
one direct child (coin `k`'s `balanceOf(self)`, static, at least 32 bytes back), left storage
and logs as the child left them, and returned `w - balances[k]`. `adminBalances_raw` is the
`<entry>_raw` safety: the model's step on the decoded call with the `RawEffect` Spec states.

Reuse: the `xs`/`xji`/`xjd`/`xdead` walk macros and `xa_staticcall_img`, `WordAt`/`Region`,
`wchain` from `Blanc/Lift/FrameWalkKit.lean` via `Walk.Kit`; `balEnv`, `adminBalances_step`,
`ri_address` from the lifted-program walk `Walk.AdminBalances`; `EnvOf`/`ReplyAt` from
`Observe.lean`; `RawEffect`/`StorEffect` from `Spec.lean`. Hoist proposal (needs a
`Dispatch.lean` edit, not owned here): share the `0 → 0x3040` dispatcher prefix instead of
re-walking it.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-! ## Dispatcher to the `admin_balances` arm -/

/-- **Dispatcher prefix for `admin_balances`**: from the frame's start to `0x3040` (past the
`remove_liquidity` test, taken). -/
theorem adminBal_disp_to_3040 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAdminBalances)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x3040 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  xs 0x2 (.push [0x04] (by decide)) ri_push
  xs 0x3 (.reg .calldatasize) ri_calldatasize
  xs 0x4 (.reg .lt) ri_lt
  xs 0x5 (.reg .iszero) ri_iszero
  xs 0x8 (.push [0x00, 0x0d] (by decide)) ri_push
  xji 0x9 0xd hw
  · exact absurd (eqCheck_eq_zero hw) (by
      rw [ltCheck_eq_zero_of_le (by rw [B256.toNat_toB256_of_lt hcd]; exact hlen)]; decide)
  xjd 0xe
  xs 0x10 (.push [0x00] (by decide)) ri_push
  xs 0x11 (.reg .calldataload) ri_calldataload
  xs 0x13 (.push [0x1c] (by decide)) ri_push
  xs 0x14 (.reg .mstore) ri_mstore
  xs 0x2a (.push [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0x2c (.push [0x20] (by decide)) ri_push
  xs 0x2d (.reg .mstore) ri_mstore
  xs 0x3e (.push [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) ri_push
  xs 0x40 (.push [0x40] (by decide)) ri_push
  xs 0x41 (.reg .mstore) ri_mstore
  xs 0x62 (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0x64 (.push [0x60] (by decide)) ri_push
  xs 0x65 (.reg .mstore) ri_mstore
  xs 0x7b (.push [0x01, 0x2a, 0x05, 0xf1, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfd, 0xab, 0xf4, 0x1c, 0x00] (by decide)) ri_push
  xs 0x7d (.push [0x80] (by decide)) ri_push
  xs 0x7e (.reg .mstore) ri_mstore
  xs 0x9f (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xd5, 0xfa, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0xa1 (.push [0xa0] (by decide)) ri_push
  xs 0xa2 (.reg .mstore) ri_mstore
  replace h : XAt sevm post 0xa2 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) _) L := h
  have hsw : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD (Bytes.toB256 [0]).toNat 32 0) =
      0xe2e7d264 := by
    rw [show (Bytes.toB256 [0]).toNat = 0 from rfl, vyImg_selector]; exact hsel
  xs 0xa4 (.push [0x00] (by decide)) ri_push
  xs 0xa5 (.reg .iszero) ri_iszero
  xs 0xa8 (.push [0x02, 0x44] (by decide)) ri_push
  xji 0xa9 0x244 hw
  · exact absurd hw (by decide)
  xjd 0x245
  xs 0x24a (.push [0xf4, 0x46, 0xc1, 0xd0] (by decide)) ri_push
  xs 0x24c (.push [0x00] (by decide)) ri_push
  xs 0x24d (.reg .mload) ri_mload_vy0
  xs 0x24e (.reg .eq) ri_eq
  xs 0x24f (.reg .iszero) ri_iszero
  xs 0x252 (.push [0x02, 0x79] (by decide)) ri_push
  xji 0x253 0x279 hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x27a
  xs 0x27c (.push [0x00] (by decide)) ri_push
  xs 0x27d (.reg .iszero) ri_iszero
  xs 0x280 (.push [0x03, 0x99] (by decide)) ri_push
  xji 0x281 0x399 hw
  · exact absurd hw (by decide)
  xjd 0x39a
  xs 0x39c (.push [0x00] (by decide)) ri_push
  xs 0x39d (.reg .iszero) ri_iszero
  xs 0x3a0 (.push [0x04, 0xc1] (by decide)) ri_push
  xji 0x3a1 0x4c1 hw
  · exact absurd hw (by decide)
  xjd 0x4c2
  xs 0x4c4 (.push [0x00] (by decide)) ri_push
  xs 0x4c5 (.reg .iszero) ri_iszero
  xs 0x4c8 (.push [0x07, 0xaf] (by decide)) ri_push
  xji 0x4c9 0x7af hw
  · exact absurd hw (by decide)
  xjd 0x7b0
  xs 0x7b2 (.push [0x00] (by decide)) ri_push
  xs 0x7b3 (.reg .iszero) ri_iszero
  xs 0x7b6 (.push [0x09, 0x0d] (by decide)) ri_push
  xji 0x7b7 0x90d hw
  · exact absurd hw (by decide)
  xjd 0x90e
  xs 0x913 (.push [0xbb, 0x7b, 0x8b, 0x80] (by decide)) ri_push
  xs 0x915 (.push [0x00] (by decide)) ri_push
  xs 0x916 (.reg .mload) ri_mload_vy0
  xs 0x917 (.reg .eq) ri_eq
  xs 0x918 (.reg .iszero) ri_iszero
  xs 0x91b (.push [0x0a, 0xf8] (by decide)) ri_push
  xji 0x91c 0xaf8 hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0xaf9
  xs 0xafe (.push [0x38, 0x83, 0xe1, 0x19] (by decide)) ri_push
  xs 0xb00 (.push [0x00] (by decide)) ri_push
  xs 0xb01 (.reg .mload) ri_mload_vy0
  xs 0xb02 (.reg .eq) ri_eq
  xs 0xb03 (.reg .iszero) ri_iszero
  xs 0xb06 (.push [0x0e, 0x46] (by decide)) ri_push
  xji 0xb07 0xe46 hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0xe47
  xs 0xe4c (.push [0x45, 0x15, 0xce, 0xf3] (by decide)) ri_push
  xs 0xe4e (.push [0x00] (by decide)) ri_push
  xs 0xe4f (.reg .mload) ri_mload_vy0
  xs 0xe50 (.reg .eq) ri_eq
  xs 0xe51 (.reg .iszero) ri_iszero
  xs 0xe54 (.push [0x18, 0x9c] (by decide)) ri_push
  xji 0xe55 0x189c hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x189d
  xs 0x189f (.push [0x00] (by decide)) ri_push
  xs 0x18a0 (.reg .iszero) ri_iszero
  xs 0x18a3 (.push [0x1d, 0x13] (by decide)) ri_push
  xji 0x18a4 0x1d13 hw
  · exact absurd hw (by decide)
  xjd 0x1d14
  xs 0x1d19 (.push [0x5e, 0x0d, 0x44, 0x3f] (by decide)) ri_push
  xs 0x1d1b (.push [0x00] (by decide)) ri_push
  xs 0x1d1c (.reg .mload) ri_mload_vy0
  xs 0x1d1d (.reg .eq) ri_eq
  xs 0x1d1e (.reg .iszero) ri_iszero
  xs 0x1d21 (.push [0x20, 0x45] (by decide)) ri_push
  xji 0x1d22 0x2045 hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x2046
  xs 0x204b (.push [0x07, 0x21, 0x1e, 0xf7] (by decide)) ri_push
  xs 0x204d (.push [0x00] (by decide)) ri_push
  xs 0x204e (.reg .mload) ri_mload_vy0
  xs 0x204f (.reg .eq) ri_eq
  xs 0x2050 (.reg .iszero) ri_iszero
  xs 0x2053 (.push [0x23, 0x0a] (by decide)) ri_push
  xji 0x2054 0x230a hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x230b
  xs 0x2310 (.push [0x3d, 0xf0, 0x21, 0x24] (by decide)) ri_push
  xs 0x2312 (.push [0x00] (by decide)) ri_push
  xs 0x2313 (.reg .mload) ri_mload_vy0
  xs 0x2314 (.reg .eq) ri_eq
  xs 0x2315 (.reg .iszero) ri_iszero
  xs 0x2318 (.push [0x2c, 0x59] (by decide)) ri_push
  xji 0x2319 0x2c59 hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x2c5a
  xs 0x2c5f (.push [0xec, 0xb5, 0x86, 0xa5] (by decide)) ri_push
  xs 0x2c61 (.push [0x00] (by decide)) ri_push
  xs 0x2c62 (.reg .mload) ri_mload_vy0
  xs 0x2c63 (.reg .eq) ri_eq
  xs 0x2c64 (.reg .iszero) ri_iszero
  xs 0x2c67 (.push [0x30, 0x40] (by decide)) ri_push
  xji 0x2c68 0x3040 hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  exact ⟨_, h⟩

/-- **Dispatcher continuation for `admin_balances`**: from `0x3040` to the arm's test
(`0x4c85`), taking every arm in between. -/
theorem adminBal_disp_to_test {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selAdminBalances)
    (h : XAt sevm post 0x3040 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4c85 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  have hsw : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD (Bytes.toB256 [0]).toNat 32 0) =
      0xe2e7d264 := by
    rw [show (Bytes.toB256 [0]).toNat = 0 from rfl, vyImg_selector]; exact hsel
  xjd 0x3041
  xs 0x3046 (.push [0x9f, 0xda, 0xea, 0x0c] (by decide)) ri_push
  xs 0x3048 (.push [0x00] (by decide)) ri_push
  xs 0x3049 (.reg .mload) ri_mload_vy0
  xs 0x304a (.reg .eq) ri_eq
  xs 0x304b (.reg .iszero) ri_iszero
  xs 0x304e (.push [0x39, 0x91] (by decide)) ri_push
  xji 0x304f 0x3991 hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x3992
  xs 0x3994 (.push [0x00] (by decide)) ri_push
  xs 0x3995 (.reg .iszero) ri_iszero
  xs 0x3998 (.push [0x3c, 0xc2] (by decide)) ri_push
  xji 0x3999 0x3cc2 hw
  · exact absurd hw (by decide)
  xjd 0x3cc3
  xs 0x3cc5 (.push [0x00] (by decide)) ri_push
  xs 0x3cc6 (.reg .iszero) ri_iszero
  xs 0x3cc9 (.push [0x43, 0x89] (by decide)) ri_push
  xji 0x3cca 0x4389 hw
  · exact absurd hw (by decide)
  xjd 0x438a
  xs 0x438f (.push [0xcc, 0x2b, 0x27, 0xd7] (by decide)) ri_push
  xs 0x4391 (.push [0x00] (by decide)) ri_push
  xs 0x4392 (.reg .mload) ri_mload_vy0
  xs 0x4393 (.reg .eq) ri_eq
  xs 0x4394 (.reg .iszero) ri_iszero
  xs 0x4397 (.push [0x43, 0xfd] (by decide)) ri_push
  xji 0x4398 0x43fd hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x43fe
  xs 0x4403 (.push [0x1a, 0x4d, 0x01, 0xd2] (by decide)) ri_push
  xs 0x4405 (.push [0x00] (by decide)) ri_push
  xs 0x4406 (.reg .mload) ri_mload_vy0
  xs 0x4407 (.reg .eq) ri_eq
  xs 0x4408 (.reg .iszero) ri_iszero
  xs 0x440b (.push [0x47, 0x68] (by decide)) ri_push
  xji 0x440c 0x4768 hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x4769
  xs 0x476e (.push [0x3c, 0x15, 0x7e, 0x64] (by decide)) ri_push
  xs 0x4770 (.push [0x00] (by decide)) ri_push
  xs 0x4771 (.reg .mload) ri_mload_vy0
  xs 0x4772 (.reg .eq) ri_eq
  xs 0x4773 (.reg .iszero) ri_iszero
  xs 0x4776 (.push [0x49, 0x0b] (by decide)) ri_push
  xji 0x4777 0x490b hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x490c
  xs 0x4911 (.push [0x55, 0x1a, 0x65, 0x88] (by decide)) ri_push
  xs 0x4913 (.push [0x00] (by decide)) ri_push
  xs 0x4914 (.reg .mload) ri_mload_vy0
  xs 0x4915 (.reg .eq) ri_eq
  xs 0x4916 (.reg .iszero) ri_iszero
  xs 0x4919 (.push [0x49, 0x9b] (by decide)) ri_push
  xji 0x491a 0x499b hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x499c
  xs 0x49a1 (.push [0x5b, 0x5a, 0x14, 0x67] (by decide)) ri_push
  xs 0x49a3 (.push [0x00] (by decide)) ri_push
  xs 0x49a4 (.reg .mload) ri_mload_vy0
  xs 0x49a5 (.reg .eq) ri_eq
  xs 0x49a6 (.reg .iszero) ri_iszero
  xs 0x49a9 (.push [0x4a, 0x64] (by decide)) ri_push
  xji 0x49aa 0x4a64 hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x4a65
  xs 0x4a6a (.push [0x4f, 0x12, 0xfe, 0x97] (by decide)) ri_push
  xs 0x4a6c (.push [0x00] (by decide)) ri_push
  xs 0x4a6d (.reg .mload) ri_mload_vy0
  xs 0x4a6e (.reg .eq) ri_eq
  xs 0x4a6f (.reg .iszero) ri_iszero
  xs 0x4a72 (.push [0x4b, 0x03] (by decide)) ri_push
  xji 0x4a73 0x4b03 hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x4b04
  xs 0x4b09 (.push [0x22, 0x68, 0x40, 0xfb] (by decide)) ri_push
  xs 0x4b0b (.push [0x00] (by decide)) ri_push
  xs 0x4b0c (.reg .mload) ri_mload_vy0
  xs 0x4b0d (.reg .eq) ri_eq
  xs 0x4b0e (.reg .iszero) ri_iszero
  xs 0x4b11 (.push [0x4b, 0x31] (by decide)) ri_push
  xji 0x4b12 0x4b31 hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x4b32
  xs 0x4b37 (.push [0x6b, 0x44, 0x1a, 0x40] (by decide)) ri_push
  xs 0x4b39 (.push [0x00] (by decide)) ri_push
  xs 0x4b3a (.reg .mload) ri_mload_vy0
  xs 0x4b3b (.reg .eq) ri_eq
  xs 0x4b3c (.reg .iszero) ri_iszero
  xs 0x4b3f (.push [0x4b, 0xd2] (by decide)) ri_push
  xji 0x4b40 0x4bd2 hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x4bd3
  xs 0x4bd8 (.push [0x6a, 0x1c, 0x05, 0xae] (by decide)) ri_push
  xs 0x4bda (.push [0x00] (by decide)) ri_push
  xs 0x4bdb (.reg .mload) ri_mload_vy0
  xs 0x4bdc (.reg .eq) ri_eq
  xs 0x4bdd (.reg .iszero) ri_iszero
  xs 0x4be0 (.push [0x4c, 0x56] (by decide)) ri_push
  xji 0x4be1 0x4c56 hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x4c57
  xs 0x4c5c (.push [0x86, 0xfb, 0xf1, 0x93] (by decide)) ri_push
  xs 0x4c5e (.push [0x00] (by decide)) ri_push
  xs 0x4c5f (.reg .mload) ri_mload_vy0
  xs 0x4c60 (.reg .eq) ri_eq
  xs 0x4c61 (.reg .iszero) ri_iszero
  xs 0x4c64 (.push [0x4c, 0x84] (by decide)) ri_push
  xji 0x4c65 0x4c84 hw
  · exact absurd (isNe_fall hw) (by rw [hsw]; decide)
  xjd 0x4c85
  exact ⟨_, h⟩

/-- **The dispatcher hands `admin_balances` its body** (past the arm's own test), with the
prologue's exact memory and the frame's remaining children unchanged. -/
theorem adminBal_disp_to_body {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selAdminBalances)
    (h : XAt sevm post 0x4c85 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4c93 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  have hsw : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD (Bytes.toB256 [0]).toNat 32 0) =
      0xe2e7d264 := by
    rw [show (Bytes.toB256 [0]).toNat = 0 from rfl, vyImg_selector]; exact hsel
  xs 0x4c8a (.push [0xe2, 0xe7, 0xd2, 0x64] (by decide)) ri_push
  xs 0x4c8c (.push [0x00] (by decide)) ri_push
  xs 0x4c8d (.reg .mload) ri_mload_vy0
  xs 0x4c8e (.reg .eq) ri_eq
  xs 0x4c8f (.reg .iszero) ri_iszero
  xs 0x4c92 (.push [0x4d, 0x2b] (by decide)) ri_push
  xji 0x4c93 0x4d2b hw
  · exact ⟨_, h⟩
  · exact absurd (by rw [hsw]; decide) (isNe_jump hw)

/-- **The dispatcher skips `admin_balances`**: the taken branch reaches the
`withdraw_admin_fees` test (`0x4d2c`). For the withdraw/donate walks. -/
theorem adminBal_disp_taken {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hne : Sevm.selector sevm ≠ selAdminBalances)
    (h : XAt sevm post 0x4c85 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4d2c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  have hsw : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD (Bytes.toB256 [0]).toNat 32 0) =
      Sevm.selector sevm := by
    rw [show (Bytes.toB256 [0]).toNat = 0 from rfl, vyImg_selector]; rfl
  have hpush : (Bytes.toB256 [0xe2, 0xe7, 0xd2, 0x64]) = selAdminBalances := by decide
  xs 0x4c8a (.push [0xe2, 0xe7, 0xd2, 0x64] (by decide)) ri_push
  xs 0x4c8c (.push [0x00] (by decide)) ri_push
  xs 0x4c8d (.reg .mload) ri_mload_vy0
  xs 0x4c8e (.reg .eq) ri_eq
  xs 0x4c8f (.reg .iszero) ri_iszero
  xs 0x4c92 (.push [0x4d, 0x2b] (by decide)) ri_push
  xji 0x4c93 0x4d2b hw
  · have heq := isNe_fall hw
    rw [hsw, hpush] at heq
    exact absurd heq hne
  · xjd 0x4d2c
    exact ⟨_, h⟩

/-! ## The `balanceOf` calldata in the image -/

theorem adminBal_sel_bytes :
    (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes = List.replicate 28 0 ++ balanceOfSel := by
  decide

/-- The `balanceOf(self)` calldata the staging writes leave at `0x15c` (the later zero word at
`0xc0` is disjoint from the window). -/
theorem adminBal_input (img : Bytes) (self : Adr) :
    ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x140
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x160 self.toB256.toBytes) 0xc0
      (Bytes.toB256 [0]).toBytes).sliceD 0x15c 0x24 0) = balanceOfData self := by
  show ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x140
    (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x160 self.toB256.toBytes) 0xc0
    (Bytes.toB256 [0]).toBytes).sliceD 0x15c 0x24 0) = balanceOfSel ++ self.toB256.toBytes
  have hsel : Region (Bytes.writeAt img 0x140 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes)
      0x15c balanceOfSel := by
    have := Region.write_self img 0x140 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes
    rw [adminBal_sel_bytes] at this
    exact this.right
  have hsel2 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x140
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x160 self.toB256.toBytes) 0xc0
      (Bytes.toB256 [0]).toBytes) 0x15c balanceOfSel :=
    Region.write_other
      (Region.write_other hsel (by simp only [balanceOfSel, B256.length_toBytes,
        List.length_cons, List.length_nil]; omega)) (Or.inr (by decide))
  refine Region.slice (Region.append' (o' := 0x160) ?_ ?_ (by rfl))
    (by simp only [balanceOfSel, List.length_append, B256.length_toBytes, List.length_cons,
      List.length_nil])
  · exact hsel2
  · exact Region.write_other (Region.write_self _ _ _) (Or.inr (by decide))

/-- The answer word the `STATICCALL` wrote at `0x1c0` reads back. -/
theorem adminBal_read_ans (img : Bytes) (out : Bytes) (hlen : (out.take 32).length = 32) :
    Bytes.toB256 ((Bytes.writeAt img 0x1c0 (out.take 32)).sliceD 0x1c0 32 0) =
      Bytes.toB256 (out.take 32) :=
  Region.read (Region.write_self img 0x1c0 (out.take 32)) hlen

/-- Any full word just written reads back, as bytes. -/
theorem adminBal_read_wordB (img : Bytes) (o : Nat) (xs : Bytes) (hlen : 32 = xs.length) :
    (Bytes.writeAt img o xs).sliceD o 32 0 = xs :=
  Region.slice (Region.write_self img o xs) hlen

/-! ## The arm's body -/

/-- **The `admin_balances` body** (`0x4c93` → `RETURN`): no value; one static child (coin `k`'s
`balanceOf(self)`, at least 32 bytes back); storage kept; logs the child's; the difference
returned. -/
theorem adminBal_body {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcoin : ∀ i, i < 3 → ¬ sevm.benvStat.rules.isPrecomp
      (((b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i)).toAdr))
    (h : XAt sevm post 0x4c93 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    sevm.value = 0 ∧
    ∃ (k : Fin 3) (c : Exec.Frame) (out : Bytes),
      L = [c] ∧
      (Sevm.argWord sevm 0).toNat = k.val ∧
      c.sevm.currentTarget = ((b.getStor sevm.currentTarget).get (coinSlot k)).toAdr ∧
      c.sevm.data = balanceOfData sevm.currentTarget ∧
      c.sevm.isStatic = true ∧
      c.post.output = out ∧ 32 ≤ out.length ∧
      c.post.logs = [] ∧
      (∀ x, (post.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x) ∧
      post.logs = b.logs ++ c.post.logs ∧
      post.output = ((Bytes.toB256 (out.take 32)) -
        (b.getStor sevm.currentTarget).get (balanceSlot k)).toBytes ∧
      ((b.getStor sevm.currentTarget).get (balanceSlot k)).toNat ≤
        (Bytes.toB256 (out.take 32)).toNat := by
  have hR : Mem.Reads (vyMem Mem.empty (Sevm.dataWord sevm 0))
      (vyImg [] (Sevm.dataWord sevm 0)) :=
    vyMem_reads Mem.wf_empty Mem.reads_empty _
  have hW : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  xs 0x4c94 (.reg .callvalue) ri_callvalue
  xs 0x4c95 (.reg .iszero) ri_iszero
  xs 0x4c98 (.push [0x4c, 0x9d] (by decide)) ri_push
  xji 0x4c99 0x4c9d hw
  · xdead
  have hval : sevm.value = 0 := eqCheck_ne_zero_eq hw
  clear hw
  xjd 0x4c9e
  xs 0x4ca0 (.push [0x20] (by decide)) ri_push
  xs 0x4ca3 (.push [0x01, 0xc0] (by decide)) ri_push
  xs 0x4ca5 (.push [0x24] (by decide)) ri_push
  xs 0x4caa (.push [0x70, 0xa0, 0x82, 0x31] (by decide)) ri_push
  xs 0x4cad (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x4cae (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  xs 0x4caf (.reg .address) ri_address
  xs 0x4cb2 (.push [0x01, 0x60] (by decide)) ri_push
  xmo 0x4cb3 (.reg .mstore) (ri_mstore_imgAt (o := 0x160) rfl)
  xs 0x4cb6 (.push [0x01, 0x5c] (by decide)) ri_push
  xs 0x4cb8 (.push [0x04] (by decide)) ri_push
  xs 0x4cb9 (.reg .calldataload) ri_calldataload
  xs 0x4cbb (.push [0x03] (by decide)) ri_push
  xs 0x4cbc (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x4cbd (.reg .lt) ri_lt
  xs 0x4cc0 (.push [0x4c, 0xc5] (by decide)) ri_push
  xji 0x4cc1 0x4cc5 hw
  · xdead
  have hlt : Sevm.dataWord sevm (Bytes.toB256 [4]) < Bytes.toB256 [3] := by
    by_contra hcon
    exact absurd (ite_eq_right hcon) hw
  clear hw
  have hltN : (Sevm.dataWord sevm (Bytes.toB256 [4])).toNat < 3 := by
    rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [3]).toNat = 3 by decide] at hlt
    exact hlt
  obtain ⟨k, hk_def⟩ : ∃ k : Fin 3, k.val = (Sevm.dataWord sevm (Bytes.toB256 [4])).toNat :=
    ⟨⟨_, hltN⟩, rfl⟩
  have hargv : Sevm.dataWord sevm (Bytes.toB256 [4]) = Nat.toB256 k.val := by
    apply B256.toNat_inj
    rw [hk_def, B256.toNat_toB256_of_lt (by omega)]
  have hslot : coinsBase + Sevm.dataWord sevm (Bytes.toB256 [4]) = coinSlot k := by
    rw [hargv]; rfl
  xjd 0x4cc6
  xs 0x4cc8 (.push [0x00] (by decide)) ri_push
  xs 0x4cca (.push [0xc0] (by decide)) ri_push
  xmo 0x4ccb (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xs 0x4ccd (.push [0x20] (by decide)) ri_push
  xs 0x4ccf (.push [0xc0] (by decide)) ri_push
  xmo 0x4cd0 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_zero] at h
  xs 0x4cd1 (.reg .add) ri_add
  rw [hslot] at h
  xw 0x4cd2 (.reg .sload) ri_sload
  rw [getStorVal_eq] at h
  xs 0x4cd3 (.reg .gas) ri_gas_remaining
  replace h := xa_staticcall_img (pc' := 0x4cd4) (i := 0x15c) (n := 0x24) (o := 0x1c0)
    (z := 0x20) hfork (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW h
  clear hR hW
  obtain ⟨d1, flag, out, M', L1, h, _, hR, hW, hrd, hob, hstor1, hlogs1, hk⟩ := h
  xs 0x4cd7 (.push [0x4c, 0xdc] (by decide)) ri_push
  xji 0x4cd8 0x4cdc hw
  · xdead
  rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, -, -, -, -, htgt, hdata, hstat, hout, hclogs, -, -⟩
  · exact absurd hpre (hcoin k.val k.isLt)
  clear hk hw
  rw [adminBal_input] at hdata
  xjd 0x4cdd
  xs 0x4cdf (.push [0x1f] (by decide)) ri_push
  xs 0x4ce0 (.reg .returndatasize) ri_returndatasize
  xs 0x4ce1 (.reg .gt) ri_gt
  xs 0x4ce4 (.push [0x4c, 0xe9] (by decide)) ri_push
  xji 0x4ce5 0x4ce9 hw
  · xdead
  have hlen32 : 32 ≤ out.length := by
    have hgt := gtCheck_ne_zero hw
    rw [B256.lt_iff_toNat_lt_toNat, hrd, B256.toNat_toB256_of_lt hob,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide] at hgt
    omega
  clear hw
  xjd 0x4cea
  xs 0x4cec (.push [0x00] (by decide)) ri_push
  xs 0x4ced (.reg .pop) ri_pop
  xs 0x4cf0 (.push [0x01, 0xc0] (by decide)) ri_push
  xmo 0x4cf1 (.reg .mload) (ri_mload_imgAt (o := 0x1c0) rfl)
  have hlen : (out.take 32).length = 32 := by rw [List.length_take]; omega
  rw [adminBal_read_ans _ _ hlen] at h
  clear hlen
  xs 0x4cf3 (.push [0x04] (by decide)) ri_push
  xs 0x4cf4 (.reg .calldataload) ri_calldataload
  xs 0x4cf6 (.push [0x03] (by decide)) ri_push
  xs 0x4cf7 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x4cf8 (.reg .lt) ri_lt
  xs 0x4cfb (.push [0x4d, 0x00] (by decide)) ri_push
  xji 0x4cfc 0x4d00 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt hlt)
  clear hw
  xjd 0x4d01
  xs 0x4d03 (.push [0x01] (by decide)) ri_push
  xs 0x4d05 (.push [0xc0] (by decide)) ri_push
  xmo 0x4d06 (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  xs 0x4d08 (.push [0x20] (by decide)) ri_push
  xs 0x4d0a (.push [0xc0] (by decide)) ri_push
  xmo 0x4d0b (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0x4d0c (.reg .add) ri_add
  have hslot2 : balancesBase + Sevm.dataWord sevm (Bytes.toB256 [4]) = balanceSlot k := by
    rw [hargv]; rfl
  rw [hslot2] at h
  xw 0x4d0d (.reg .sload) ri_sload
  rw [getStorVal_eq, hstor1, afterSload_getStor] at h
  xs 0x4d0e (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x4d0f (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x4d10 (.reg .lt) ri_lt
  xs 0x4d11 (.reg .iszero) ri_iszero
  xs 0x4d14 (.push [0x4d, 0x19] (by decide)) ri_push
  xji 0x4d15 0x4d19 hw
  · xdead
  have hle : ((b.getStor sevm.currentTarget).get (balanceSlot k)).toNat ≤
      (Bytes.toB256 (out.take 32)).toNat := by
    have hne := ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)
    exact B256.le_iff_toNat_le_toNat.mp (not_lt.mp hne)
  clear hw
  xjd 0x4d1a
  xs 0x4d1b (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x4d1c (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x4d1d (.reg .sub) ri_sub
  xs 0x4d1e (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x4d1f (.reg .pop) ri_pop
  xs 0x4d20 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x4d21 (.reg .pop) ri_pop
  xs 0x4d23 (.push [0x00] (by decide)) ri_push
  xmo 0x4d24 (.reg .mstore) (ri_mstore_imgAt (o := 0) rfl)
  xs 0x4d26 (.push [0x20] (by decide)) ri_push
  xs 0x4d28 (.push [0x00] (by decide)) ri_push
  obtain ⟨hrun, hL1⟩ := xa_halt (l := .return_) (atL hcode (by kernel_rfl)) h
  simp only [Linst.Run, Linst.run] at hrun
  rw [Devm.popToNat_eq_ok (devm := _) rfl] at hrun
  rcases Except.bind_eq_ok hrun with ⟨⟨idx, dA⟩, hpop1, hrun⟩
  obtain ⟨rfl, rfl⟩ := Except.ok.inj hpop1
  dsimp only at hrun
  rw [Devm.popToNat_eq_ok (devm := _) rfl] at hrun
  rcases Except.bind_eq_ok hrun with ⟨⟨sz, dB⟩, hpop2, hrun⟩
  obtain ⟨rfl, rfl⟩ := Except.ok.inj hpop2
  rcases Except.bind_eq_ok hrun with ⟨dC, hchg, hrun⟩
  dsimp only at hrun
  simp only [chargeGas_def] at hchg
  split at hchg
  · cases hchg
  · rename_i gas hsafe
    injection hchg with hdv
    subst hdv
    injection hrun with hpost
    have harg0 : Sevm.argWord sevm 0 = Sevm.dataWord sevm (Bytes.toB256 [4]) := by
      unfold Sevm.argWord
      rw [show (32 * (0 : B256) + 4 : B256) = Bytes.toB256 [4] by decide]
    have hout_post : post.output =
        ((Bytes.toB256 (out.take 32)) -
          (b.getStor sevm.currentTarget).get (balanceSlot k)).toBytes := by
      rw [← hpost, Devm.withOutput_output]
      show (M.read 0 32).1 = _
      rw [Mem.Reads.read hR 0 32]
      exact adminBal_read_wordB _ _ _ (by simp only [B256.length_toBytes])
    have hlogs_post : post.logs = b.logs ++ c.post.logs := by
      rw [← hpost, Devm.withOutput_logs, Devm.memRead_logs]
      show (afterSload sevm d1 (balanceSlot k)).logs = b.logs ++ c.post.logs
      rw [afterSload_logs, hlogs1, afterSload_logs, hclogs, List.append_nil]
    have hstor_post : ∀ x, (post.getStor sevm.currentTarget).get x =
        (b.getStor sevm.currentTarget).get x := by
      intro x
      rw [← hpost]
      show ((afterSload sevm d1 (balanceSlot k)).getStor _).get x = _
      rw [afterSload_getStor, hstor1, afterSload_getStor]
    rw [hL1] at hL
    refine ⟨hval, k, c, out, hL, ?_, htgt, hdata, hstat, hout, hlen32, hclogs, hstor_post,
      hlogs_post, hout_post, hle⟩
    rw [harg0]
    exact hk_def.symm

/-! ## The frame theorem -/

/-- **The `admin_balances` frame**: from the frame's start, past the dispatcher, the body ran:
no value; one static child (coin `k`'s `balanceOf(self)`, at least 32 bytes back); storage
kept; logs the child's; the difference returned. -/
theorem xa_adminBalances {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAdminBalances)
    (hcoin : ∀ i, i < 3 → ¬ sevm.benvStat.rules.isPrecomp
      (((b.getStor sevm.currentTarget).get (coinsBase + Nat.toB256 i)).toAdr))
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    sevm.value = 0 ∧
    ∃ (k : Fin 3) (c : Exec.Frame) (out : Bytes),
      L = [c] ∧
      (Sevm.argWord sevm 0).toNat = k.val ∧
      c.sevm.currentTarget = ((b.getStor sevm.currentTarget).get (coinSlot k)).toAdr ∧
      c.sevm.data = balanceOfData sevm.currentTarget ∧
      c.sevm.isStatic = true ∧
      c.post.output = out ∧ 32 ≤ out.length ∧
      c.post.logs = [] ∧
      (∀ x, (post.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x) ∧
      post.logs = b.logs ++ c.post.logs ∧
      post.output = ((Bytes.toB256 (out.take 32)) -
        (b.getStor sevm.currentTarget).get (balanceSlot k)).toBytes ∧
      ((b.getStor sevm.currentTarget).get (balanceSlot k)).toNat ≤
        (Bytes.toB256 (out.take 32)).toNat := by
  obtain ⟨G1, h⟩ := adminBal_disp_to_3040 hcode hlen hcd hsel h
  obtain ⟨G2, h⟩ := adminBal_disp_to_test hcode hsel h
  obtain ⟨G3, h⟩ := adminBal_disp_to_body hcode hsel h
  exact adminBal_body hcode hfork hcoin h

/-- The environment an `admin_balances` frame observed: coin `k`'s one `balanceOf(self)`
answer `w` (as the pre-call read; there is no second call, so no post-call read), nothing
else. (`balEnv`'s `balPost = some` would demand two ordered replies for one child, which no
single-`STATICCALL` frame can give; the transition reads `balPre` only.) -/
def adminBal_env (sevm : Sevm) (k : Fin 3) (w : Nat) : Env :=
  ⟨sevm.benvStat.time.toNat, sevm.caller.toB256.toNat, sevm.value.toNat,
    fun j => if j = k then ⟨some w, none, false, false⟩ else ⟨none, none, false, false⟩,
    none, false, false⟩

/-- The model's `admin_balances(i)` under the frame's one answer. -/
theorem adminBal_step {sevm : Sevm} {s : State} (hv : sevm.value = 0) (k : Fin 3)
    (hk : arg sevm 0 = k.val) (w : Nat) (hle : s.balances.get k ≤ w) :
    step s (adminBal_env sevm k w) (.adminBalances (arg sevm 0)) =
      some (viewOut s (w - s.balances.get k)) := by
  have hv' : (adminBal_env sevm k w).value = 0 := by
    show sevm.value.toNat = 0
    rw [hv]; rfl
  have hidx : idx (arg sevm 0) = some k := by
    rw [hk, idx, dite_eq_left k.isLt]
  have hif : (if sevm.value.toNat = 0 then some (viewOut s (w - s.balances.get k))
      else none) = some (viewOut s (w - s.balances.get k)) := by
    rw [show sevm.value.toNat = 0 from hv']; rfl
  simp only [step, body, hif, ite_true, hidx, adminBalances, adminBal_env, ite_true,
    StableSwapNewton.chkSub, hle, bind, Option.bind]

/-- **Safety of `admin_balances`.** A successful frame of the pool's runtime on the
`admin_balances` selector, entered at a `Checkpoint` with empty stack and memory, under the
frame premises (no coin is a precompile), computed the model's step on the decoded call in
the environment `adminBal_env` it observed, with the raw effect Spec states. -/
theorem adminBalances_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAdminBalances)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
      (((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨hval, k, c, out, hL, harg, htgt, hdata, hstat, hout, hlen32, hclogs, hstorF, hlogsF,
    houtF, hleW⟩ :=
    xa_adminBalances hcode hfork hlen hcd hsel (fun i hi => hcoin ⟨i, hi⟩) hx
  have hdec : decodeCall sevm = .adminBalances (arg sevm 0) :=
    decodeCall_at (k := 19) rfl hsel hlen
  have harg0 : arg sevm 0 = k.val := harg
  have hidx : idx (arg sevm 0) = some k := by
    rw [harg0, idx, dite_eq_left k.isLt]
  have hbal : s.balances.get k = ((pre.getStor sevm.currentTarget).get (balanceSlot k)).toNat :=
    (hck.abs.balances k).symm
  have hleM : s.balances.get k ≤ answerWord out := by
    rw [hbal]
    exact hleW
  have hstep := adminBal_step hval k harg0 (answerWord out) hleM
  have hchildren : children ⟨0, sevm, pre, .ok post, exc⟩ = [c] := hL
  refine ⟨adminBal_env sevm k (answerWord out),
    viewOut s (answerWord out - s.balances.get k), ?step, ?raw⟩
  case step =>
    rw [hdec]
    exact hstep
  case raw =>
    have hreply : ReplyAt ⟨0, sevm, pre, .ok post, exc⟩ 0
        ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr
        (balanceOfData sevm.currentTarget) (answerWord out) := by
      refine ⟨c, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hchildren]; rfl
      · exact htgt
      · exact hdata
      · rw [hout]; exact hlen32
      · rw [hout]
    refine ⟨?env, ?stor, ?logs, ?output, ?calls⟩
    case env =>
      refine ⟨rfl, rfl, rfl, fun j => ?_, fun T h => (by cases h), fun h => (by cases h),
        fun h => (by cases h)⟩
      by_cases hj : j = k
      · subst j
        have hc : (adminBal_env sevm k (answerWord out)).coin k =
            ⟨some (answerWord out), none, false, false⟩ :=
          ite_eq_left rfl
        rw [hc]
        refine ⟨fun w' h => ?_, fun w' h => (by cases h), fun h => (by cases h),
          fun h => (by cases h)⟩
        have hw' : answerWord out = w' := Option.some_inj.mp h
        subst hw'
        exact Or.inr ⟨0, hreply⟩
      · have hc : (adminBal_env sevm k (answerWord out)).coin j =
            ⟨none, none, false, false⟩ := by
          show (if j = k then (⟨some (answerWord out), none, false, false⟩ : CoinObs)
            else ⟨none, none, false, false⟩) = _
          rw [ite_eq_right hj]
        rw [hc]
        exact ⟨fun w' h => (by cases h), fun w' h => (by cases h), fun h => (by cases h),
          fun h => (by cases h)⟩
    case stor =>
      show StorEffect (decodeCall sevm) (pre.getStor sevm.currentTarget)
        (post.getStor sevm.currentTarget)
        (viewOut s (answerWord out - s.balances.get k)).state
      rw [hdec]
      refine ⟨fun x _ => hstorF x, fun f hf => ?_⟩
      rw [show footprint (.adminBalances (arg sevm 0)) = [] from rfl] at hf
      cases hf
    case logs =>
      rw [hlogsF, hchildren]
      simp only [viewOut, List.flatMap_cons, List.flatMap_nil, List.map_nil, List.append_nil]
    case output =>
      have hsub : (Bytes.toB256 (out.take 32) -
          (pre.getStor sevm.currentTarget).get (balanceSlot k)).toNat =
          answerWord out - s.balances.get k := by
        rw [B256.toNat_sub_eq_of_le _ _
          (B256.le_iff_toNat_le_toNat.mpr (by simpa only [hbal, answerWord] using hleM)),
          hbal, answerWord]
      have hword : (Bytes.toB256 (out.take 32) -
          (pre.getStor sevm.currentTarget).get (balanceSlot k)) =
          Nat.toB256 (answerWord out - s.balances.get k) := by
        apply B256.toNat_inj
        rw [hsub, B256.toNat_toB256_of_lt (by
          have h256 : answerWord out < 2 ^ 256 := B256.toNat_lt _
          omega)]
      rw [houtF]
      simp only [retOut, word]
      exact congrArg B256.toBytes hword
    case calls =>
      intro hs
      have hcallsL : CallsOf ⟨0, sevm, pre, .ok post, exc⟩ = [] := by
        rw [CallsOf, hchildren]
        simp only [List.filterMap_cons, List.filterMap_nil, hstat, ↓reduceIte]
      have hcallsR : modelCalls ⟨0, sevm, pre, .ok post, exc⟩
          (viewOut s (answerWord out - s.balances.get k)).calls = [] := by
        simp only [modelCalls, viewOut, List.map_nil, List.filter_nil]
      rw [hcallsL, hcallsR]

end Blanc.Lift.Curve3Pool
