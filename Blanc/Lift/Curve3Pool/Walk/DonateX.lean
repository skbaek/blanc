import Blanc.Lift.Curve3Pool.Walk.Dispatch
import Blanc.Lift.Curve3Pool.Walk.Donate
import Blanc.Lift.Curve3Pool.Walk.AdminBalancesX
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityLoop
import Blanc.Lift.Curve3Pool.Spec

/-!
# `donate_admin_fees`, on the actual derivation

From the frame's entry with the `donate_admin_fees` selector (`0x524c3901`) the dispatcher
walks past every earlier arm to the arm's test (`0x4f52`) and falls into its body (`0x4f60`):
the non-payable guard, the owner guard, the counter init at `0x140`, then three iterations.
Each iteration loads `coins[i]` at `keccak(0) + i`, does one `balanceOf(self)` `STATICCALL`
with the output window `0x1e0`, asserts the flag and `RETURNDATASIZE > 31`, and stores the
answer word at `balances[i] = keccak(1) + i`; the tail bumps the counter and loops back
until it reaches `3`, exiting to `STOP`.

`xa_donate` is the frame theorem: a successful frame found no value, spawned exactly three
direct children (coin `k`'s `balanceOf(self)`, static, at least 32 bytes back), wrote the
three answers into `balances[0..2]`, left everything else as the children left it, and
halted with empty output. `donate_raw` is the `<entry>_raw` safety: the model's step on the
decoded call with the `RawEffect` Spec states.

Reuse: `adminBal_disp_taken` (the shared `0x4c85 → 0x4d2c` hop) from `Walk.AdminBalancesX`;
`donEnv`, `donate_step`, `fn3` from the lifted-program walk `Walk.Donate`; the `xs`/`xji`/
`xjd`/`xdead` walk macros and `xa_staticcall_img`, `WordAt`/`Region` from `FrameWalkKit`
via `Walk.Kit` (`Walk.Dispatch`); `keccak_zero`/`keccak_one` via `Walk.RemoveLiquidityLoop`;
`EnvOf`/`ReplyAt`/`answerWord` from `Observe.lean`; `RawEffect`/`StorEffect` from `Spec`.
The `0 → 0x3040` and `0x3040 → 0x4c85` dispatcher walks are re-walked with the donate `hsw`
(they differ from `admin_balances` only there); hoisting them to `Dispatch.lean` needs an
edit to that file, not owned here.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-! ## Dispatcher to the `donate_admin_fees` arm -/

/-- **Dispatcher prefix for `donate_admin_fees`**: from the frame's start to `0x3040` (past
the `remove_liquidity` test, taken). -/
theorem donX_disp_to_3040 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selDonateAdminFees)
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
      0x524c3901 := by
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

/-- **Dispatcher continuation for `donate_admin_fees`**: from `0x3040` to the
`admin_balances` test (`0x4c85`), taking every arm in between. -/
theorem donX_disp_to_test {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selDonateAdminFees)
    (h : XAt sevm post 0x3040 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4c85 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  have hsw : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD (Bytes.toB256 [0]).toNat 32 0) =
      0x524c3901 := by
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

/-- From the `admin_balances` test to the `withdraw_admin_fees` test (`0x4d2c`), via the
shared taken hop. -/
theorem donX_to_withdraw {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selDonateAdminFees)
    (h : XAt sevm post 0x4c85 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4d2c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  have hne : Sevm.selector sevm ≠ selAdminBalances := by
    rw [hsel]; decide
  exact adminBal_disp_taken hcode hne h

/-- **The dispatcher skips `withdraw_admin_fees`**: the taken branch reaches the
`donate_admin_fees` test (`0x4f52`). -/
theorem donX_withdraw_fall {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selDonateAdminFees)
    (h : XAt sevm post 0x4d2c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4f52 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  have hsw : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD (Bytes.toB256 [0]).toNat 32 0) =
      Sevm.selector sevm := by
    rw [show (Bytes.toB256 [0]).toNat = 0 from rfl, vyImg_selector]; rfl
  xs 0x4d31 (.push [0x30, 0xc5, 0x40, 0x85] (by decide)) ri_push
  xs 0x4d33 (.push [0x00] (by decide)) ri_push
  xs 0x4d34 (.reg .mload) ri_mload_vy0
  xs 0x4d35 (.reg .eq) ri_eq
  xs 0x4d36 (.reg .iszero) ri_iszero
  xs 0x4d39 (.push [0x4f, 0x51] (by decide)) ri_push
  xji 0x4d3a 0x4f51 hw
  · have heq := isNe_fall hw
    rw [hsw, hsel] at heq
    exact absurd heq (by decide)
  · xjd 0x4f52
    exact ⟨_, h⟩

/-- **The dispatcher hands `donate_admin_fees` its body** (past the arm's own test at
`0x4f52`, falling into `0x4f60`). -/
theorem donX_disp_to_body {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selDonateAdminFees)
    (h : XAt sevm post 0x4f52 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4f60 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  have hsw : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD (Bytes.toB256 [0]).toNat 32 0) =
      0x524c3901 := by
    rw [show (Bytes.toB256 [0]).toNat = 0 from rfl, vyImg_selector]; exact hsel
  xs 0x4f57 (.push [0x52, 0x4c, 0x39, 0x01] (by decide)) ri_push
  xs 0x4f59 (.push [0x00] (by decide)) ri_push
  xs 0x4f5a (.reg .mload) ri_mload_vy0
  xs 0x4f5b (.reg .eq) ri_eq
  xs 0x4f5c (.reg .iszero) ri_iszero
  xs 0x4f5f (.push [0x50, 0x0a] (by decide)) ri_push
  xji 0x4f60 0x500a hw
  · exact ⟨_, h⟩
  · exact absurd (by rw [hsw]; decide) (isNe_jump hw)

/-! ## Guards and counter init -/

/-- **Guards of `donate_admin_fees`**: no value, the caller is the owner, the counter at
`0x140` set to `0` with `[3, 0x140]` on the stack, entering the loop at `0x4f84`. -/
theorem donX_guards {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h : XAt sevm post 0x4f60 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    sevm.value = 0 ∧ sevm.caller.toB256 = (b.getStor sevm.currentTarget).get ownerSlot ∧
    ∃ G' M' img', Mem.Wf M' ∧ Mem.Reads M' img' ∧
      Region img' 0x140 (Nat.toB256 0).toBytes ∧
      XAt sevm post 0x4f84
        (St (afterSload sevm b ownerSlot) [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]]
          M' G') L := by
  have hR : Mem.Reads (vyMem Mem.empty (Sevm.dataWord sevm 0))
      (vyImg [] (Sevm.dataWord sevm 0)) :=
    vyMem_reads Mem.wf_empty Mem.reads_empty _
  have hW : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  xs 0x4f61 (.reg .callvalue) ri_callvalue
  xs 0x4f62 (.reg .iszero) ri_iszero
  xs 0x4f65 (.push [0x4f, 0x6a] (by decide)) ri_push
  xji 0x4f66 0x4f6a hw
  · xdead
  have hval : sevm.value = 0 := eqCheck_ne_zero_eq hw
  clear hw
  xjd 0x4f6b
  xs 0x4f6d (.push [0x04] (by decide)) ri_push
  xw 0x4f6e (.reg .sload) ri_sload
  rw [show Bytes.toB256 [4] = ownerSlot from by decide] at h
  xs 0x4f6f (.reg .caller) ri_caller
  xs 0x4f70 (.reg .eq) ri_eq
  xs 0x4f73 (.push [0x4f, 0x78] (by decide)) ri_push
  xji 0x4f74 0x4f78 hw
  · xdead
  have hown : sevm.caller.toB256 = (b.getStor sevm.currentTarget).get ownerSlot := by
    have e := eqCheck_ne_zero_eq hw
    rw [getStorVal_eq] at e
    exact e
  clear hw
  xjd 0x4f79
  xs 0x4f7c (.push [0x01, 0x40] (by decide)) ri_push
  xs 0x4f7e (.push [0x00] (by decide)) ri_push
  xs 0x4f80 (.push [0x03] (by decide)) ri_push
  xs 0x4f81 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x4f82 (.reg (.dup 3)) (ri_dup (by rfl))
  xmo 0x4f83 (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  have hctrR : Region (Bytes.writeAt (vyImg [] (Sevm.dataWord sevm 0)) 320
      (Bytes.toB256 [0]).toBytes) 0x140 (Nat.toB256 0).toBytes :=
    Region.write_self _ _ _
  xs 0x4f84 (.reg .add) ri_add
  have h30 : Bytes.toB256 [0x03] + Bytes.toB256 [0x00] = Bytes.toB256 [0x03] := by decide
  rw [h30] at h
  exact ⟨hval, hown, _, _, _, hW, hR, hctrR, h⟩

/-! ## The `balanceOf` calldata in the image -/

/-- The `balanceOf(self)` calldata the staging writes leave at `0x17c` (the zero word at
`0xc0` and the counter word at `0x140` are disjoint from the window). -/
theorem donX_input (img : Bytes) (self : Adr) :
    ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x160
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x180 self.toB256.toBytes) 0xc0
      (Bytes.toB256 [0]).toBytes).sliceD 0x17c 0x24 0) = balanceOfData self := by
  show ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x160
    (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x180 self.toB256.toBytes) 0xc0
    (Bytes.toB256 [0]).toBytes).sliceD 0x17c 0x24 0) = balanceOfSel ++ self.toB256.toBytes
  have hsel : Region (Bytes.writeAt img 0x160 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes)
      0x17c balanceOfSel := by
    have := Region.write_self img 0x160 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes
    rw [adminBal_sel_bytes] at this
    exact this.right
  have hsel2 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x160
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x180 self.toB256.toBytes) 0xc0
      (Bytes.toB256 [0]).toBytes) 0x17c balanceOfSel :=
    Region.write_other
      (Region.write_other hsel (by simp only [balanceOfSel, B256.length_toBytes,
        List.length_cons, List.length_nil]; omega)) (Or.inr (by decide))
  refine Region.slice (Region.append' (o' := 0x180) ?_ ?_ (by rfl))
    (by simp only [balanceOfSel, List.length_append, B256.length_toBytes, List.length_cons,
      List.length_nil])
  · exact hsel2
  · exact Region.write_other (Region.write_self _ _ _) (Or.inr (by decide))

/-- The answer word the `STATICCALL` wrote at `0x1e0` reads back. -/
theorem donX_read_out (img : Bytes) (out : Bytes) (hlen : (out.take 32).length = 32) :
    Bytes.toB256 ((Bytes.writeAt img 0x1e0 (out.take 32)).sliceD 0x1e0 32 0) =
      Bytes.toB256 (out.take 32) :=
  Region.read (Region.write_self img 0x1e0 (out.take 32)) hlen

/-- `SSTORE` keeps logs. -/
theorem donX_sstore_logs (sevm : Sevm) (b : Devm) (k v : B256) :
    (afterSstore sevm b k v).logs = b.logs := by
  unfold afterSstore
  split <;> rfl

/-- `SSTORE` keeps output. -/
theorem donX_sstore_output (sevm : Sevm) (b : Devm) (k v : B256) :
    (afterSstore sevm b k v).output = b.output := by
  unfold afterSstore
  split <;> rfl

/-! ## The loop tail -/

/-- **The `donate_admin_fees` loop tail** (`0x4ff6`): the counter becomes `k + 1`; either
loop back to `0x4f84` (still below `3`) or fall out to `0x5009` (reached `3`). -/
theorem donX_tail {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {M : Mem}
    {img : Bytes} {G : Nat}
    (hcode : sevm.code = code)
    (k : Nat) (hk3 : k < 3)
    (hctrR : Region img 0x140 (Nat.toB256 k).toBytes)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x4ff6
      (St d [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M G) L) :
    (k + 1 < 3 ∧ ∃ G' M' img',
      Region img' 0x140 (Nat.toB256 (k + 1)).toBytes ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧
      XAt sevm post 0x4f84
        (St d [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M' G') L)
    ∨ (k + 1 = 3 ∧ ∃ M' G', XAt sevm post 0x5009 (St d [] M' G') L) := by
  have hplus : Bytes.toB256 [0x01] + Nat.toB256 k = Nat.toB256 (k + 1) := by
    apply B256.toNat_inj
    have hnof : B256.Nof (Bytes.toB256 [0x01]) (Nat.toB256 k) := by
      unfold B256.Nof
      rw [show (Bytes.toB256 [0x01]).toNat = 1 by decide,
        B256.toNat_toB256_of_lt (by omega : k < 2 ^ 256)]
      omega
    rw [B256.toNat_add_eq_of_nof _ _ hnof,
      show (Bytes.toB256 [0x01]).toNat = 1 by decide,
      B256.toNat_toB256_of_lt (by omega : k < 2 ^ 256),
      B256.toNat_toB256_of_lt (by omega : k + 1 < 2 ^ 256)]
    omega
  xjd 0x4ff7
  xs 0x4ff8 (.reg (.dup 1)) (ri_dup (by rfl))
  xmo 0x4ff9 (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  rw [Region.read hctrR (B256.length_toBytes _), B256.toB256_toBytes] at h
  xs 0x4ffb (.push [0x01] (by decide)) ri_push
  xs 0x4ffc (.reg .add) ri_add
  rw [hplus] at h
  xs 0x4ffd (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x4ffe (.reg (.dup 3)) (ri_dup (by rfl))
  xmo 0x4fff (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  have hctrR' : Region (Bytes.writeAt img 0x140 (Nat.toB256 (k + 1)).toBytes) 0x140
      (Nat.toB256 (k + 1)).toBytes :=
    Region.write_self _ _ _
  xs 0x5000 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x5001 (.reg .eq) ri_eq
  xs 0x5002 (.reg .iszero) ri_iszero
  xs 0x5005 (.push [0x4f, 0x84] (by decide)) ri_push
  have h32 : (Bytes.toB256 [0x03]).toNat = 3 := by decide
  have hkp1 : (Nat.toB256 (k + 1)).toNat = k + 1 :=
    B256.toNat_toB256_of_lt (by omega : k + 1 < 2 ^ 256)
  by_cases hdone : k + 1 = 3
  · xji 0x5006 0x4f84 hw
    · xjd 0x5007
      xs 0x5008 (.reg .pop) ri_pop
      xs 0x5009 (.reg .pop) ri_pop
      exact Or.inr ⟨hdone, _, _, h⟩
    · have hne := isNe_jump hw
      have h3 : (Bytes.toB256 [0x03]).toNat ≠ (Nat.toB256 (k + 1)).toNat :=
        fun e => hne (B256.toNat_inj _ _ e)
      rw [h32, hkp1] at h3
      omega
  · have hback : k + 1 < 3 := by omega
    xji 0x5006 0x4f84 hw
    · have heq := isNe_fall hw
      have h3 : (Bytes.toB256 [0x03]).toNat = (Nat.toB256 (k + 1)).toNat :=
        congrArg B256.toNat heq
      rw [h32, hkp1] at h3
      omega
    · exact Or.inl ⟨hback, _, _, _, hctrR', hR, hW, h⟩

/-! ## One loop iteration -/

/-- **One `donate_admin_fees` iteration** (`0x4f84 → 0x4ff6`): with the counter at `k`, one
`balanceOf` `STATICCALL`, the answer stored at `balances[k]`. -/
theorem donX_iter {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {M : Mem}
    {img : Bytes} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (k : Fin 3)
    (hctrR : Region img 0x140 (Nat.toB256 ↑k).toBytes)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hcoinK : ¬ sevm.benvStat.rules.isPrecomp
      (((d.getStor sevm.currentTarget).get (coinSlot k)).toAdr))
    (h : XAt sevm post 0x4f84
      (St d [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M G) L) :
    ∃ (c : Exec.Frame) (out : Bytes) (L' : List Exec.Frame) (d' : Devm) (M' : Mem)
      (img' : Bytes) (G' : Nat),
      L = c :: L' ∧
      c.sevm.currentTarget = ((d.getStor sevm.currentTarget).get (coinSlot k)).toAdr ∧
      c.sevm.data = balanceOfData sevm.currentTarget ∧
      c.sevm.isStatic = true ∧
      c.post.output = out ∧ 32 ≤ out.length ∧
      c.post.logs = [] ∧
      (d'.getStor sevm.currentTarget).get (balanceSlot k) =
        Bytes.toB256 (out.take 32) ∧
      (∀ x, x ≠ balanceSlot k → (d'.getStor sevm.currentTarget).get x =
        (d.getStor sevm.currentTarget).get x) ∧
      d'.logs = d.logs ∧
      d'.output = d.output ∧
      Region img' 0x140 (Nat.toB256 ↑k).toBytes ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧
      XAt sevm post 0x4ff6
        (St d' [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M' G') L' := by
  xjd 0x4f85
  xs 0x4f87 (.push [0x20] (by decide)) ri_push
  xs 0x4f8a (.push [0x01, 0xe0] (by decide)) ri_push
  xs 0x4f8c (.push [0x24] (by decide)) ri_push
  xs 0x4f91 (.push [0x70, 0xa0, 0x82, 0x31] (by decide)) ri_push
  xs 0x4f94 (.push [0x01, 0x60] (by decide)) ri_push
  xmo 0x4f95 (.reg .mstore) (ri_mstore_imgAt (o := 0x160) rfl)
  have hctrR_A : Region (Bytes.writeAt img 0x160
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR (Or.inl (by simp only [B256.length_toBytes]; omega))
  xs 0x4f96 (.reg .address) ri_address
  xs 0x4f99 (.push [0x01, 0x80] (by decide)) ri_push
  xmo 0x4f9a (.reg .mstore) (ri_mstore_imgAt (o := 0x180) rfl)
  have hctrR_B : Region (Bytes.writeAt (Bytes.writeAt img 0x160
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x180
      sevm.currentTarget.toB256.toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_A (Or.inl (by simp only [B256.length_toBytes]; omega))
  xs 0x4f9d (.push [0x01, 0x7c] (by decide)) ri_push
  xs 0x4fa0 (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x4fa1 (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  rw [Region.read hctrR_B (B256.length_toBytes _), B256.toB256_toBytes] at h
  xs 0x4fa3 (.push [0x03] (by decide)) ri_push
  xs 0x4fa4 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x4fa5 (.reg .lt) ri_lt
  xs 0x4fa8 (.push [0x4f, 0xad] (by decide)) ri_push
  have hltK : Nat.toB256 ↑k < Bytes.toB256 [0x03] := by
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega),
      show (Bytes.toB256 [0x03]).toNat = 3 by decide]
    exact k.isLt
  xji 0x4fa9 0x4fad hw
  · exact absurd hw (ltCheck_ne_zero_of_lt hltK)
  clear hw
  xjd 0x4fae
  xs 0x4fb0 (.push [0x00] (by decide)) ri_push
  xs 0x4fb2 (.push [0xc0] (by decide)) ri_push
  xmo 0x4fb3 (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  have hctrR_C : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x160
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x180
      sevm.currentTarget.toB256.toBytes) 0xc0
      (Bytes.toB256 [0]).toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_B (Or.inr (by decide))
  xs 0x4fb5 (.push [0x20] (by decide)) ri_push
  xs 0x4fb7 (.push [0xc0] (by decide)) ri_push
  xmo 0x4fb8 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_zero] at h
  xs 0x4fb9 (.reg .add) ri_add
  have hslot : coinsBase + Nat.toB256 ↑k = coinSlot k := rfl
  rw [hslot] at h
  xw 0x4fba (.reg .sload) ri_sload
  rw [getStorVal_eq] at h
  xs 0x4fbb (.reg .gas) ri_gas_remaining
  replace h := xa_staticcall_img (pc' := 0x4fbc) (i := 0x17c) (n := 0x24) (o := 0x1e0)
    (z := 0x20) hfork (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW h
  clear hR hW
  obtain ⟨d1, flag, out, M', L1, h, hR, hW, hrd, hob, hstor1, hlogs1, hk⟩ := h
  have hctrR_D : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img
      0x160 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x180
      sevm.currentTarget.toB256.toBytes) 0xc0 (Bytes.toB256 [0]).toBytes) 0x1e0
      (out.take 32)) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_C (Or.inl (by simp only [B256.length_toBytes]; omega))
  xs 0x4fbf (.push [0x4f, 0xc4] (by decide)) ri_push
  xji 0x4fc0 0x4fc4 hw
  · xdead
  rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, -, houtKeep, -, -, htgt, hdata, hstat, hout, hclogs, -, -⟩
  · exact absurd hpre hcoinK
  clear hk hw
  rw [donX_input] at hdata
  xjd 0x4fc5
  xs 0x4fc7 (.push [0x1f] (by decide)) ri_push
  xs 0x4fc8 (.reg .returndatasize) ri_returndatasize
  xs 0x4fc9 (.reg .gt) ri_gt
  xs 0x4fcc (.push [0x4f, 0xd1] (by decide)) ri_push
  xji 0x4fcd 0x4fd1 hw
  · xdead
  have hlen32 : 32 ≤ out.length := by
    have hgt := gtCheck_ne_zero hw
    rw [B256.lt_iff_toNat_lt_toNat, hrd, B256.toNat_toB256_of_lt hob,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide] at hgt
    omega
  clear hw
  xjd 0x4fd2
  xs 0x4fd4 (.push [0x00] (by decide)) ri_push
  xs 0x4fd5 (.reg .pop) ri_pop
  xs 0x4fd8 (.push [0x01, 0xe0] (by decide)) ri_push
  xmo 0x4fd9 (.reg .mload) (ri_mload_imgAt (o := 0x1e0) rfl)
  have hlen : (out.take 32).length = 32 := by rw [List.length_take]; omega
  rw [donX_read_out _ _ hlen] at h
  clear hlen
  xs 0x4fdc (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x4fdd (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  rw [Region.read hctrR_D (B256.length_toBytes _), B256.toB256_toBytes] at h
  xs 0x4fdf (.push [0x03] (by decide)) ri_push
  xs 0x4fe0 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x4fe1 (.reg .lt) ri_lt
  xs 0x4fe4 (.push [0x4f, 0xe9] (by decide)) ri_push
  xji 0x4fe5 0x4fe9 hw
  · exact absurd hw (ltCheck_ne_zero_of_lt hltK)
  clear hw
  xjd 0x4fea
  xs 0x4fec (.push [0x01] (by decide)) ri_push
  xs 0x4fee (.push [0xc0] (by decide)) ri_push
  xmo 0x4fef (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  have hctrR_E : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt img 0x160 (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x180
      sevm.currentTarget.toB256.toBytes) 0xc0 (Bytes.toB256 [0]).toBytes) 0x1e0
      (out.take 32)) 0xc0 (Bytes.toB256 [1]).toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_D (Or.inr (by decide))
  xs 0x4ff1 (.push [0x20] (by decide)) ri_push
  xs 0x4ff3 (.push [0xc0] (by decide)) ri_push
  xmo 0x4ff4 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0x4ff5 (.reg .add) ri_add
  have hslotB : balancesBase + Nat.toB256 ↑k = balanceSlot k := rfl
  rw [hslotB] at h
  xw 0x4ff6 (.reg .sstore) ri_sstore
  refine ⟨c, out, L1, _, _, _, _, hL, htgt, hdata, hstat, hout, hlen32, hclogs,
    ?_, ?_, ?_, ?_, hctrR_E, hR, hW, h⟩
  · show (afterSstore sevm d1 (balanceSlot k) (Bytes.toB256 (out.take 32))).getStorVal
      sevm.currentTarget (balanceSlot k) = _
    rw [getStorVal_afterSstore_self, Stor.get_set_self]
  · intro x hx
    show (afterSstore sevm d1 (balanceSlot k) (Bytes.toB256 (out.take 32))).getStorVal
      sevm.currentTarget x = (d.getStor sevm.currentTarget).get x
    rw [getStorVal_afterSstore_ne (Ne.symm hx), getStorVal_eq, hstor1, afterSload_getStor]
  · rw [donX_sstore_logs, hlogs1, afterSload_logs]
  · rw [donX_sstore_output, houtKeep, afterSload_output]
/-! ## The frame theorem -/

/-- **The `donate_admin_fees` frame**: from the frame's start, past the dispatcher, the
guards and three loop iterations ran: no value; three static children (coin `k`'s
`balanceOf(self)`, at least 32 bytes back); the answers stored at `balances[0..2]`;
everything else kept; logs and output kept; halted at `STOP`. -/
theorem xa_donate {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selDonateAdminFees)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
      (((b.getStor sevm.currentTarget).get (coinSlot k)).toAdr))
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    sevm.value = 0 ∧ sevm.caller.toB256 = (b.getStor sevm.currentTarget).get ownerSlot ∧
    ∃ (c0 c1 c2 : Exec.Frame) (out0 out1 out2 : Bytes),
      L = [c0, c1, c2] ∧
      c0.sevm.currentTarget = ((b.getStor sevm.currentTarget).get (coinSlot 0)).toAdr ∧
      c0.sevm.data = balanceOfData sevm.currentTarget ∧
      c0.sevm.isStatic = true ∧
      c0.post.output = out0 ∧ 32 ≤ out0.length ∧
      c0.post.logs = [] ∧
      c1.sevm.currentTarget = ((b.getStor sevm.currentTarget).get (coinSlot 1)).toAdr ∧
      c1.sevm.data = balanceOfData sevm.currentTarget ∧
      c1.sevm.isStatic = true ∧
      c1.post.output = out1 ∧ 32 ≤ out1.length ∧
      c1.post.logs = [] ∧
      c2.sevm.currentTarget = ((b.getStor sevm.currentTarget).get (coinSlot 2)).toAdr ∧
      c2.sevm.data = balanceOfData sevm.currentTarget ∧
      c2.sevm.isStatic = true ∧
      c2.post.output = out2 ∧ 32 ≤ out2.length ∧
      c2.post.logs = [] ∧
      (post.getStor sevm.currentTarget).get (balanceSlot 0) =
        Bytes.toB256 (out0.take 32) ∧
      (post.getStor sevm.currentTarget).get (balanceSlot 1) =
        Bytes.toB256 (out1.take 32) ∧
      (post.getStor sevm.currentTarget).get (balanceSlot 2) =
        Bytes.toB256 (out2.take 32) ∧
      (∀ x, x ≠ balanceSlot 0 → x ≠ balanceSlot 1 → x ≠ balanceSlot 2 →
        (post.getStor sevm.currentTarget).get x = (b.getStor sevm.currentTarget).get x) ∧
      post.logs = b.logs ∧
      post.output = b.output := by
  obtain ⟨G1, h⟩ := donX_disp_to_3040 hcode hlen hcd hsel h
  obtain ⟨G2, h⟩ := donX_disp_to_test hcode hsel h
  obtain ⟨G3, h⟩ := donX_to_withdraw hcode hsel h
  obtain ⟨G4, h⟩ := donX_withdraw_fall hcode hsel h
  obtain ⟨G5, h⟩ := donX_disp_to_body hcode hsel h
  obtain ⟨hval, hown, G6, M6, img6, hW6, hR6, hctrR6, h⟩ := donX_guards hcode hfork h
  have hcoinK0 : ¬ sevm.benvStat.rules.isPrecomp
      (((afterSload sevm b ownerSlot).getStor sevm.currentTarget).get (coinSlot 0)).toAdr := by
    rw [afterSload_getStor]
    exact hcoin 0
  obtain ⟨c0, out0, L1, d1, M1, img1, G7, hL0, htgt0, hdata0, hstat0, hout0, hlen0,
    hclogs0, hbal0, hkept0, hlogs0, houtD0, hctrR1, hR1, hW1, h⟩ :=
    donX_iter hcode hfork 0 hctrR6 hR6 hW6 hcoinK0 h
  rcases donX_tail hcode 0 (by omega) hctrR1 hR1 hW1 h with backArm | exitArm
  · obtain ⟨-, G8, M8, img8, hctrR8, hR8, hW8, h⟩ := backArm
    have hcoinK1 : ¬ sevm.benvStat.rules.isPrecomp
        (((d1.getStor sevm.currentTarget).get (coinSlot 1)).toAdr) := by
      have e : (d1.getStor sevm.currentTarget).get (coinSlot 1) =
          (b.getStor sevm.currentTarget).get (coinSlot 1) := by
        rw [hkept0 _ (by decide), afterSload_getStor]
      rw [e]
      exact hcoin 1
    obtain ⟨c1, out1, L2, d2, M2, img2, G9, hL1, htgt1, hdata1, hstat1, hout1, hlen1,
      hclogs1, hbal1, hkept1, hlogs1, houtD1, hctrR9, hR9, hW9, h⟩ :=
      donX_iter hcode hfork 1 hctrR8 hR8 hW8 hcoinK1 h
    rcases donX_tail hcode 1 (by omega) hctrR9 hR9 hW9 h with backArm | exitArm
    · obtain ⟨-, G10, M10, img10, hctrR10, hR10, hW10, h⟩ := backArm
      have hcoinK2 : ¬ sevm.benvStat.rules.isPrecomp
          (((d2.getStor sevm.currentTarget).get (coinSlot 2)).toAdr) := by
        have e : (d2.getStor sevm.currentTarget).get (coinSlot 2) =
            (b.getStor sevm.currentTarget).get (coinSlot 2) := by
          rw [hkept1 _ (by decide), hkept0 _ (by decide), afterSload_getStor]
        rw [e]
        exact hcoin 2
      obtain ⟨c2, out2, L3, d3, M3, img3, G11, hL2, htgt2, hdata2, hstat2, hout2,
        hlen2, hclogs2, hbal2, hkept2, hlogs2, houtD2, hctrR11, hR11, hW11, h⟩ :=
        donX_iter hcode hfork 2 hctrR10 hR10 hW10 hcoinK2 h
      rcases donX_tail hcode 2 (by omega) hctrR11 hR11 hW11 h with backArm | exitArm
      · obtain ⟨hback2, _, _, _, _, _, _, _⟩ := backArm
        omega
      · obtain ⟨-, M4, G12, h⟩ := exitArm
        obtain ⟨hrun, hLfin⟩ := xa_halt (l := .stop) (atL hcode (by kernel_rfl)) h
        simp only [Linst.Run, Linst.run] at hrun
        injection hrun with hpost
        have hL : L = [c0, c1, c2] := by rw [hL0, hL1, hL2, hLfin]
        have htgt0' : c0.sevm.currentTarget =
            ((b.getStor sevm.currentTarget).get (coinSlot 0)).toAdr := by
          rw [afterSload_getStor] at htgt0
          exact htgt0
        have e1 : (d1.getStor sevm.currentTarget).get (coinSlot 1) =
            (b.getStor sevm.currentTarget).get (coinSlot 1) := by
          rw [hkept0 _ (by decide), afterSload_getStor]
        have e2 : (d2.getStor sevm.currentTarget).get (coinSlot 2) =
            (b.getStor sevm.currentTarget).get (coinSlot 2) := by
          rw [hkept1 _ (by decide), hkept0 _ (by decide), afterSload_getStor]
        have htgt1' : c1.sevm.currentTarget =
            ((b.getStor sevm.currentTarget).get (coinSlot 1)).toAdr := by
          rw [e1] at htgt1
          exact htgt1
        have htgt2' : c2.sevm.currentTarget =
            ((b.getStor sevm.currentTarget).get (coinSlot 2)).toAdr := by
          rw [e2] at htgt2
          exact htgt2
        have hbal0' : (post.getStor sevm.currentTarget).get (balanceSlot 0) =
            Bytes.toB256 (out0.take 32) := by
          rw [← hpost]
          show (d3.getStor sevm.currentTarget).get (balanceSlot 0) = _
          rw [hkept2 _ (by decide), hkept1 _ (by decide)]
          exact hbal0
        have hbal1' : (post.getStor sevm.currentTarget).get (balanceSlot 1) =
            Bytes.toB256 (out1.take 32) := by
          rw [← hpost]
          show (d3.getStor sevm.currentTarget).get (balanceSlot 1) = _
          rw [hkept2 _ (by decide)]
          exact hbal1
        have hbal2' : (post.getStor sevm.currentTarget).get (balanceSlot 2) =
            Bytes.toB256 (out2.take 32) := by
          rw [← hpost]
          show (d3.getStor sevm.currentTarget).get (balanceSlot 2) = _
          exact hbal2
        have hkept' : ∀ x, x ≠ balanceSlot 0 → x ≠ balanceSlot 1 → x ≠ balanceSlot 2 →
            (post.getStor sevm.currentTarget).get x =
              (b.getStor sevm.currentTarget).get x := by
          intro x h0 h1 h2
          rw [← hpost]
          show (d3.getStor sevm.currentTarget).get x = _
          rw [hkept2 _ h2, hkept1 _ h1, hkept0 _ h0, afterSload_getStor]
        have hlogs' : post.logs = b.logs := by
          rw [← hpost]
          show d3.logs = _
          rw [hlogs2, hlogs1, hlogs0, afterSload_logs]
        have hout' : post.output = b.output := by
          rw [← hpost]
          show d3.output = _
          rw [houtD2, houtD1, houtD0, afterSload_output]
        exact ⟨hval, hown, c0, c1, c2, out0, out1, out2, hL, htgt0', hdata0, hstat0,
          hout0, hlen0, hclogs0, htgt1', hdata1, hstat1, hout1, hlen1, hclogs1,
          htgt2', hdata2, hstat2, hout2, hlen2, hclogs2, hbal0', hbal1', hbal2',
          hkept', hlogs', hout'⟩
    · obtain ⟨hdone1, _, _⟩ := exitArm
      omega
  · obtain ⟨hdone0, _, _⟩ := exitArm
    omega

/-- **Safety of `donate_admin_fees`.** A successful frame of the pool's runtime on the
`donate_admin_fees` selector, entered at a `Checkpoint` with empty stack and memory, under
the frame premises (no coin is a precompile), computed the model's step on the decoded call
in the environment `donEnv` it observed, with the raw effect Spec states. -/
theorem donate_raw {sevm : Sevm} {pre post : Devm} {s : State}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selDonateAdminFees)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty) (hgas : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hcoin : ∀ k : Fin 3, ¬ sevm.benvStat.rules.isPrecomp
      (((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)) :
    ∃ e o, step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o := by
  have hx : XAt sevm post 0 (St pre [] Mem.empty pre.gasLeft) (Exec.childFrames exc) :=
    XAt.of_eq (St.self hstack hmem) (XAt.of_exec exc hgas)
  obtain ⟨hval, hown, c0, c1, c2, out0, out1, out2, hL, htgt0, hdata0, hstat0, hout0,
    hlen0, hclogs0, htgt1, hdata1, hstat1, hout1, hlen1, hclogs1, htgt2, hdata2,
    hstat2, hout2, hlen2, hclogs2, hbal0, hbal1, hbal2, hkept, hlogsF, houtF⟩ :=
    xa_donate hcode hfork hlen hcd hsel hcoin hx
  have hdec : decodeCall sevm = .donateAdminFees :=
    decodeCall_at (k := 21) rfl hsel hlen
  have hown' : (quietEnv sevm).caller = s.owner := by
    show sevm.caller.toB256.toNat = s.owner
    rw [hown]
    exact hck.abs.owner
  have hstep := donate_step (fn3 (answerWord out0) (answerWord out1) (answerWord out2))
    hval hown'
  have hchildren : children ⟨0, sevm, pre, .ok post, exc⟩ = [c0, c1, c2] := hL
  refine ⟨donEnv sevm (fn3 (answerWord out0) (answerWord out1) (answerWord out2)),
    ⟨{ s with balances := ⟨answerWord out0, answerWord out1, answerWord out2⟩ },
      none, [], []⟩, ?step, ?raw⟩
  case step =>
    rw [hdec]
    exact hstep
  case raw =>
    have hreply0 : ReplyAt ⟨0, sevm, pre, .ok post, exc⟩ 0
        ((pre.getStor sevm.currentTarget).get (coinSlot 0)).toAdr
        (balanceOfData sevm.currentTarget) (answerWord out0) := by
      refine ⟨c0, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hchildren]; rfl
      · exact htgt0
      · exact hdata0
      · rw [hout0]; exact hlen0
      · rw [hout0]
    have hreply1 : ReplyAt ⟨0, sevm, pre, .ok post, exc⟩ 1
        ((pre.getStor sevm.currentTarget).get (coinSlot 1)).toAdr
        (balanceOfData sevm.currentTarget) (answerWord out1) := by
      refine ⟨c1, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hchildren]; rfl
      · exact htgt1
      · exact hdata1
      · rw [hout1]; exact hlen1
      · rw [hout1]
    have hreply2 : ReplyAt ⟨0, sevm, pre, .ok post, exc⟩ 2
        ((pre.getStor sevm.currentTarget).get (coinSlot 2)).toAdr
        (balanceOfData sevm.currentTarget) (answerWord out2) := by
      refine ⟨c2, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hchildren]; rfl
      · exact htgt2
      · exact hdata2
      · rw [hout2]; exact hlen2
      · rw [hout2]
    refine ⟨?env, ?stor, ?logs, ?output, ?calls⟩
    case env =>
      refine ⟨rfl, rfl, rfl, fun k => ?_, fun T h => (by cases h), fun h => (by cases h),
        fun h => (by cases h)⟩
      by_cases h0 : k.val = 0
      · have hk0 : k = 0 := Fin.ext h0
        subst hk0
        have hc : (donEnv sevm (fn3 (answerWord out0) (answerWord out1)
            (answerWord out2))).coin 0 =
            ⟨some (answerWord out0), none, false, false⟩ := rfl
        rw [hc]
        refine ⟨fun w' h => ?_, fun w' h => (by cases h), fun h => (by cases h),
          fun h => (by cases h)⟩
        have hw' : answerWord out0 = w' := Option.some_inj.mp h
        subst hw'
        exact Or.inr ⟨0, hreply0⟩
      · by_cases h1 : k.val = 1
        · have hk1 : k = 1 := Fin.ext h1
          subst hk1
          have hc : (donEnv sevm (fn3 (answerWord out0) (answerWord out1)
              (answerWord out2))).coin 1 =
              ⟨some (answerWord out1), none, false, false⟩ := rfl
          rw [hc]
          refine ⟨fun w' h => ?_, fun w' h => (by cases h), fun h => (by cases h),
            fun h => (by cases h)⟩
          have hw' : answerWord out1 = w' := Option.some_inj.mp h
          subst hw'
          exact Or.inr ⟨1, hreply1⟩
        · have hk2 : k = 2 := Fin.ext (by omega)
          subst hk2
          have hc : (donEnv sevm (fn3 (answerWord out0) (answerWord out1)
              (answerWord out2))).coin 2 =
              ⟨some (answerWord out2), none, false, false⟩ := rfl
          rw [hc]
          refine ⟨fun w' h => ?_, fun w' h => (by cases h), fun h => (by cases h),
            fun h => (by cases h)⟩
          have hw' : answerWord out2 = w' := Option.some_inj.mp h
          subst hw'
          exact Or.inr ⟨2, hreply2⟩
    case stor =>
      show StorEffect (decodeCall sevm) (pre.getStor sevm.currentTarget)
        (post.getStor sevm.currentTarget)
        { s with balances := ⟨answerWord out0, answerWord out1, answerWord out2⟩ }
      rw [hdec]
      refine ⟨fun x hx => ?_, fun f hf => ?_⟩
      · exact hkept x (Ne.symm (hx (.bal 0) (by decide)))
          (Ne.symm (hx (.bal 1) (by decide))) (Ne.symm (hx (.bal 2) (by decide)))
      · simp only [footprint, balFlds, List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl
        · show ((post.getStor sevm.currentTarget).get (balanceSlot 0)).toNat =
            ({ s with balances :=
              ⟨answerWord out0, answerWord out1, answerWord out2⟩ }).balances.get 0
          rw [hbal0]
          rfl
        · show ((post.getStor sevm.currentTarget).get (balanceSlot 1)).toNat =
            ({ s with balances :=
              ⟨answerWord out0, answerWord out1, answerWord out2⟩ }).balances.get 1
          rw [hbal1]
          rfl
        · show ((post.getStor sevm.currentTarget).get (balanceSlot 2)).toNat =
            ({ s with balances :=
              ⟨answerWord out0, answerWord out1, answerWord out2⟩ }).balances.get 2
          rw [hbal2]
          rfl
    case logs =>
      rw [hlogsF, hchildren]
      simp only [List.flatMap_cons, List.flatMap_nil, hclogs0, hclogs1, hclogs2,
        List.map_nil, List.append_nil]
    case output =>
      rw [houtF]
      simp only [retOut]
    case calls =>
      intro hs
      have hcallsL : CallsOf ⟨0, sevm, pre, .ok post, exc⟩ = [] := by
        rw [CallsOf, hchildren]
        simp only [List.filterMap_cons, List.filterMap_nil, hstat0, hstat1, hstat2,
          ↓reduceIte]
      show CallsOf ⟨0, sevm, pre, .ok post, exc⟩ =
        modelCalls ⟨0, sevm, pre, .ok post, exc⟩ []
      rw [hcallsL]
      simp only [modelCalls, List.map_nil, List.filter_nil]

